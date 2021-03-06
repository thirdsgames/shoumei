//! The `runtime` module executes functions from a `.shoumei` program.

use std::collections::HashMap;

use crate::{
    parser::type_check::{Expression, ExpressionContents, Pattern},
    ModuleLoader,
};

pub mod value;
use value::*;

/// The `'ml` lifetime refers to the lifetime of the module loader that we're borrowing information from.
pub struct Runtime<'ml> {
    pub module_loader: &'ml ModuleLoader,

    /// The thunk stack is like the call stack from imperative languages, but
    /// represents the thunk dependency chain. In order to evaluate the thunk at the
    /// bottom of the stack, the second-bottom thunk must be evaluated, and so on until
    /// the top of the stack.
    thunk_stack: Vec<ValueRef<'ml>>,
}

/// We tried to match a pattern to a list of arguments,
/// but something went wrong.
enum MatchError<'ml> {
    /// The pattern was not matched.
    NotMatched,
    /// We must evaluate a thunk before we know if the pattern is matched.
    Evaluate {
        /// Which thunk do we need to evaluate before we know if the pattern is matched?
        /// This ValueRef must point to a thunk.
        thunk: ValueRef<'ml>,
    },
}

/// Profiling information for an evaluation of an expression.
pub struct EvaluationProfile<'ml> {
    /// The actual value that was found.
    pub value: Value<'ml>,
    /// The maximum stack depth that was reached while computing a chain of thunks.
    /// This can be used to aid in optimising tail-recursive functions.
    pub max_stack_depth: usize,
    /// The maximum depth of data nesting in the result expression.
    pub max_result_depth: usize,
    /// Whether a stack overflow was detected. If this is true, the value may not be
    /// completely strictly evaluated.
    pub stack_overflow: bool,
}

impl<'ml> Runtime<'ml> {
    /// Creates a new runtime and evaluates the given value.
    /// The result value is returned, along with profiling information about this evaluation.
    /// The result is evaluated strictly, but intermediate operations may be lazy.
    pub fn evaluate(
        module_loader: &'ml ModuleLoader,
        root_thunk: ValueRef<'ml>,
    ) -> EvaluationProfile<'ml> {
        Runtime::evaluate_inner(module_loader, root_thunk, 0)
    }

    /// The `recursion_depth` is the level of nesting that the result of the computation has.
    /// For example, the value `Just (Just (Just 1))` has a maximum recursion depth of 4.
    /// We can use this to detect and prevent stack overflows, and detect infinitely recursive data.
    fn evaluate_inner(
        module_loader: &'ml ModuleLoader,
        root_thunk: ValueRef<'ml>,
        recursion_depth: usize,
    ) -> EvaluationProfile<'ml> {
        const MAX_RECURSION_DEPTH: usize = 1000;

        let mut runtime = Self {
            module_loader,
            thunk_stack: Vec::new(),
        };
        runtime.thunk_stack.push(root_thunk.clone());

        let mut max_stack_depth = 1;

        // If the root thunk is an `Apply` or a `Let`, we should evaluate it in this main loop.
        // But if it isn't, we can just skip the first iteration of the loop and then
        // it'll return the value.
        let should_evaluate = matches!(&*root_thunk.0.borrow(), Value::Apply(_) | Value::Let(_));

        // Keep evaluating thunks on the stack until the thunk is fully evaluated.
        loop {
            // Evaluate the topmost thunk on the stack.
            if should_evaluate {
                let topmost_thunk = runtime.thunk_stack.last().unwrap().clone();
                let mut topmost_thunk_borrow = topmost_thunk.0.borrow_mut();
                match &mut *topmost_thunk_borrow {
                    Value::Apply(apply) => {
                        if let Some(value) = runtime.evaluate_apply(apply) {
                            // The thunk was evaluated. Let's update its value.
                            let is_data = matches!(value, Value::Data(_) | Value::Function(_));
                            *topmost_thunk_borrow = value;
                            // Now, we can pop this thunk from the list if it's plain old data.
                            if is_data {
                                runtime.thunk_stack.pop();
                            }
                        }
                    }
                    Value::Let(let_expr) => {
                        *topmost_thunk_borrow = runtime.evaluate_let(let_expr);
                    }
                    v => panic!("stack contained an invalid value: {:#?}", v),
                };
            }

            // Update profiling information.
            max_stack_depth = max_stack_depth.max(runtime.thunk_stack.len());

            // Check to see if the root thunk has been evaluated.
            match &*root_thunk.0.borrow() {
                Value::Apply(_) | Value::Let(_) => {
                    // We still have more computation to go.
                    // Continue the loop.
                }
                val => {
                    // We've evaluated the computation!
                    // We can return this as a result.
                    // But wait - if it's a data type, we first need to make sure that its arguments are evaluated.
                    let mut max_result_depth = recursion_depth;

                    if let Value::Data(data) = val {
                        // We should check to make sure that recursive
                        // evaluation of data arguments doesn't stack overflow.
                        if recursion_depth > MAX_RECURSION_DEPTH {
                            return EvaluationProfile {
                                value: val.clone(),
                                max_stack_depth,
                                max_result_depth: recursion_depth,
                                stack_overflow: true,
                            };
                        }

                        // We need to merge the inner evaluation profiles with this one.
                        let mut max_inner_stack_depth = 0;
                        for arg in &data.args {
                            let inner_evaluation_profile = Runtime::evaluate_inner(
                                module_loader,
                                arg.clone(),
                                recursion_depth + 1,
                            );
                            max_inner_stack_depth =
                                max_inner_stack_depth.max(inner_evaluation_profile.max_stack_depth);
                            max_result_depth =
                                max_result_depth.max(inner_evaluation_profile.max_result_depth);
                        }
                        max_stack_depth += max_inner_stack_depth;
                    }

                    return EvaluationProfile {
                        value: val.clone(),
                        max_stack_depth,
                        max_result_depth,
                        stack_overflow: false,
                    };
                }
            }
        }
    }

    /// Tries to evaluate a function application.
    /// If any dependencies are generated, they are pushed onto the stack.
    /// Otherwise, a result is acquired, and it is returned.
    fn evaluate_apply(&mut self, apply: &Apply<'ml>) -> Option<Value<'ml>> {
        match &mut *apply.function.0.borrow_mut() {
            Value::Function(func) => {
                // The left hand side of the application has been evaluated,
                // so we can try to invoke it.

                // We should avoid recursion, since this could lead to stack overflows, which
                // we want to catch gracefully to display to the user.

                // Does the thunk have the right arity? We could be trying to apply a 2-ary function to only one value, for example.
                if apply.args.len() != func.arity() {
                    // We don't have the right amount of arguments to execute the function.
                    panic!("incorrect number of arguments for function arity")
                }

                // In order to execute a function, we need to know which pattern the arguments match.
                for case in &*func.cases {
                    // Do the function arguments match this case?
                    match self.args_match_pattern(&apply.args, &case.arg_patterns) {
                        Ok(bindings) => {
                            return Some(self.evaluate_expression(
                                &bindings,
                                &HashMap::new(),
                                &case.replacement,
                            ));
                        }
                        Err(MatchError::NotMatched) => {}
                        Err(MatchError::Evaluate { thunk }) => {
                            self.thunk_stack.push(thunk);
                            return None;
                        }
                    };
                }
                panic!("no pattern was matched");
            }
            Value::Data(_) => {
                panic!("data cannot be treated as a function");
            }
            Value::Apply(inner_apply) => {
                // The function that we're trying to invoke has not yet been computed.
                // Merge the argument from this function application into
                // the inner function.
                inner_apply.args.extend(apply.args.clone());
                Some(inner_apply.clone().into())
            }
            Value::Lambda(lambda) => {
                // The left hand side of the application has been evaluated as a lambda expression,
                // so we can try to invoke it.

                // Does the thunk have the right arity? We could be trying to apply a 2-ary function to only one value, for example.
                if apply.args.len() != lambda.arity() {
                    // We don't have the right amount of arguments to execute the function.
                    panic!("incorrect number of arguments for function arity")
                }

                // Lambda expressions contain no pattern matching. Let's simply substitute the arguments into the lambda body.
                let mut bound_variables = lambda.function_bound_variables.clone();
                // Bind the new variables.
                bound_variables.extend(
                    lambda
                        .params
                        .iter()
                        .cloned()
                        .zip(apply.args.iter().cloned()),
                );
                Some(self.evaluate_expression(
                    &lambda.function_arguments,
                    &bound_variables,
                    &lambda.expr,
                ))
            }
            Value::Let(let_expr) => {
                // Collapse the let expression into a function or a lambda.
                let function = self.evaluate_let(let_expr).into();
                Some(
                    Apply {
                        function,
                        args: apply.args.clone(),
                    }
                    .into(),
                )
            }
        }
    }

    fn evaluate_let(&self, let_expr: &Let<'ml>) -> Value<'ml> {
        // A let expression involves substituting the `left_expr` into the `right_expr`.
        // We can accomplish this by inserting the `left_expr` into the `bound_variables` of the `right_expr`.
        let left = self.evaluate_expression(
            &let_expr.function_arguments,
            &let_expr.function_bound_variables,
            &let_expr.left_expr,
        );

        // We have evaluated the `left_expr`.
        let mut bound_variables = let_expr.function_bound_variables.clone();
        bound_variables.insert(let_expr.var_name.clone(), left.into());
        self.evaluate_expression(
            &let_expr.function_arguments,
            &bound_variables,
            &let_expr.right_expr,
        )
    }

    /// Check whether the provided arguments match the argument patterns.
    /// If they match, the return value is a map of bindings from variable names to the values that they represent.
    /// If they do not match, or if we don't know yet (i.e. a thunk must be evaluated first), the error is returned.
    fn args_match_pattern(
        &self,
        args: &[ValueRef<'ml>],
        patterns: &[Pattern],
    ) -> Result<HashMap<String, ValueRef<'ml>>, MatchError<'ml>> {
        let mut bindings = HashMap::new();
        for (arg, pattern) in args.iter().zip(patterns) {
            self.arg_matches_pattern(arg, pattern, &mut bindings)?;
        }
        Ok(bindings)
    }

    /// Check if a single argument matches a pattern.
    fn arg_matches_pattern(
        &self,
        arg: &ValueRef<'ml>,
        pattern: &Pattern,
        bindings: &mut HashMap<String, ValueRef<'ml>>,
    ) -> Result<(), MatchError<'ml>> {
        // Does this argument match the pattern?
        // Because of type checking, we know that the type of the argument matches the type of the pattern.
        // So all that's left is to check the contents of the argument.
        match pattern {
            Pattern::Named(name) => {
                // Any argument fits a name pattern.
                bindings.insert(name.name.clone(), arg.clone());
                Ok(())
            }
            Pattern::TypeConstructor {
                type_ctor,
                args: type_ctor_patterns,
            } => {
                match &*arg.0.borrow() {
                    Value::Data(data) => {
                        // Check that the argument was constructed using the correct type constructor.
                        if data.type_ctor == type_ctor.type_ctor {
                            // This was the correct type constructor.
                            // Now we need to check if the arguments to this type constructor match.
                            for (arg, pattern) in data.args.iter().zip(type_ctor_patterns) {
                                self.arg_matches_pattern(arg, pattern, bindings)?;
                            }
                            Ok(())
                        } else {
                            Err(MatchError::NotMatched)
                        }
                    }
                    Value::Apply(_) => {
                        // We don't know if this argument matches the pattern, since its value
                        // has not yet been computed.
                        Err(MatchError::Evaluate { thunk: arg.clone() })
                    }
                    _ => panic!("non-data can't match a type constructor"),
                }
            }
            Pattern::Function { .. } => {
                panic!("should never have a function pattern at runtime")
            }
            Pattern::Unknown(_) => {
                // Any argument fits an unknown pattern.
                // No bindings are necessary.
                Ok(())
            }
        }
    }

    /// A result value for the expression, possibly containing dependencies, is returned.
    ///
    /// `bound_variables` contains all the monotype and polytype variables created in this scope.
    ///
    /// TODO This method is slightly inefficient. We return a cloned `Value` instead of a `ValueRef` so that
    /// we can update the contents of a thunk's `ValueRef`. Perhaps it would be more efficient to add
    /// another level of indirection in order to avoid this clone - or maybe the processor's optimisations
    /// on `memcpy` are good enough that we don't need to worry about this? After all, we're only cloning a
    /// small data structure that may contain some `Rc` instances.
    fn evaluate_expression(
        &self,
        arguments: &HashMap<String, ValueRef<'ml>>,
        bound_variables: &HashMap<String, ValueRef<'ml>>,
        expression: &'ml Expression,
    ) -> Value<'ml> {
        match &expression.contents {
            ExpressionContents::Argument(arg) => arguments[&arg.name].0.borrow().clone(),
            ExpressionContents::MonotypeVariable(var) => {
                bound_variables[&var.name].0.borrow().clone()
            }
            ExpressionContents::PolytypeVariable(var) => {
                bound_variables[&var.name].0.borrow().clone()
            }
            ExpressionContents::Symbol {
                name,
                type_variables,
                ..
            } => {
                // Instance a symbol from global scope.
                let def = self.module_loader.definition(name).unwrap();
                assert!(def.quantifiers.len() == type_variables.len());
                Value::Apply(Function { cases: &def.cases }.apply_zero_args())
            }
            ExpressionContents::Apply(l, r) => {
                let l = self.evaluate_expression(arguments, bound_variables, &l);
                let r = self.evaluate_expression(arguments, bound_variables, &r);

                Value::Apply(Apply {
                    function: l.into(),
                    args: vec![r.into()],
                })
            }
            ExpressionContents::Lambda { params, expr, .. } => {
                // Create this lambda expression.
                Value::Apply(
                    Lambda {
                        function_arguments: arguments.clone(),
                        function_bound_variables: bound_variables.clone(),
                        expr,
                        params: params.iter().map(|id| id.name.clone()).collect(),
                    }
                    .apply_zero_args(),
                )
            }
            ExpressionContents::Let {
                identifier,
                left_expr,
                right_expr,
                ..
            } => {
                // Create this let expression.
                Value::Let(Let {
                    function_arguments: arguments.clone(),
                    function_bound_variables: bound_variables.clone(),
                    left_expr,
                    right_expr,
                    var_name: identifier.name.clone(),
                })
            }
            ExpressionContents::CreateData {
                data_type_name,
                type_ctor,
                args,
            } => {
                let args = args
                    .iter()
                    .map(|expr| {
                        ValueRef::from(self.evaluate_expression(arguments, bound_variables, expr))
                    })
                    .collect::<Vec<_>>();

                Value::Data(Data {
                    data_type_name: data_type_name.clone(),
                    type_ctor: type_ctor.clone(),
                    args,
                })
            }
        }
    }
}
