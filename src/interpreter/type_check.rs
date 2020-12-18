//! Performs type deduction and type checking of expressions and patterns.

use std::collections::{hash_map::Entry, HashMap};

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity};

use super::{ModulePath, QualifiedName, Range, index::{ModuleIndex, TypeDeclarationI, TypeDeclarationTypeI}, index_resolve::{resolve_symbol, resolve_type_constructor, TypeConstructorInvocation}, parser::{DefinitionCaseP, ExpressionP, IdentifierP, ModuleP}, type_resolve::{resolve_typep, Type}, types::{TypeDeclarationC, TypeDeclarationTypeC}};

/// A parsed and fully type checked module.
/// No effort has been made to ensure semantic consistency or correctness,
/// just syntactic and type correctness.
pub struct Module {}

/// A pattern made up of type constructors and potential unknowns.
#[derive(Debug)]
pub enum Pattern {
    /// A name representing the entire pattern, e.g. `a`.
    Named(IdentifierP),
    /// A type constructor, e.g. `False` or `Maybe 3`.
    TypeConstructor {
        type_ctor: TypeConstructorInvocation,
        args: Vec<Pattern>,
    },
    /// An underscore representing an ignored pattern.
    Unknown(Range),
}

impl Pattern {
    pub fn range(&self) -> Range {
        match self {
            Pattern::Named(identifier) => identifier.range,
            Pattern::TypeConstructor{ type_ctor, args } => args.iter().fold(type_ctor.range, |acc, i| acc.union(i.range())),
            Pattern::Unknown(range) => *range,
        }
    }
}

/// Used to determine whether sets of patterns are exhaustive or not.
#[derive(Debug)]
enum PatternExhaustionCheck<'a> {
    /// A type constructor, e.g. `False` or `Maybe 3`.
    TypeConstructors {
        decl: &'a TypeDeclarationI,
        /// If this map is ever filled with all possible type constructors,
        /// all of which have all their arguments covered,
        /// then this can be reduced to `Covered`.
        ctors: HashMap<String, TypeConstructorExhaustionCheck<'a>>,
    },
    /// The pattern is covered and all cases have been handled.
    Covered,
}

impl<'a> PatternExhaustionCheck<'a> {
    /// Adds the given pattern to this pattern check.
    /// This unifies the patterns, e.g. if this is `True` and `pattern` is `False`, this is reduced to `Covered` since
    /// all cases are covered under the combination of patterns.
    /// If anything was modified, return true.
    pub fn add(&mut self, pattern: &Pattern) -> bool {
        match pattern {
            Pattern::Named(_) => {
                *self = PatternExhaustionCheck::Covered;
                true
            }
            Pattern::TypeConstructor { type_ctor, args } => {
                match self {
                    PatternExhaustionCheck::TypeConstructors { decl, ctors } => {
                        // Add the type constructor to this map of type constructors.
                        let type_ctor_exhaustion = ctors.entry(type_ctor.type_ctor.clone()).or_insert(TypeConstructorExhaustionCheck {
                            args: Vec::new(),
                        });
                        let mut anything_modified = false;
                        for (arg_pattern, arg_pattern_exhaustion) in args.iter().zip(type_ctor_exhaustion.args.iter_mut()) {
                            anything_modified |= arg_pattern_exhaustion.add(arg_pattern);
                        }
                        // Check whether all type constructors are covered.
                        if let TypeDeclarationTypeI::Data(datai) = &decl.decl_type {
                            if datai.type_ctors.len() == ctors.len() {
                                // All type constructors are in the list, let's check they're all covered.
                                if ctors.iter().all(|(_, ctor_exhaustion)| ctor_exhaustion.is_covered()) {
                                    *self = PatternExhaustionCheck::Covered;
                                }
                            }
                        } else {
                            panic!("should be a data type");
                        }
                        anything_modified
                    }
                    PatternExhaustionCheck::Covered => false,
                }
            }
            Pattern::Unknown(_) => {
                *self = PatternExhaustionCheck::Covered;
                true
            }
        }
    }
}

#[derive(Debug)]
struct TypeConstructorExhaustionCheck<'a> {
    args: Vec<PatternExhaustionCheck<'a>>,
}

impl TypeConstructorExhaustionCheck<'_> {
    pub fn is_covered(&self) -> bool {
        self.args.iter().all(|arg| matches!(arg, PatternExhaustionCheck::Covered))
    }
}

pub fn check(
    module_path: &ModulePath,
    project_types: &HashMap<ModulePath, HashMap<String, TypeDeclarationC>>,
    project_index: &HashMap<ModulePath, ModuleIndex>,
    module: ModuleP,
) -> DiagnosticResult<Module> {
    let type_checker = TypeChecker {
        module_path,
        project_types,
        project_index,
        messages: Vec::new(),
    };
    type_checker.compute(module)
}

struct TypeChecker<'a> {
    module_path: &'a ModulePath,
    project_types: &'a HashMap<ModulePath, HashMap<String, TypeDeclarationC>>,
    project_index: &'a HashMap<ModulePath, ModuleIndex>,

    messages: Vec<ErrorMessage>,
}

/// A variable bound by the definition of a function.
#[derive(Debug)]
struct BoundVariable {
    pub range: Range,
    pub var_type: Type,
}

#[derive(Debug)]
struct Expression {
    pub ty: Type,
    pub contents: ExpressionContents,
}

#[derive(Debug)]
enum ExpressionContents {
    /// A local variable e.g. `x`.
    Variable(IdentifierP),
    /// A symbol in global scope e.g. `+` or `fold`.
    Symbol(QualifiedName),
    /// Apply the left hand side to the right hand side, e.g. `a b`.
    /// More complicated expressions e.g. `a b c d` can be desugared into `((a b) c) d`.
    Apply(Box<Expression>, Box<Expression>),
}

impl<'a> TypeChecker<'a> {
    fn compute(mut self, module: ModuleP) -> DiagnosticResult<Module> {
        for definition in module.definitions {
            let function_name = definition.identifier.name;
            let symbol_type = definition.symbol_type;
            let cases = definition.cases;

            // Let's type check the function signature.
            let symbol_type = resolve_typep(self.module_path, &symbol_type, self.project_types);
            let validated = symbol_type.bind(|symbol_type| {
                // We need to check pattern exhaustiveness in the definition's cases.
                // Let's resolve each case's patterns and expressions.
                let cases = cases
                    .into_iter()
                    .map(|case| self.resolve_case(&function_name, case))
                    .collect::<DiagnosticResult<_>>();

                // Now we can check whether the patterns are valid.
                let cases_validated = cases.bind(|cases| {
                    cases
                        .into_iter()
                        .map(|(range, args, replacement)| {
                            self.validate_case(&symbol_type, range, args, replacement)
                        })
                        .collect::<DiagnosticResult<_>>()
                });
                println!("Cases: {:#?}", cases_validated);
                // Check that the patterns we have generated are exhaustive.
                cases_validated.bind(|cases_validated| {
                    self.check_cases_exhaustive(
                        &symbol_type,
                        cases_validated.iter().map(|(range, pat, _)| (*range, pat)).collect(),
                    )
                    .map(|_| cases_validated)
                })
            });
            let (_, mut inner_messages) = validated.destructure();
            self.messages.append(&mut inner_messages);
        }

        DiagnosticResult::ok_with_many(Module {}, self.messages)
    }

    fn resolve_case(
        &self,
        function_name: &str,
        case: DefinitionCaseP,
    ) -> DiagnosticResult<(Range, Vec<Pattern>, ExpressionP)> {
        let range = case.pattern.range();
        let pattern = self.resolve_func_pattern(function_name, case.pattern);
        let replacement = case.replacement;
        pattern.map(|pattern| (range, pattern, replacement))
    }

    /// Verify that the given case exactly matches the required type, and also type check the expression given the arguments' types and the expected output type.
    fn validate_case(
        &self,
        symbol_type: &Type,
        range: Range,
        args: Vec<Pattern>,
        replacement: ExpressionP,
    ) -> DiagnosticResult<(Range, Vec<Pattern>, Expression)> {
        let (symbol_args, result) = get_args_of_type(symbol_type);
        // The types in `args` must match the first `args.len()` types in symbol_args.
        if args.len() > symbol_args.len() {
            return DiagnosticResult::fail(ErrorMessage::new(
                String::from("too many arguments given to function"),
                Severity::Error,
                Diagnostic::at(self.module_path.clone(), args[symbol_args.len()].range()),
            ));
        }
        // Let's recalculate symbol_args and result to match the number of arguments we supplied.
        let (symbol_args, result) = get_args_of_type_arity(symbol_type, args.len());

        // Now we can check that the types provided in `args` match the expected `symbol_args`.
        let bound_variables = args
            .iter()
            .zip(symbol_args.into_iter())
            .map(|(pattern, expected_type)| self.match_and_bind(pattern, expected_type))
            .collect::<DiagnosticResult<_>>();
        // Collect the list of maps into a single map, ensuring that we don't have duplicate variable names.
        let bound_variables =
            bound_variables.bind(|bound| collect_bound_vars(self.module_path, bound));

        // Now, parse the expression, now that we know the input variable types.
        bound_variables.bind(|bound_variables| self.parse_expr(&bound_variables, replacement)).map(|expr| (range, args, expr))
    }

    /// Type checks an expression, assigning new type variables to each sub-expression.
    fn parse_expr(&self, bound_variables: &HashMap<String, BoundVariable>, expr: ExpressionP) -> DiagnosticResult<Expression> {
        match expr {
            ExpressionP::Variable(identifier) => match bound_variables.get(&identifier.name) {
                // Let's try to work out what this identifier is referring to.
                // First, check bound variables.
                Some(bound_variable) => DiagnosticResult::ok(Expression {
                    ty: bound_variable.var_type.clone(),
                    contents: ExpressionContents::Variable(identifier),
                }),
                None => {
                    // Now let's look for a symbol in scope.
                    match resolve_symbol(self.module_path, &identifier, self.project_index).destructure().0 {
                        Some((symbol_module_path, symbol)) => DiagnosticResult::ok(Expression {
                            ty: symbol.symbol_type.clone(),
                            contents: ExpressionContents::Symbol(QualifiedName {
                                module_path: symbol_module_path.clone(),
                                name: symbol.name.name.clone(),
                                range: symbol.name.range,
                            }),
                        }),
                        // If None, we couldn't find a symbol in scope.
                        None => DiagnosticResult::fail(ErrorMessage::new(
                            format!("variable `{}` not recognised", identifier.name),
                            Severity::Error,
                            Diagnostic::at(self.module_path.clone(), identifier.range),
                        )),
                    }
                }
            }
            ExpressionP::Apply(left, right) => {
                self.parse_expr(bound_variables, *left).bind(|left| self.parse_expr(bound_variables, *right).map(|right| Expression {
                    ty: Type::new_unknown(),
                    contents: ExpressionContents::Apply(Box::new(left), Box::new(right))
                }))
            },
            ExpressionP::Unknown(range) => DiagnosticResult::fail(ErrorMessage::new(
                String::from("underscore not allowed in expressions"),
                Severity::Error,
                Diagnostic::at(self.module_path.clone(), range),
            )),
        }
    }

    /// Match the pattern to the type. If the pattern is a match for the type, a map is returned which
    /// shows what variable names have what types.
    fn match_and_bind(
        &self,
        pattern: &Pattern,
        expected_type: Type,
    ) -> DiagnosticResult<HashMap<String, BoundVariable>> {
        match pattern {
            Pattern::Named(identifier) => {
                let mut map = HashMap::new();
                map.insert(
                    identifier.name.clone(),
                    BoundVariable {
                        var_type: expected_type,
                        range: identifier.range,
                    },
                );
                DiagnosticResult::ok(map)
            }
            Pattern::TypeConstructor { type_ctor, args } => match expected_type {
                Type::Named(expected_name) => {
                    if type_ctor.data_type == expected_name {
                        let data_decl = &self.project_types[&expected_name.module_path][&expected_name.name];
                        if let TypeDeclarationTypeC::Data(data) = &data_decl.decl_type {
                            // TODO when we have type constructors that take variables, we need to add behaviour here.
                            //collect_bound_vars(self.module_path, args.iter().map(|arg| self.match_and_bind(pattern, expected_type)))
                            DiagnosticResult::ok(HashMap::new())
                        } else {
                            panic!("was not a data constructor");
                        }
                    } else {
                        DiagnosticResult::fail(ErrorMessage::new(
                            format!("expected a type constructor for `{}`", expected_name),
                            Severity::Error,
                            Diagnostic::at(self.module_path.clone(), type_ctor.range),
                        ))
                    }
                }
                Type::Function(_, _) => DiagnosticResult::fail(ErrorMessage::new(
                    String::from("expected a name for a function, not a type constructor"),
                    Severity::Error,
                    Diagnostic::at(self.module_path.clone(), type_ctor.range),
                )),
                Type::Unknown(_) => panic!("expected type must be known")
            },
            Pattern::Unknown(_) => DiagnosticResult::ok(HashMap::new()),
        }
    }

    fn check_cases_exhaustive(
        &self,
        symbol_type: &Type,
        cases: Vec<(Range, &Vec<Pattern>)>,
    ) -> DiagnosticResult<()> {
        // Check that all cases have the same amount of arguments.
        let arg_count = cases[0].1.len();
        let mismatched_cases = cases.iter().filter(|(_, args)| args.len() != arg_count).collect::<Vec<_>>();
        if !mismatched_cases.is_empty() {
            let error_messages = mismatched_cases.into_iter().map(|(case_range, _)| {
                ErrorMessage::new_with(
                    String::from("patterns had different amounts of arguments"),
                    Severity::Error,
                    Diagnostic::at(self.module_path.clone(), *case_range),
                    HelpMessage {
                        message: format!("expected {} to match first pattern", arg_count),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(self.module_path.clone(), cases[0].0),
                    }
                )
            }).collect::<Vec<_>>();
            return DiagnosticResult::fail_many(error_messages);
        }

        // Now, let's begin gradually refining the patterns for each argument until exhaustion is determined.
        let (symbol_args, _) = get_args_of_type_arity(symbol_type, arg_count);
        let mut args_exhaustion = symbol_args.into_iter().map(|arg| match arg {
            Type::Named(qualified_name) => PatternExhaustionCheck::TypeConstructors {
                decl: &self.project_index[&qualified_name.module_path].types[&qualified_name.name],
                ctors: HashMap::new(),
            },
            Type::Function(_, _) => PatternExhaustionCheck::Covered,
            Type::Unknown(_) => PatternExhaustionCheck::Covered,
        }).collect::<Vec<_>>();

        println!("Args: {:#?}", args_exhaustion);
        for (range, patterns) in &cases {
            for (exhaustion, pattern) in args_exhaustion.iter_mut().zip(patterns.iter()) {
                exhaustion.add(pattern);
            }
            println!("Args now: {:#?}", args_exhaustion);
        }

        DiagnosticResult::ok(())
    }

    /// Converts a pattern representing a function invocation into a pattern object.
    /// The returned values are the function's parameters.
    /// This function does not guarantee that the returned pattern is valid for the function.
    fn resolve_func_pattern(
        &self,
        function_name: &str,
        expression: ExpressionP,
    ) -> DiagnosticResult<Vec<Pattern>> {
        match expression {
            ExpressionP::Variable(identifier) => {
                // This identifier should be the function.
                let symbol = resolve_symbol(self.module_path, &identifier, self.project_index);
                symbol.bind(|(symbol_module_path, symbol)| {
                    // Verify that the symbol really is the function.
                    if symbol_module_path != self.module_path || symbol.name.name != function_name {
                        DiagnosticResult::fail(ErrorMessage::new_with(
                            String::from("this did not match the function being defined"),
                            Severity::Error,
                            Diagnostic::at(self.module_path.clone(), identifier.range),
                            HelpMessage {
                                message: format!("replace this with `{}`", function_name),
                                help_type: HelpType::Help,
                                diagnostic: Diagnostic::at(
                                    self.module_path.clone(),
                                    identifier.range,
                                ),
                            },
                        ))
                    } else {
                        DiagnosticResult::ok(Vec::new())
                    }
                })
            }
            ExpressionP::Apply(left, right) => {
                // The left hand side should be a function pattern, and the right hand side should be a type pattern.
                self.resolve_func_pattern(function_name, *left)
                    .bind(|mut left| {
                        self.resolve_type_pattern(*right).map(|right| {
                            left.push(right);
                            left
                        })
                    })
            }
            ExpressionP::Unknown(range) => {
                // This is invalid, the function must be the pattern.
                DiagnosticResult::fail(ErrorMessage::new_with(
                    String::from("this did not match the function being defined"),
                    Severity::Error,
                    Diagnostic::at(self.module_path.clone(), range),
                    HelpMessage {
                        message: format!("replace this with `{}`", function_name),
                        help_type: HelpType::Help,
                        diagnostic: Diagnostic::at(self.module_path.clone(), range),
                    },
                ))
            }
        }
    }

    /// Converts a pattern representing a type constructor into a pattern object.
    fn resolve_type_pattern(&self, expression: ExpressionP) -> DiagnosticResult<Pattern> {
        match expression {
            ExpressionP::Variable(identifier) => {
                // This identifier is either a type constructor or a variable name.
                let type_ctor =
                    resolve_type_constructor(self.module_path, &identifier, self.project_index)
                        .destructure()
                        .0;
                match type_ctor {
                    Some(type_ctor) => DiagnosticResult::ok(Pattern::TypeConstructor { type_ctor, args: Vec::new() }),
                    None => {
                        // It was not a type constructor, so it must just be a variable name.
                        DiagnosticResult::ok(Pattern::Named(identifier))
                    }
                }
            }
            ExpressionP::Apply(left, right) => self.resolve_type_pattern(*left).bind(|left| {
                self.resolve_type_pattern(*right)
                    .bind(|right| {
                        match left {
                            Pattern::TypeConstructor { type_ctor, mut args } => {
                                args.push(right);
                                DiagnosticResult::ok(Pattern::TypeConstructor { type_ctor, args })
                            }
                            _ => DiagnosticResult::fail(ErrorMessage::new(
                                String::from("expected a type constructor on the left of this application"),
                                Severity::Error,
                                Diagnostic::at(self.module_path.clone(), left.range())
                            ))
                        }
                    })
            }),
            ExpressionP::Unknown(range) => DiagnosticResult::ok(Pattern::Unknown(range)),
        }
    }
}

fn collect_bound_vars(
    module_path: &ModulePath,
    bound_variables: Vec<HashMap<String, BoundVariable>>,
) -> DiagnosticResult<HashMap<String, BoundVariable>> {
    let mut messages = Vec::new();
    let mut map = HashMap::<String, BoundVariable>::new();

    for inner in bound_variables {
        for (k, v) in inner {
            match map.entry(k) {
                Entry::Occupied(occupied) => {
                    messages.push(ErrorMessage::new_with(
                        format!("variable `{}` was already defined", occupied.key()),
                        Severity::Error,
                        Diagnostic::at(module_path.clone(), v.range),
                        HelpMessage {
                            message: String::from("previously defined here"),
                            help_type: HelpType::Note,
                            diagnostic: Diagnostic::at(module_path.clone(), occupied.get().range),
                        },
                    ));
                }
                Entry::Vacant(vacant) => {
                    vacant.insert(v);
                }
            }
        }
    }

    DiagnosticResult::ok_with_many(map, messages)
}

/// Treating this symbol as a function, what are its arguments' types and the result type?
/// If this is not a function, then it is treated as a zero-argument function.
fn get_args_of_type(symbol_type: &Type) -> (Vec<Type>, Type) {
    match symbol_type {
        Type::Named(_) => (Vec::new(), symbol_type.clone()),
        Type::Function(left, right) => {
            let (mut args, out) = get_args_of_type(&right);
            args.insert(0, *left.clone());
            (args, out)
        }
        Type::Unknown(_) => panic!("type must be known")
    }
}

/// Treating this symbol as a function, what are its arguments' types and the result type?
/// If this is not a function, then it is treated as a zero-argument function.
///
/// This enforces that the function is treated as a `num_args`-argument function,
/// by currying arguments until the required arity is achieved.
fn get_args_of_type_arity(symbol_type: &Type, num_args: usize) -> (Vec<Type>, Type) {
    let (mut symbol_args, mut result) = get_args_of_type(symbol_type);

    // Now, let's edit the `symbol_args` and `result` type to match the number of arguments we supplied.
    // For example, if we have a function of type `a -> b -> c` and we supplied one argument of type `a`, the result is of type `b -> c`.
    while symbol_args.len() > num_args {
        let last_arg = symbol_args.pop().unwrap();
        result = Type::Function(Box::new(last_arg), Box::new(result));
    }

    (symbol_args, result)
}
