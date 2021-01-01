//! Performs type deduction and type checking of expressions and patterns.

use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Display,
};

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity};

use super::{
    index::{ModuleIndex, ProjectIndex, TypeDeclarationTypeI},
    index_resolve::{resolve_symbol, resolve_type_constructor, TypeConstructorInvocation},
    syntax_tree::{DefinitionCaseP, ExpressionP, IdentifierP, ModuleP},
    type_deduce::deduce_expr_type,
    type_resolve::{Type, TypeVariableId},
    Location, ModulePath, QualifiedName, Range, Ranged,
};

/// A parsed and fully type checked module.
/// No effort has been made to ensure semantic consistency or correctness,
/// just syntactic and type correctness.
#[derive(Debug)]
pub struct Module {
    pub definitions: HashMap<String, Definition>,
}

impl Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Definitions:")?;
        for (def_name, def) in &self.definitions {
            writeln!(f, "  {} : {}", def_name, def.symbol_type)?;
        }
        Ok(())
    }
}

/// A definition for a symbol, i.e. a function or constant.
#[derive(Debug)]
pub struct Definition {
    /// The `forall` definition at the start of this definition.
    quantifiers: Vec<String>,
    symbol_type: Type,
    cases: Vec<DefinitionCase>,
}

#[derive(Debug)]
pub struct DefinitionCase {
    range: Range,
    arg_patterns: Vec<Pattern>,
    replacement: Expression,
}

/// A pattern made up of type constructors and potential unknowns.
#[derive(Debug, Clone)]
pub enum Pattern {
    /// A name representing the entire pattern, e.g. `a`.
    Named(IdentifierP),
    /// A type constructor, e.g. `False` or `Maybe 3`.
    TypeConstructor {
        type_ctor: TypeConstructorInvocation,
        args: Vec<Pattern>,
    },
    /// A function pattern. This cannot be used directly in code,
    /// this is created only for working with functions that have multiple patterns.
    Function {
        param_types: Vec<Type>,
        args: Vec<Pattern>,
    },
    /// An underscore representing an ignored pattern.
    Unknown(Range),
}

impl Pattern {
    pub fn range(&self) -> Range {
        match self {
            Pattern::Named(identifier) => identifier.range,
            Pattern::TypeConstructor { type_ctor, args } => args
                .iter()
                .fold(type_ctor.range, |acc, i| acc.union(i.range())),
            Pattern::Unknown(range) => *range,
            Pattern::Function { args, .. } => args
                .iter()
                .fold(args[0].range(), |acc, i| acc.union(i.range())),
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Named(identifier) => write!(f, "{}", identifier.name),
            Pattern::TypeConstructor { type_ctor, args } => {
                if args.is_empty() {
                    return write!(f, "{}", type_ctor.type_ctor);
                }

                write!(f, "({}", type_ctor.type_ctor)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
            Pattern::Function { args, .. } => {
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                Ok(())
            }
            Pattern::Unknown(_) => write!(f, "_"),
        }
    }
}

/// Used to determine whether sets of patterns are exhaustive or not.
#[derive(Debug)]
struct PatternExhaustionCheck {
    /// Unmatched patterns should be treated as if in file name "" at location (0, 0).
    unmatched_patterns: Vec<Pattern>,
}

impl PatternExhaustionCheck {
    /// Adds the given pattern to this pattern check, excluding this pattern from all as yet `unmatched_patterns`.
    /// If anything was modified, return true.
    pub fn add(
        &mut self,
        project_index: &HashMap<ModulePath, ModuleIndex>,
        to_exclude: &Pattern,
    ) -> bool {
        let mut anything_modified = false;
        for pat in std::mem::take(&mut self.unmatched_patterns) {
            let (modified, mut new_internal_patterns) =
                PatternExhaustionCheck::exclude_pattern(project_index, pat, to_exclude);
            if modified {
                anything_modified = true;
            }
            self.unmatched_patterns.append(&mut new_internal_patterns);
        }
        anything_modified
    }

    /// This function returns all patterns that match `pat` but do not match `to_exclude`; and returns true if some refinement to the pattern happened.
    /// In the simplest case, when the two patterns are orthogonal, this returns `(false, vec![pat])`.
    /// If `to_exclude` matches `pat` completely, then this returns `(true, Vec::new())`.
    /// If `to_exclude` matches some subset of `pat`, then `true` and the complement of this subset is returned.
    fn exclude_pattern(
        project_index: &HashMap<ModulePath, ModuleIndex>,
        pat: Pattern,
        to_exclude: &Pattern,
    ) -> (bool, Vec<Pattern>) {
        match pat {
            Pattern::Named(_) => (
                true,
                PatternExhaustionCheck::complement(project_index, to_exclude),
            ),
            pat @ Pattern::TypeConstructor { .. } => {
                // If we have a type constructor e.g. `Type a b`, and we want to exclude `Type c d`,
                // the resultant patterns are intersection(`Type a b`, complement(`Type c d`)).
                let mut anything_changed = false;
                let mut results = Vec::new();
                for pat_to_exclude in PatternExhaustionCheck::complement(project_index, to_exclude)
                {
                    let (changed, result) = PatternExhaustionCheck::intersection(
                        project_index,
                        pat.clone(),
                        pat_to_exclude,
                    );
                    if changed {
                        anything_changed = true;
                    }
                    if let Some(result) = result {
                        results.push(result);
                    }
                }
                (anything_changed, results)
            }
            pat @ Pattern::Function { .. } => {
                // If we have a function e.g. `add a b`, and we want to exclude `add c d`,
                // the resultant patterns are intersection(`add a b`, complement(`add c d`)).
                let mut anything_changed = false;
                let mut results = Vec::new();
                for pat_to_exclude in PatternExhaustionCheck::complement(project_index, to_exclude)
                {
                    let (changed, result) = PatternExhaustionCheck::intersection(
                        project_index,
                        pat.clone(),
                        pat_to_exclude,
                    );
                    if changed {
                        anything_changed = true;
                    }
                    if let Some(result) = result {
                        results.push(result);
                    }
                }
                // If the results list is empty, then there was a change - namely, there was no complement,
                // and therefore there is no intersection.
                (anything_changed || results.is_empty(), results)
            }
            Pattern::Unknown(_) => (
                true,
                PatternExhaustionCheck::complement(project_index, to_exclude),
            ),
        }
    }

    /// Returns all patterns of the same type that did not match the given pattern.
    fn complement(project_index: &HashMap<ModulePath, ModuleIndex>, pat: &Pattern) -> Vec<Pattern> {
        match pat {
            Pattern::Named(_) => {
                // A named pattern, e.g. `a`, matches anything.
                Vec::new()
            }
            Pattern::TypeConstructor { type_ctor, args } => {
                // A type constructor, e.g. `Just 3` does not match:
                // - `Just a` where `a` is in the complement of `3`
                // - `a` where `a` is any other type constructor for the same type.
                let data_type_decl = &project_index[&type_ctor.data_type.module_path].types
                    [&type_ctor.data_type.name];
                let TypeDeclarationTypeI::Data(datai) = &data_type_decl.decl_type;
                // Loop through all of the type constructors.
                let mut complement = Vec::new();
                for known_type_ctor in &datai.type_ctors {
                    if known_type_ctor.name == type_ctor.type_ctor {
                        // This is the type constructor we want to find the complement of.
                        // The complement of a type constructor e.g. `Foo a b c` is the intersection of all possible combinations of
                        // complements of a, b and c except for `Foo a b c` itself. In this example, it would be
                        // - Foo comp(a) _ _
                        // - Foo a comp(b) _
                        // - Foo a b comp(c)
                        complement.extend(
                            PatternExhaustionCheck::complement_args(project_index, args)
                                .into_iter()
                                .map(|arg_list| Pattern::TypeConstructor {
                                    type_ctor: TypeConstructorInvocation {
                                        data_type: type_ctor.data_type.clone(),
                                        type_ctor: known_type_ctor.name.clone(),
                                        range: Location { line: 0, col: 0 }.into(),
                                    },
                                    args: arg_list,
                                }),
                        );
                    } else {
                        // Instance a generic pattern for this type constructor.
                        complement.push(Pattern::TypeConstructor {
                            type_ctor: TypeConstructorInvocation {
                                data_type: type_ctor.data_type.clone(),
                                type_ctor: known_type_ctor.name.clone(),
                                range: Location { line: 0, col: 0 }.into(),
                            },
                            args: known_type_ctor
                                .arguments
                                .iter()
                                .map(|_| Pattern::Unknown(Location { line: 0, col: 0 }.into()))
                                .collect(),
                        });
                    }
                }
                complement
            }
            Pattern::Function { param_types, args } => {
                // The complement of a function invocation e.g. `foo a b c` is the intersection of all possible combinations of
                // complements of a, b and c except for `foo a b c` itself. In this example, it would be
                // - foo comp(a) _ _
                // - foo a comp(b) _
                // - foo a b comp(c)
                PatternExhaustionCheck::complement_args(project_index, args)
                    .into_iter()
                    .map(|arg_list| Pattern::Function {
                        param_types: param_types.clone(),
                        args: arg_list,
                    })
                    .collect()
            }
            Pattern::Unknown(_) => {
                // An unknown pattern, e.g. `_`, matches anything.
                Vec::new()
            }
        }
    }

    /// See `Pattern::Function` case in `complement`.
    /// This takes every possible case of an argument and its complement, excluding the case without any complements.
    /// Returns a list of all possible argument lists.
    /// The complement of `True True True` returned by this function is `False _ _`, `True False _`, `True True False`.
    fn complement_args(project_index: &ProjectIndex, args: &[Pattern]) -> Vec<Vec<Pattern>> {
        let mut complements = Vec::new();
        for i in 0..args.len() {
            // This argument will become its complement.
            // Prior arguments are cloned, and future arguments are ignored.
            for complement in PatternExhaustionCheck::complement(project_index, &args[i]) {
                let mut new_args = Vec::new();
                for arg in &args[0..i] {
                    new_args.push(arg.clone());
                }
                new_args.push(complement);
                for _ in (i + 1)..args.len() {
                    new_args.push(Pattern::Unknown(Location { line: 0, col: 0 }.into()));
                }
                complements.push(new_args);
            }
        }
        complements
    }

    /// Returns the pattern that matched both patterns, if such a pattern existed.
    /// Returns false if no pattern deduction occured (i.e., if we return pat1).
    fn intersection(
        project_index: &HashMap<ModulePath, ModuleIndex>,
        pat1: Pattern,
        pat2: Pattern,
    ) -> (bool, Option<Pattern>) {
        match pat1 {
            Pattern::Named(_) => {
                // A named pattern matches anything, so return just pat2.
                // If pat2 is `Named` or `Unknown`, no deduction occured.
                (
                    !matches!(pat2, Pattern::Named(_) | Pattern::Unknown(_)),
                    Some(pat2),
                )
            }
            Pattern::TypeConstructor {
                type_ctor: type_ctor1,
                args: args1,
            } => {
                match pat2 {
                    Pattern::TypeConstructor {
                        type_ctor: type_ctor2,
                        args: args2,
                    } => {
                        if type_ctor1.type_ctor == type_ctor2.type_ctor {
                            // If the type constructors are the same, the intersection is just the intersection of their args.
                            let mut anything_modified = false;
                            let mut args = Vec::new();
                            for (arg1, arg2) in args1.into_iter().zip(args2) {
                                let (modified, new_arg) =
                                    PatternExhaustionCheck::intersection(project_index, arg1, arg2);
                                if modified {
                                    anything_modified = true;
                                }
                                match new_arg {
                                    Some(new_arg) => args.push(new_arg),
                                    // If None, no intersection was found between the arguments, so there is no intersection between the main patterns.
                                    None => return (true, None),
                                }
                            }
                            (
                                anything_modified,
                                Some(Pattern::TypeConstructor {
                                    type_ctor: type_ctor1,
                                    args,
                                }),
                            )
                        } else {
                            // If the type constructors are different, the intersection is empty.
                            (true, None)
                        }
                    }
                    Pattern::Named(_) | Pattern::Unknown(_) => (
                        false,
                        Some(Pattern::TypeConstructor {
                            type_ctor: type_ctor1,
                            args: args1,
                        }),
                    ),
                    _ => panic!("was not type constructor {:#?}", pat2),
                }
            }
            Pattern::Function {
                param_types,
                args: args1,
            } => {
                if let Pattern::Function { args: args2, .. } = pat2 {
                    // The intersection is just the intersection of the functions' arguments.
                    let mut anything_modified = false;
                    let mut args = Vec::new();
                    for (arg1, arg2) in args1.into_iter().zip(args2) {
                        let (modified, new_arg) =
                            PatternExhaustionCheck::intersection(project_index, arg1, arg2);
                        if modified {
                            anything_modified = true;
                        }
                        match new_arg {
                            Some(new_arg) => args.push(new_arg),
                            // If None, no intersection was found between the arguments, so there is no intersection between the main patterns.
                            None => return (true, None),
                        }
                    }
                    (
                        anything_modified,
                        Some(Pattern::Function { param_types, args }),
                    )
                } else {
                    panic!("was not function")
                }
            }
            Pattern::Unknown(_) => {
                // An unknown pattern matches anything, so return just pat2.
                // If pat2 is `Named` or `Unknown`, no deduction occured.
                (
                    !matches!(pat2, Pattern::Named(_) | Pattern::Unknown(_)),
                    Some(pat2),
                )
            }
        }
    }
}

pub fn check(
    module_path: &ModulePath,
    project_index: &HashMap<ModulePath, ModuleIndex>,
    module: ModuleP,
) -> DiagnosticResult<Module> {
    let type_checker = TypeChecker {
        module_path,
        project_index,
        messages: Vec::new(),
    };
    type_checker.compute(module)
}

struct TypeChecker<'a> {
    module_path: &'a ModulePath,
    project_index: &'a HashMap<ModulePath, ModuleIndex>,

    messages: Vec<ErrorMessage>,
}

/// A variable bound by the definition of a function.
#[derive(Debug, Clone)]
pub struct BoundVariable {
    pub range: Range,
    pub var_type: Type,
}

/// A variable bound by some abstraction e.g. a lambda or a let inside it.
#[derive(Debug, Clone)]
pub struct AbstractionVariable {
    pub range: Range,
    pub var_type: TypeVariableId,
}

#[derive(Debug)]
pub struct ExpressionT {
    pub type_variable: TypeVariable,
    pub contents: ExpressionContents<Self>,
}

impl Ranged for ExpressionT {
    fn range(&self) -> Range {
        self.contents.range()
    }
}

/// Closely tied to the `Type` struct, this is used while type checking to allow
/// unknown types, represented by `TypeVariableId`s.
#[derive(Debug, Clone)]
pub enum TypeVariable {
    /// An explicitly named type possibly with type parameters, e.g. `Bool` or `Either a b`.
    Named {
        name: QualifiedName,
        parameters: Vec<TypeVariable>,
    },
    Function(Box<TypeVariable>, Box<TypeVariable>),
    /// A known type variable, e.g. `a`.
    Variable(String),
    /// A completely unknown type - we don't even have a type variable letter to describe it such as `a`.
    /// These are assigned random IDs, and when printed are converted into Greek letters using the
    /// `TypeVariablePrinter`.
    Unknown(TypeVariableId),
}

/// A utility for printing type variables to screen.
/// Works like the Display trait, but works better for printing type variable names.
pub struct TypeVariablePrinter {
    /// Maps type variable IDs to the names we use to render them.
    type_variable_names: HashMap<TypeVariableId, String>,
    /// When we see a new type variable that we've not named yet, what name should we give it?
    /// This monotonically increasing counter is used to work out what the name should be.
    type_variable_name: u32,
    /// A substitution mapping type variables to the substituted type variable.
    /// This map is tried before making a new name for a type variable.
    substitution: HashMap<TypeVariableId, TypeVariable>,
}

impl TypeVariablePrinter {
    pub fn new(substitution: HashMap<TypeVariableId, TypeVariable>) -> Self {
        Self {
            type_variable_names: HashMap::new(),
            type_variable_name: 0,
            substitution,
        }
    }

    pub fn print(&mut self, ty: TypeVariable) -> String {
        match ty {
            TypeVariable::Named { name, parameters } => {
                let mut result = name.name;
                for param in parameters {
                    result += " (";
                    result += &self.print(param);
                    result += ")";
                }
                result
            }
            TypeVariable::Function(l, r) => {
                // TODO sort out precedence
                format!("{} -> ({})", self.print(*l), self.print(*r))
            }
            TypeVariable::Unknown(ty) => self.get_name(&ty),
            TypeVariable::Variable(name) => name,
        }
    }

    fn get_name(&mut self, ty: &TypeVariableId) -> String {
        if let Some(result) = self.substitution.get(ty) {
            let cloned = result.clone();
            // If the substitution doesn't do anything, don't stick in an infinite loop.
            // We don't need to worry about cycles - the substitution is defined to be idempotent.
            if let TypeVariable::Unknown(other_id) = cloned {
                if other_id == *ty {
                    // The substitution exists, but maps the value to itself.
                } else {
                    return self.print(cloned);
                }
            } else {
                return self.print(cloned);
            }
        }
        if let Some(result) = self.type_variable_names.get(&ty) {
            return result.clone();
        }
        let name = self.new_name();
        self.type_variable_names.insert(*ty, name.clone());
        name
    }

    fn new_name(&mut self) -> String {
        let id = self.type_variable_name;
        self.type_variable_name += 1;

        // Assign a new lowercase Greek letter to this type.
        // There are 24 letters to choose from.
        // If we overflow this, just add a suffix to the name.
        let name = std::char::from_u32('α' as u32 + (id % 24)).unwrap();
        let suffix = id / 24;
        if suffix > 0 {
            format!("<{}{}>", name, suffix)
        } else {
            format!("<{}>", name)
        }
    }
}

#[derive(Debug)]
pub struct Expression {
    pub ty: Type,
    pub contents: ExpressionContents<Self>,
}

impl Ranged for Expression {
    fn range(&self) -> Range {
        self.contents.range()
    }
}

/// Represents the contents of an expression (which may or may not have been already type checked).
#[derive(Debug)]
pub enum ExpressionContents<E> {
    /// An argument to this function e.g. `x`.
    Argument(IdentifierP),
    /// A local variable declared by a `lambda` expression.
    MonotypeVariable(IdentifierP),
    /// A local variable declared by a `let` expression.
    PolytypeVariable(IdentifierP),
    /// A symbol in global scope e.g. `+` or `fold`.
    Symbol {
        /// The name that the symbol refers to.
        name: QualifiedName,
        /// The range where the symbol's name was written in this file.
        range: Range,
    },
    /// Apply the left hand side to the right hand side, e.g. `a b`.
    /// More complicated expressions e.g. `a b c d` can be desugared into `((a b) c) d`.
    Apply(Box<E>, Box<E>),
    /// A lambda abstraction, specifically `lambda params -> expr`.
    Lambda {
        lambda_token: Range,
        params: Vec<IdentifierP>,
        expr: Box<E>,
    },
    /// A let expression, specifically `let identifier = left_expr in right_expr`.
    Let {
        let_token: Range,
        identifier: IdentifierP,
        left_expr: Box<E>,
        right_expr: Box<E>,
    },
}

impl<E> Ranged for ExpressionContents<E>
where
    E: Ranged,
{
    fn range(&self) -> Range {
        match self {
            ExpressionContents::Argument(arg) => arg.range,
            ExpressionContents::MonotypeVariable(var) => var.range,
            ExpressionContents::PolytypeVariable(var) => var.range,
            ExpressionContents::Symbol { range, .. } => *range,
            ExpressionContents::Apply(l, r) => l.range().union(r.range()),
            ExpressionContents::Lambda {
                lambda_token, expr, ..
            } => lambda_token.union(expr.range()),
            ExpressionContents::Let {
                let_token,
                right_expr,
                ..
            } => let_token.union(right_expr.range()),
        }
    }
}

impl<'a> TypeChecker<'a> {
    fn compute(mut self, module: ModuleP) -> DiagnosticResult<Module> {
        let mut definitions = HashMap::<String, Definition>::new();

        for definition in module.definitions {
            let cases = definition.cases;
            let def_ident = definition.identifier;
            let quantifiers = definition.quantifiers;

            // Let's type check the function signature.
            let symbol = &self.project_index[self.module_path].symbols[&def_ident.name];
            let symbol_type = &symbol.symbol_type;

            // We need to check pattern exhaustiveness in the definition's cases.
            // Let's resolve each case's patterns and expressions.
            let cases = cases
                .into_iter()
                .map(|case| self.resolve_case(&def_ident.name, case))
                .collect::<DiagnosticResult<_>>();

            // Now we can check whether the patterns are valid.
            let cases_validated = cases.bind(|cases| {
                cases
                    .into_iter()
                    .map(|(range, args, replacement)| {
                        self.validate_case(&symbol_type, range, args, replacement, def_ident.range)
                    })
                    .collect::<DiagnosticResult<_>>()
            });
            // Check that the patterns we have generated are exhaustive.
            let validated = cases_validated.deny().bind(|cases_validated| {
                self.check_cases_exhaustive(
                    &symbol_type,
                    cases_validated
                        .iter()
                        .map(|(range, pat, _)| (*range, pat))
                        .collect(),
                    &def_ident,
                )
                .map(|_| cases_validated)
            });

            let (definition_parsed, mut inner_messages) = validated.destructure();
            self.messages.append(&mut inner_messages);
            if let Some(cases) = definition_parsed {
                definitions.insert(
                    def_ident.name,
                    Definition {
                        quantifiers: quantifiers.iter().map(|id| id.name.clone()).collect(),
                        symbol_type: symbol_type.clone(),
                        cases: cases
                            .into_iter()
                            .map(|(range, arg_patterns, replacement)| DefinitionCase {
                                range,
                                arg_patterns,
                                replacement,
                            })
                            .collect(),
                    },
                );
            }
        }

        DiagnosticResult::ok_with_many(Module { definitions }, self.messages)
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
        definition_identifier_range: Range,
    ) -> DiagnosticResult<(Range, Vec<Pattern>, Expression)> {
        let (symbol_args, _) = get_args_of_type(symbol_type);
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
        let arg_vars = args
            .iter()
            .zip(symbol_args.into_iter())
            .map(|(pattern, expected_type)| self.match_and_bind(pattern, expected_type))
            .collect::<DiagnosticResult<_>>();
        // Collect the list of maps into a single map, ensuring that we don't have duplicate variable names.
        let arg_vars = arg_vars.bind(|arg_vars| collect_bound_vars(self.module_path, arg_vars));

        // Now, parse the expression, now that we know the input variable types.
        arg_vars
            .bind(|arg_vars| {
                deduce_expr_type(
                    self.module_path,
                    self.project_index,
                    &arg_vars,
                    replacement,
                    result,
                    definition_identifier_range,
                )
            })
            .map(|expr| (range, args, expr))
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
                Type::Named {
                    name: expected_name,
                    parameters: concrete_type_parameters,
                } => {
                    if type_ctor.data_type == expected_name {
                        // Find the data type declaration in the index.
                        let data_type_decl = &self.project_index[&expected_name.module_path].types
                            [&expected_name.name];
                        // Find the original list of named type parameters. We can then create a bijective correspondence
                        // between the list of `concrete_type_parameters` given and the list of `named_type_parameters`,
                        // so we can identify which type parameter has which value.
                        let named_type_parameters = {
                            let TypeDeclarationTypeI::Data(datai) = &data_type_decl.decl_type;
                            &datai.type_params
                        };

                        // Find the list of parameters for the type constructor that we're creating.
                        let expected_parameters = self.project_index[&expected_name.module_path]
                            .get_type_ctor_args(&type_ctor.type_ctor);

                        // Process the arguments to this type constructor.
                        if args.len() != expected_parameters.len() {
                            return DiagnosticResult::fail(ErrorMessage::new(
                                format!(
                                    "expected {} parameters for this type constructor",
                                    expected_parameters.len()
                                ),
                                Severity::Error,
                                Diagnostic::at(self.module_path.clone(), type_ctor.range),
                            ));
                        }

                        // We now know that the amount of arguments supplied is correct for this type constructor.
                        let bound_args = args
                            .iter()
                            .zip(expected_parameters)
                            .map(|(arg, expected)| {
                                // For each argument in the pattern, we need to match that argument against the known type
                                // of this argument. So we need to match the type parameters in this type constructor
                                // against the type parameters above.
                                // This means that when matching a `Maybe Bool`, the type constructor `Just a` becomes `Just Bool`,
                                // because the `a` is replaced with the concrete type `Bool`.
                                let expected = expected.replace_type_variables(
                                    named_type_parameters,
                                    &concrete_type_parameters,
                                );
                                self.match_and_bind(arg, expected)
                            })
                            .collect::<DiagnosticResult<_>>();
                        bound_args
                            .bind(|bound_args| collect_bound_vars(self.module_path, bound_args))
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
                Type::Variable(name) => DiagnosticResult::fail(ErrorMessage::new(
                    format!(
                        "expected a name for a variable of type `{}`, not a type constructor",
                        name
                    ),
                    Severity::Error,
                    Diagnostic::at(self.module_path.clone(), type_ctor.range),
                )),
            },
            Pattern::Unknown(_) => DiagnosticResult::ok(HashMap::new()),
            Pattern::Function { .. } => unimplemented!(),
        }
    }

    fn check_cases_exhaustive(
        &self,
        symbol_type: &Type,
        cases: Vec<(Range, &Vec<Pattern>)>,
        def_ident: &IdentifierP,
    ) -> DiagnosticResult<()> {
        // Check that all cases have the same amount of arguments.
        let arg_count = cases[0].1.len();
        let mismatched_cases = cases
            .iter()
            .filter(|(_, args)| args.len() != arg_count)
            .collect::<Vec<_>>();
        if !mismatched_cases.is_empty() {
            let error_messages = mismatched_cases
                .into_iter()
                .map(|(case_range, _)| {
                    ErrorMessage::new_with(
                        String::from("patterns had different amounts of arguments"),
                        Severity::Error,
                        Diagnostic::at(self.module_path.clone(), *case_range),
                        HelpMessage {
                            message: format!("expected {} to match first pattern", arg_count),
                            help_type: HelpType::Note,
                            diagnostic: Diagnostic::at(self.module_path.clone(), cases[0].0),
                        },
                    )
                })
                .collect::<Vec<_>>();
            return DiagnosticResult::fail_many(error_messages);
        }

        // Now, let's begin gradually refining the patterns for each argument until exhaustion is determined.
        let (symbol_args, _) = get_args_of_type_arity(symbol_type, arg_count);
        let mut args_exhaustion = PatternExhaustionCheck {
            unmatched_patterns: vec![Pattern::Function {
                param_types: symbol_args.clone(),
                args: (0..arg_count)
                    .map(|_| Pattern::Unknown(Location { line: 0, col: 0 }.into()))
                    .collect(),
            }],
        };

        let mut messages = Vec::new();
        for (range, patterns) in &cases {
            let pattern = Pattern::Function {
                param_types: symbol_args.clone(),
                args: (*patterns).clone(),
            };
            let anything_modified = args_exhaustion.add(self.project_index, &pattern);
            if !anything_modified {
                messages.push(ErrorMessage::new(
                    String::from("this pattern will never be matched"),
                    Severity::Warning,
                    Diagnostic::at(self.module_path.clone(), *range),
                ));
            }
        }
        if !args_exhaustion.unmatched_patterns.is_empty() {
            let mut message = String::from(
                "the patterns in this definition are not exhaustive\nunmatched patterns:",
            );
            for pat in args_exhaustion.unmatched_patterns {
                message += &format!("\n    {} {}", def_ident.name, pat);
            }
            messages.push(ErrorMessage::new(
                message,
                Severity::Error,
                Diagnostic::at(self.module_path.clone(), def_ident.range),
            ))
        }

        DiagnosticResult::ok_with_many((), messages)
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
            ExpressionP::Lambda { lambda_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("lambda abstractions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.module_path.clone(), lambda_token),
            )),
            ExpressionP::Let { let_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("let expressions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.module_path.clone(), let_token),
            )),
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
                    Some(type_ctor) => DiagnosticResult::ok(Pattern::TypeConstructor {
                        type_ctor,
                        args: Vec::new(),
                    }),
                    None => {
                        // It was not a type constructor, so it must just be a variable name.
                        DiagnosticResult::ok(Pattern::Named(identifier))
                    }
                }
            }
            ExpressionP::Apply(left, right) => self.resolve_type_pattern(*left).bind(|left| {
                self.resolve_type_pattern(*right).bind(|right| match left {
                    Pattern::TypeConstructor {
                        type_ctor,
                        mut args,
                    } => {
                        args.push(right);
                        DiagnosticResult::ok(Pattern::TypeConstructor { type_ctor, args })
                    }
                    _ => DiagnosticResult::fail(ErrorMessage::new(
                        String::from("expected a type constructor on the left of this application"),
                        Severity::Error,
                        Diagnostic::at(self.module_path.clone(), left.range()),
                    )),
                })
            }),
            ExpressionP::Unknown(range) => DiagnosticResult::ok(Pattern::Unknown(range)),
            ExpressionP::Lambda { lambda_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("lambda abstractions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.module_path.clone(), lambda_token),
            )),
            ExpressionP::Let { let_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("let expressions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.module_path.clone(), let_token),
            )),
        }
    }
}

/// Flattens a list of maps into a single map, adding error messages if variables were multiply defined.
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
        Type::Named { .. } => (Vec::new(), symbol_type.clone()),
        Type::Function(left, right) => {
            let (mut args, out) = get_args_of_type(&right);
            args.insert(0, *left.clone());
            (args, out)
        }
        Type::Variable { .. } => (Vec::new(), symbol_type.clone()),
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
