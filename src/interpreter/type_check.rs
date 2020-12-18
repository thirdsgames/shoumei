//! Performs type deduction and type checking of expressions and patterns.

use std::collections::HashMap;

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity};

use super::{
    index::ModuleIndex,
    index_resolve::{resolve_symbol, resolve_type_constructor, TypeConstructorInvocation},
    parser::{DefinitionCaseP, ExpressionP, ModuleP},
    type_resolve::{resolve_type_identifier, resolve_typep},
    types::TypeDeclarationC,
    ModulePath, QualifiedName, Range,
};

/// A parsed and fully type checked module.
/// No effort has been made to ensure semantic consistency or correctness,
/// just syntactic and type correctness.
pub struct Module {}

#[derive(Debug)]
pub enum Pattern {
    TypeConstructor(TypeConstructorInvocation),
    Apply(Box<Pattern>, Box<Pattern>),
    Unknown(Range),
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

impl<'a> TypeChecker<'a> {
    fn compute(mut self, module: ModuleP) -> DiagnosticResult<Module> {
        for definition in module.definitions {
            // We need to check pattern exhaustiveness in the definition's cases.
            // Let's resolve each case's patterns and expressions.
            let function_name = definition.identifier.name;
            let cases = definition
                .cases
                .into_iter()
                .map(|case| self.resolve_case(&function_name, case))
                .collect::<DiagnosticResult<_>>();
            let (value, mut inner_messages) = cases.destructure();
            println!("Value: {:#?}", value);
            self.messages.append(&mut inner_messages);
        }

        DiagnosticResult::ok_with_many(Module {}, self.messages)
    }

    fn resolve_case(
        &self,
        function_name: &str,
        case: DefinitionCaseP,
    ) -> DiagnosticResult<(Vec<Pattern>, ExpressionP)> {
        let pattern = self.resolve_func_pattern(function_name, case.pattern);
        let replacement = case.replacement;
        pattern.map(|pattern| (pattern, replacement))
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
                // This identifier must be a type constructor.
                resolve_type_constructor(self.module_path, &identifier, self.project_index)
                    .map(Pattern::TypeConstructor)
            }
            ExpressionP::Apply(left, right) => self.resolve_type_pattern(*left).bind(|left| {
                self.resolve_type_pattern(*right)
                    .map(|right| Pattern::Apply(Box::new(left), Box::new(right)))
            }),
            ExpressionP::Unknown(range) => DiagnosticResult::ok(Pattern::Unknown(range)),
        }
    }
}
