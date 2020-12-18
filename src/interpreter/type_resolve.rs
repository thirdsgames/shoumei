//! Resolves an unqualified name into a fully qualified name with type information.

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, Severity};

use super::{
    parser::{IdentifierP, TypeP},
    types::ProjectTypesC,
    ModulePath, QualifiedName,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// An explicitly named type without type parameters, e.g. `Bool`.
    Named(QualifiedName),
    /// A function `a -> b`.
    /// Functions with more arguments, e.g. `a -> b -> c` are represented as
    /// curried functions, e.g. `a -> (b -> c)`.
    Function(Box<Type>, Box<Type>),
}

/// Resolves a type into a fully qualified type.
pub fn resolve_typep(
    module_path: &ModulePath,
    typep: &TypeP,
    project_types: &ProjectTypesC,
) -> DiagnosticResult<Type> {
    match typep {
        TypeP::Named(identifier) => {
            resolve_type_identifier(module_path, identifier, project_types).map(Type::Named)
        }
        TypeP::Function(left, right) => {
            resolve_typep(module_path, &left, project_types).bind(|left| {
                resolve_typep(module_path, &right, project_types)
                    .map(|right| Type::Function(Box::new(left), Box::new(right)))
            })
        }
    }
}

pub fn resolve_type_identifier(
    module_path: &ModulePath,
    identifier: &IdentifierP,
    project_types: &ProjectTypesC,
) -> DiagnosticResult<QualifiedName> {
    // We don't have `import`-style statements yet, so let's just only search for types in the current module path.
    let module_types = &project_types[module_path];
    match module_types.get(&identifier.name) {
        Some(type_decl) => DiagnosticResult::ok(QualifiedName {
            module_path: module_path.clone(),
            name: type_decl.name.name.clone(),
            range: type_decl.name.range,
        }),
        None => DiagnosticResult::fail(ErrorMessage::new(
            String::from("could not resolve type"),
            Severity::Error,
            Diagnostic::at(module_path.clone(), identifier.range),
        )),
    }
}
