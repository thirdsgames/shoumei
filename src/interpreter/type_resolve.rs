//! Resolves an unqualified name into a fully qualified name with type information.

use std::{
    fmt::Display,
    sync::atomic::{AtomicU64, Ordering},
};

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
    /// An unknown type, used for intermediate values of expressions that we don't know the type of.
    /// Create this using `new_unknown`.
    Unknown(u64),
}

static UNKNOWN_TYPE_COUNTER: AtomicU64 = AtomicU64::new(0);

impl Type {
    /// Use this to create a new unknown type.
    pub fn new_unknown() -> Type {
        Type::Unknown(UNKNOWN_TYPE_COUNTER.fetch_add(1, Ordering::Relaxed))
    }

    /// If `parenthesise` is true, functions should be parenthesised.
    pub fn fmt_proper(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        parenthesise: bool,
    ) -> std::fmt::Result {
        match self {
            Type::Named(name) => write!(f, "{}", name.name),
            Type::Function(left, right) => {
                if parenthesise {
                    write!(f, "(")?;
                }
                left.fmt_proper(f, true)?;
                write!(f, " -> ")?;
                right.fmt_proper(f, false)?;
                if parenthesise {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::Unknown(_) => write!(f, "_"),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_proper(f, false)
    }
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
