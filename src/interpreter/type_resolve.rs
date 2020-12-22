//! Resolves an unqualified name into a fully qualified name with type information.

use std::{
    collections::HashSet,
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
    /// An explicitly named type possibly with type parameters, e.g. `Bool` or `Either a b`.
    Named {
        name: QualifiedName,
        parameters: Vec<Type>,
    },
    /// A function `a -> b`.
    /// Functions with more arguments, e.g. `a -> b -> c` are represented as
    /// curried functions, e.g. `a -> (b -> c)`.
    Function(Box<Type>, Box<Type>),
    /// A type variable, like `a`. Type variables may not contain parameters.
    Variable(String),
    /// An unknown type, used for intermediate values of expressions that we don't know the type of.
    /// Create this using `new_unknown`.
    Unknown(u64),
    /// A type quantified over some type variables, e.g. `forall a . a`
    Quantified {
        quantifiers: Vec<String>,
        ty: Box<Type>,
    },
}

static UNKNOWN_TYPE_COUNTER: AtomicU64 = AtomicU64::new(0);

impl Type {
    /// Use this to create a new unknown type.
    pub fn new_unknown() -> Type {
        Type::Unknown(UNKNOWN_TYPE_COUNTER.fetch_add(1, Ordering::Relaxed))
    }

    /// If `parenthesise` is true, the parameter should be parenthesised.
    pub fn fmt_proper(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        parenthesise: bool,
    ) -> std::fmt::Result {
        if parenthesise {
            write!(f, "(")?;
        }
        match self {
            Type::Named { name, parameters } => {
                write!(f, "{}", name.name)?;
                for param in parameters {
                    // Check if we should parenthesise this parameter.
                    let should_parenthesise = match param {
                        Type::Named {
                            parameters: inner_params,
                            ..
                        } => !inner_params.is_empty(),
                        Type::Function(_, _) => true,
                        Type::Variable(_) => false,
                        Type::Unknown(_) => false,
                        Type::Quantified { .. } => true,
                    };
                    write!(f, " ")?;
                    param.fmt_proper(f, should_parenthesise)?;
                }
            }
            Type::Function(left, right) => {
                left.fmt_proper(f, matches!(**left, Type::Function(_, _)))?;
                write!(f, " -> ")?;
                right.fmt_proper(f, false)?;
            }
            Type::Unknown(_) => write!(f, "_")?,
            Type::Variable(name) => write!(f, "{}", name)?,
            Type::Quantified { quantifiers, ty } => {
                write!(f, "forall")?;
                for quantifier in quantifiers {
                    write!(f, " {}", quantifier)?;
                }
                write!(f, " . {}", ty)?;
            }
        };
        if parenthesise {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_proper(f, false)
    }
}

/// Resolves a type into a fully qualified type, given a list of the current
/// type parameters.
pub fn resolve_typep(
    module_path: &ModulePath,
    typep: &TypeP,
    type_params: &HashSet<String>,
    project_types: &ProjectTypesC,
) -> DiagnosticResult<Type> {
    match typep {
        TypeP::Named { identifier, args } => {
            if type_params.contains(&identifier.name) {
                if args.is_empty() {
                    DiagnosticResult::ok(Type::Variable(identifier.name.clone()))
                } else {
                    DiagnosticResult::ok_with(
                        Type::Variable(identifier.name.clone()),
                        ErrorMessage::new(
                            String::from("unexpected parameters on this type variable"),
                            Severity::Error,
                            Diagnostic::at(module_path.clone(), args[0].range()),
                        ),
                    )
                }
            } else {
                resolve_type_identifier(module_path, identifier, project_types).bind(|name| {
                    args.iter()
                        .map(|arg| resolve_typep(module_path, arg, type_params, project_types))
                        .collect::<DiagnosticResult<Vec<_>>>()
                        .map(|parameters| Type::Named { name, parameters })
                })
            }
        }
        TypeP::Function(left, right) => {
            resolve_typep(module_path, &left, type_params, project_types).bind(|left| {
                resolve_typep(module_path, &right, type_params, project_types)
                    .map(|right| Type::Function(Box::new(left), Box::new(right)))
            })
        }
        TypeP::Quantified { quantifiers, ty } => {
            let mut new_params = type_params.clone();
            new_params.extend(quantifiers.iter().map(|id| id.name.clone()));
            resolve_typep(module_path, ty, &new_params, project_types).map(|ty| {
                // Now that we've resolved the type with respect to these type parameters, we need to re-quantify over these type variables.
                match ty {
                    Type::Quantified {
                        quantifiers: resolved_quantifiers,
                        ty: resolved_ty,
                    } => Type::Quantified {
                        quantifiers: quantifiers
                            .iter()
                            .map(|id| id.name.clone())
                            .chain(resolved_quantifiers)
                            .collect(),
                        ty: resolved_ty,
                    },
                    ty => Type::Quantified {
                        quantifiers: quantifiers.iter().map(|id| id.name.clone()).collect(),
                        ty: Box::new(ty),
                    },
                }
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
