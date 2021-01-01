//! Resolves an unqualified name into a fully qualified name with type information.

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, Severity};

use super::{
    syntax_tree::{IdentifierP, TypeP},
    type_check::TypeVariable,
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
}

impl Type {
    /// Replaces named type parameters e.g. `a` with their concrete types.
    /// For example, calling this function on `Just a`, when `named_type_parameters = [a]` and `concrete_type_parameters = [Bool]` gives `Just Bool`.
    pub fn replace_type_variables(
        self,
        named_type_parameters: &[IdentifierP],
        concrete_type_parameters: &[Type],
    ) -> Type {
        match self {
            Type::Named { name, parameters } => Type::Named {
                name,
                parameters: parameters
                    .into_iter()
                    .map(|param| {
                        param
                            .replace_type_variables(named_type_parameters, concrete_type_parameters)
                    })
                    .collect(),
            },
            Type::Function(l, r) => Type::Function(
                Box::new(l.replace_type_variables(named_type_parameters, concrete_type_parameters)),
                Box::new(r.replace_type_variables(named_type_parameters, concrete_type_parameters)),
            ),
            Type::Variable(name) => {
                // Is this type variable in our list of named type variables?
                if let Some((i, _)) = named_type_parameters
                    .iter()
                    .enumerate()
                    .find(|(_, param)| param.name == name)
                {
                    concrete_type_parameters[i].clone()
                } else {
                    // This was not in the list; just return it verbatim.
                    Type::Variable(name)
                }
            }
        }
    }

    /// You can instantiate a type into a type variable,
    /// by letting all unknown variables be polymorphic type variables, over which the type is quantified.
    pub fn instantiate(&self) -> TypeVariable {
        self.instantiate_with(&mut HashMap::new())
    }

    /// While we're instantiating a type, we need to keep track of all of the named type variables
    /// and which IDs we've assigned them.
    fn instantiate_with(&self, ids: &mut HashMap<String, TypeVariableId>) -> TypeVariable {
        match self {
            Type::Named { name, parameters } => TypeVariable::Named {
                name: name.clone(),
                parameters: parameters
                    .iter()
                    .map(|p| p.instantiate_with(ids))
                    .collect::<Vec<_>>(),
            },
            Type::Function(l, r) => {
                let l2 = l.instantiate_with(ids);
                let r2 = r.instantiate_with(ids);
                TypeVariable::Function(Box::new(l2), Box::new(r2))
            }
            Type::Variable(name) => TypeVariable::Unknown(
                *ids.entry(name.clone())
                    .or_insert_with(TypeVariableId::default),
            ),
        }
    }

    /// You can convert a type into a type variable without quantifying over any variable types.
    /// This is used primarily for arguments and return types of functions, in which we should never
    /// quantify over the type variables.
    pub fn as_variable(&self) -> TypeVariable {
        match self {
            Type::Named { name, parameters } => TypeVariable::Named {
                name: name.clone(),
                parameters: parameters
                    .iter()
                    .map(|p| p.as_variable())
                    .collect::<Vec<_>>(),
            },
            Type::Function(l, r) => {
                let l2 = l.as_variable();
                let r2 = r.as_variable();
                TypeVariable::Function(Box::new(l2), Box::new(r2))
            }
            Type::Variable(name) => TypeVariable::Variable(name.clone()),
        }
    }
}

/// An unknown type, used for intermediate values of expressions that we don't know the type of.
/// To generate a new type variable, call `default`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TypeVariableId(u64);
static TYPE_VARIABLE_ID_GENERATOR: AtomicU64 = AtomicU64::new(0);

impl Default for TypeVariableId {
    fn default() -> Self {
        Self(TYPE_VARIABLE_ID_GENERATOR.fetch_add(1, Ordering::Relaxed))
    }
}

impl Type {
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
            Type::Variable(name) => write!(f, "{}", name)?,
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
