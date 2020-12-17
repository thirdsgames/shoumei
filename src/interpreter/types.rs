//! Caches all of the types declared in a module, specifically, all `data` statements.
//!
//! This module does not validate the contents of `def` blocks to check that their types match and patterns are exhaustive,
//! that is kept to a later type checking phase.

use std::collections::{hash_map::Entry, HashMap};

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity};

use super::{
    parser::{IdentifierP, ModuleP},
    ModulePath, Range,
};

/// A set of all types declared in a single module, mapping type names to their declarations.
pub type ModuleTypesC = HashMap<String, TypeDeclarationC>;

/// All types known about in an entire project.
pub type ProjectTypesC = HashMap<ModulePath, ModuleTypesC>;

/// A type declaration, e.g. `data Bool = True | False`.
#[derive(Debug)]
pub struct TypeDeclarationC {
    pub name: DefinedName,
    pub decl_type: TypeDeclarationTypeC,
}

#[derive(Debug)]
pub enum TypeDeclarationTypeC {
    Data(DataC),
}

/// A `data` statement, e.g. `data Bool = True | False`.
#[derive(Debug)]
pub struct DataC {
    /// A list of all the type constructors for a `data` statement. For example, in `data Bool = True | False`, the two
    /// type constructors are `True` and `False`.
    pub type_ctors: Vec<TypeConstructorC>,
}

#[derive(Debug)]
pub struct TypeConstructorC {
    pub name: DefinedName,
}

/// The name of a type/symbol where it is defined.
/// For example, the `Bool` in `data Bool = ...` but *not* the `Bool` in `Bool -> Bool`.
/// These other usages must be qualified names, not defined names.
///
/// This type is not `Clone` because it is unsound to have two symbols with identical names.
/// You can refer to defined names using qualified names.
#[derive(Debug)]
pub struct DefinedName {
    pub name: String,
    pub range: Range,
}

impl From<IdentifierP> for DefinedName {
    fn from(id: IdentifierP) -> Self {
        Self {
            name: id.name,
            range: id.range,
        }
    }
}

/// Computes the types declared in the module.
pub fn compute_types(module_path: &ModulePath, module: &ModuleP) -> DiagnosticResult<ModuleTypesC> {
    let mut messages = Vec::new();
    let mut types = ModuleTypesC::new();
    for data in &module.data {
        let entry = types.entry(data.identifier.name.clone());
        match entry {
            Entry::Occupied(occupied) => {
                // This type has already been defined.
                // This is an error.
                messages.push(ErrorMessage::new_with(
                    String::from("type with this name was already defined"),
                    Severity::Error,
                    Diagnostic::at(module_path.clone(), data.identifier.range),
                    HelpMessage {
                        message: String::from("previously defined here"),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(module_path.clone(), occupied.get().name.range),
                    },
                ));
            }
            Entry::Vacant(vacant) => {
                // This type has not yet been defined.
                // So, let's add it to the list of types.
                let mut type_ctors = Vec::<TypeConstructorC>::new();
                for type_ctor in &data.type_ctors {
                    // Is this a duplicate type constructor name?
                    let mut was_valid = true;
                    for validated_type_ctor in &type_ctors {
                        if type_ctor.id.name == validated_type_ctor.name.name {
                            was_valid = false;
                            messages.push(ErrorMessage::new_with(
                                String::from("type constructor with this name was already defined"),
                                Severity::Error,
                                Diagnostic::at(module_path.clone(), type_ctor.id.range),
                                HelpMessage {
                                    message: String::from("previously defined here"),
                                    help_type: HelpType::Note,
                                    diagnostic: Diagnostic::at(
                                        module_path.clone(),
                                        validated_type_ctor.name.range,
                                    ),
                                },
                            ))
                        }
                    }
                    if was_valid {
                        type_ctors.push(TypeConstructorC {
                            name: type_ctor.id.clone().into(),
                        });
                    }
                }
                vacant.insert(TypeDeclarationC {
                    name: data.identifier.clone().into(),
                    decl_type: TypeDeclarationTypeC::Data(DataC { type_ctors }),
                });
            }
        }
    }

    DiagnosticResult::ok_with_many(types, messages)
}
