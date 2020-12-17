//! Computes an index of all top-level items in a module,
//! storing type information. The module index is sufficient to determine the type
//! of any expression.

use std::collections::{hash_map::Entry, HashMap};

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity};

use super::{
    parser::ModuleP,
    type_resolve::{resolve_typep, Type},
    types::{DefinedName, ProjectTypesC},
    ModulePath, QualifiedName, Range,
};

/// An index of all top-level items in a module.
///
/// Realistically this type should probably have the `I` suffix, but in my opinion it's pretty self-evident.
#[derive(Debug)]
pub struct ModuleIndex {
    pub types: HashMap<String, TypeDeclarationI>,
    pub symbols: HashMap<String, SymbolI>,
}

/// A type declaration, e.g. `data Bool = True | False`.
#[derive(Debug)]
pub struct TypeDeclarationI {
    /// This is kept here mostly because it contains the `Range` where it was defined.
    pub name: DefinedName,
    pub decl_type: TypeDeclarationTypeI,
}

#[derive(Debug)]
pub enum TypeDeclarationTypeI {
    Data(DataI),
}

/// A `data` statement, e.g. `data Bool = True | False`.
#[derive(Debug)]
pub struct DataI {
    /// A list of all the type constructors for a `data` statement. For example, in `data Bool = True | False`, the two
    /// type constructors are `True` and `False`.
    /// Each type constructor is a function `... -> a`, where `a` is the type in the `data` declaration, defined in this module.
    pub type_ctors: Vec<String>,
}

/// A top-level symbol, i.e. a `def` block.
#[derive(Debug)]
pub struct SymbolI {
    pub name: DefinedName,
    pub symbol_type: Type,
}

/// Returns a generic error message about multiply defined symbols, making sure that the "earlier" symbol
/// actually was the one that appeared earlier in the file.
fn name_used_earlier(module_path: &ModulePath, range1: Range, range2: Range) -> ErrorMessage {
    ErrorMessage::new_with(
        String::from("this name was used earlier for another definition"),
        Severity::Error,
        Diagnostic::at(module_path.clone(), range1.max(range2)),
        HelpMessage {
            message: String::from("previously used here"),
            help_type: HelpType::Note,
            diagnostic: Diagnostic::at(module_path.clone(), range1.min(range2)),
        },
    )
}

/// Computes the index for a module.
pub fn index(
    module_path: &ModulePath,
    module: &ModuleP,
    project_types: &ProjectTypesC,
) -> DiagnosticResult<ModuleIndex> {
    let mut messages = Vec::new();

    let mut types = HashMap::<String, TypeDeclarationI>::new();
    let mut symbols = HashMap::<String, SymbolI>::new();

    for definition in &module.definitions {
        match symbols.entry(definition.identifier.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    module_path,
                    definition.identifier.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add this definition into the map.
                let symbol_type =
                    resolve_typep(module_path, &definition.symbol_type, project_types);
                let (symbol_type, mut inner_messages) = symbol_type.destructure();
                messages.append(&mut inner_messages);
                if let Some(symbol_type) = symbol_type {
                    let definition = SymbolI {
                        name: definition.identifier.clone().into(),
                        symbol_type,
                    };
                    vacant.insert(definition);
                }
            }
        }
    }

    for data in &module.data {
        let data_type = Type::Named(QualifiedName {
            module_path: module_path.clone(),
            name: data.identifier.name.clone(),
            range: data.identifier.range,
        });
        match types.entry(data.identifier.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    module_path,
                    data.identifier.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add the definition into the map.
                for type_ctor in &data.type_ctors {
                    // We need to add each type constructor as a function.
                    match symbols.entry(type_ctor.id.name.clone()) {
                        Entry::Occupied(occupied) => {
                            messages.push(name_used_earlier(
                                module_path,
                                type_ctor.id.range,
                                occupied.get().name.range,
                            ));
                        }
                        Entry::Vacant(vacant) => {
                            // Let's add the type constructor as a function.
                            // Once we have actual type constructors that take values, this will need
                            // to include some diagnostics, since those values might fail to type check.
                            let symbol = SymbolI {
                                name: type_ctor.id.clone().into(),
                                symbol_type: data_type.clone(),
                            };
                            vacant.insert(symbol);
                        }
                    }
                }
                let datai = DataI {
                    type_ctors: data
                        .type_ctors
                        .iter()
                        .map(|type_ctor| type_ctor.id.name.clone())
                        .collect(),
                };
                vacant.insert(TypeDeclarationI {
                    name: data.identifier.clone().into(),
                    decl_type: TypeDeclarationTypeI::Data(datai),
                });
            }
        }
    }

    let index = ModuleIndex { types, symbols };
    DiagnosticResult::ok_with_many(index, messages)
}
