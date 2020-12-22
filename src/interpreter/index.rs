//! Computes an index of all top-level items in a module,
//! storing type information. The module index is sufficient to determine the type
//! of any expression.

use std::collections::{hash_map::Entry, HashMap, HashSet};

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity};

use super::{
    parser::{IdentifierP, ModuleP},
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
    /// Maps type constructor names onto the types that they construct.
    pub type_ctors: HashMap<String, String>,
    pub symbols: HashMap<String, SymbolI>,
}

impl ModuleIndex {
    pub fn get_type_ctor_args(&self, type_ctor_name: &str) -> Vec<Type> {
        let mut ty = &self.symbols[type_ctor_name].symbol_type;
        let mut args = Vec::new();
        while let Type::Function(l, r) = ty {
            args.push((**l).clone());
            ty = r;
        }
        // Check that we've extracted all args correctly.
        match ty {
            Type::Named { name, .. } => {
                if name.name != self.type_ctors[type_ctor_name] {
                    panic!(
                        "did not give correct type: {} != {}",
                        name.name, self.type_ctors[type_ctor_name]
                    );
                }
            }
            _ => panic!("did not give named value"),
        }
        args
    }
}

pub type ProjectIndex = HashMap<ModulePath, ModuleIndex>;

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
    /// Where was this data statement written?
    pub range: Range,
    pub type_params: Vec<IdentifierP>,
    /// A list of all the type constructors for a `data` statement. For example, in `data Bool = True | False`, the two
    /// type constructors are `True` and `False`.
    /// Each type constructor is a function `... -> a`, where `a` is the type in the `data` declaration, defined in this module.
    pub type_ctors: Vec<TypeConstructorI>,
}

#[derive(Debug)]
pub struct TypeConstructorI {
    pub name: String,
    pub arguments: Vec<Type>,
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
    let mut type_ctors = HashMap::<String, String>::new();
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
                let symbol_type = resolve_typep(
                    module_path,
                    &definition.symbol_type,
                    &HashSet::new(),
                    project_types,
                );
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
        let data_type = Type::Named {
            name: QualifiedName {
                module_path: module_path.clone(),
                name: data.identifier.name.clone(),
                range: data.identifier.range,
            },
            parameters: data
                .type_params
                .iter()
                .map(|param| Type::Variable(param.name.clone()))
                .collect(),
        };

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
                let type_params = data
                    .type_params
                    .iter()
                    .map(|ident| ident.name.clone())
                    .collect::<HashSet<_>>();

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
                            // Let's add the type constructor as a function, making sure
                            // to add the argument types.

                            let mut arg_types = Vec::new();
                            for arg in &type_ctor.arguments {
                                // This argument could be a type parameter, or just a normal type.
                                let (resolved_type, mut inner_messages) =
                                    resolve_typep(module_path, arg, &type_params, project_types)
                                        .destructure();
                                if let Some(resolved_type) = resolved_type {
                                    arg_types.push(resolved_type);
                                }
                                if let Some(message) = inner_messages.first_mut() {
                                    message.help.push(HelpMessage {
                                        message: String::from(
                                            "if this was a type parameter, declare the type parameter here",
                                        ),
                                        help_type: HelpType::Help,
                                        diagnostic: Diagnostic::at_location(
                                            module_path.clone(),
                                            data.identifier.range.end,
                                        ),
                                    });
                                }
                                messages.append(&mut inner_messages);
                            }

                            // Convert the list of arguments [a, b, c, ...] into a function `a -> b -> c -> ... -> t` where
                            // `t` is the data type that we're parsing.
                            // We'll do this iteratively, since we want a hierarchy like `a -> (b -> (c -> (... -> t)))`.
                            // Probably could have used a fold, but this is good for now.
                            let mut type_ctor_type = data_type.clone();
                            while let Some(last_type) = arg_types.pop() {
                                type_ctor_type =
                                    Type::Function(Box::new(last_type), Box::new(type_ctor_type));
                            }

                            let symbol = SymbolI {
                                name: type_ctor.id.clone().into(),
                                symbol_type: type_ctor_type,
                            };
                            vacant.insert(symbol);
                            type_ctors
                                .insert(type_ctor.id.name.clone(), data.identifier.name.clone());
                        }
                    }
                }

                let type_ctors = data
                    .type_ctors
                    .iter()
                    .map(|type_ctor| {
                        type_ctor
                            .arguments
                            .iter()
                            .map(|arg| resolve_typep(module_path, arg, &type_params, project_types))
                            .collect::<DiagnosticResult<Vec<_>>>()
                            .map(|arguments| TypeConstructorI {
                                name: type_ctor.id.name.clone(),
                                arguments,
                            })
                    })
                    .collect::<DiagnosticResult<Vec<_>>>();
                let (_, mut inner_messages) = type_ctors
                    .map(|type_ctors| {
                        let datai = DataI {
                            range: data.identifier.range,
                            type_params: data.type_params.clone(),
                            type_ctors,
                        };
                        vacant.insert(TypeDeclarationI {
                            name: data.identifier.clone().into(),
                            decl_type: TypeDeclarationTypeI::Data(datai),
                        });
                    })
                    .destructure();
                messages.append(&mut inner_messages);
            }
        }
    }

    let index = ModuleIndex {
        types,
        type_ctors,
        symbols,
    };
    println!("Constructed index: {:#?}", index);
    DiagnosticResult::ok_with_many(index, messages)
}
