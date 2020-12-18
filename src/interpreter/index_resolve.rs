use crate::{Diagnostic, DiagnosticResult, ErrorMessage, Severity};

use super::{
    index::{ProjectIndex, SymbolI, TypeDeclarationTypeI},
    parser::IdentifierP,
    ModulePath, QualifiedName,
};

/// When a type constructor is used in code, e.g. `False`.
/// For type constructor declarations, see `TypeConstructor`.
#[derive(Debug)]
pub struct TypeConstructorInvocation {
    /// The data type that the type constructor belongs to.
    pub data_type: QualifiedName,
    /// The name of the type constructor that was called.
    pub type_ctor: String,
}

/// Resolves the use of a type constructor.
pub fn resolve_type_constructor(
    module_path: &ModulePath,
    identifier: &IdentifierP,
    project_index: &ProjectIndex,
) -> DiagnosticResult<TypeConstructorInvocation> {
    // We don't have `import`-style statements yet, so let's just only search for types in the current module path.
    let module_index = &project_index[module_path];
    match module_index.type_ctors.get(&identifier.name) {
        Some(data_name) => {
            if let TypeDeclarationTypeI::Data(datai) = &module_index.types[data_name].decl_type {
                DiagnosticResult::ok(TypeConstructorInvocation {
                    data_type: QualifiedName {
                        module_path: module_path.clone(),
                        name: data_name.clone(),
                        range: datai.range,
                    },
                    type_ctor: identifier.name.clone(),
                })
            } else {
                panic!("type constructor was for a non-data type");
            }
        }
        None => DiagnosticResult::fail(ErrorMessage::new(
            String::from("could not resolve type constructor"),
            Severity::Error,
            Diagnostic::at(module_path.clone(), identifier.range),
        )),
    }
}

/// Resolves a symbol. Returns the module that it was defined in, along with the symbol itself.
pub fn resolve_symbol<'a>(
    module_path: &ModulePath,
    identifier: &IdentifierP,
    project_index: &'a ProjectIndex,
) -> DiagnosticResult<(&'a ModulePath, &'a SymbolI)> {
    // We don't have `import`-style statements yet, so let's just only search for types in the current module path.
    let key = project_index.get_key_value(module_path);
    if let Some((module_path_long_lifetime, module_index)) =
        project_index.get_key_value(module_path)
    {
        match module_index.symbols.get(&identifier.name) {
            Some(symbol) => DiagnosticResult::ok((module_path_long_lifetime, symbol)),
            None => DiagnosticResult::fail(ErrorMessage::new(
                String::from("could not resolve symbol"),
                Severity::Error,
                Diagnostic::at(module_path.clone(), identifier.range),
            )),
        }
    } else {
        panic!("module was not in index")
    }
}
