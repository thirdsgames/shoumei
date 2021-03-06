use std::collections::{HashMap, HashSet};

use type_check::{Definition, Module};

use crate::{parser::*, Diagnostic, ErrorEmitter, ErrorMessage, Severity};

/// Loads resources from disk, lexing and parsing them.
pub struct ModuleLoader {
    /// When we begin loading a module, this set is updated. When a module is fully loaded, the corresponding value is removed.
    /// We can use this to track circular inclusions.
    currently_loading: HashSet<ModulePath>,
    /// A map containing all lexed and parsed modules.
    /// If a module could not be parsed, the result here is None to show that the module was loaded but not parsed.
    modules: HashMap<ModulePath, Option<Module>>,
    error_emitter: ErrorEmitter,
}

impl ModuleLoader {
    pub fn new(error_emitter: ErrorEmitter) -> Self {
        Self {
            currently_loading: HashSet::new(),
            modules: HashMap::new(),
            error_emitter,
        }
    }

    /// Any errors or other messages while loading are emitted to the given ErrorEmitter.
    pub fn load(&mut self, module_path: ModulePath) {
        if self.currently_loading.contains(&module_path) {
            self.error_emitter.process(vec![ErrorMessage::new(
                String::from("cyclic module inclusion detected"),
                Severity::Error,
                Diagnostic::in_file(module_path),
            )]);
            return;
        }
        self.currently_loading.insert(module_path.clone());

        let module = self.error_emitter.consume_diagnostic(parse(&module_path));
        if let Some(module) = &module {
            println!("Parsed module.");
            println!("{}", module);
        }

        self.currently_loading.remove(&module_path);
        self.modules.insert(module_path, module);
    }

    /// Call this to retrieve all errors emitted while loading the modules.
    pub fn take_error_emitter(&mut self) -> ErrorEmitter {
        std::mem::take(&mut self.error_emitter)
    }

    /// Returns the module at the given path, if it was loaded and parsed correctly.
    pub fn module(&self, module_path: &ModulePath) -> Option<&Module> {
        self.modules
            .get(module_path)
            .map(|inner| inner.as_ref())
            .flatten()
    }

    /// Returns the definition with the given name, if it was loaded and parsed correctly.
    pub fn definition(&self, name: &QualifiedName) -> Option<&Definition> {
        self.module(&name.module_path)
            .and_then(|module| module.definitions.get(&name.name))
    }
}
