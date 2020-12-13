use std::{collections::{HashMap, HashSet}, fmt::Display, fs::File, io::{BufRead, BufReader}, path::PathBuf};

use crate::{Diagnostic, DiagnosticResult, ErrorEmitter, ErrorMessage, Severity};

/// A list of path segments. These cannot contain forward or backward slashes, or colons.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModulePath(pub Vec<String>);

impl<'a> From<&'a ModulePath> for PathBuf {
    fn from(path: &'a ModulePath) -> Self {
        path.0.iter().collect()
    }
}

impl Display for ModulePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, item) in self.0.iter().enumerate() {
            if i != 0 {
                write!(f, "/")?;
            }
            write!(f, "{}", item)?;
        }
        Ok(())
    }
}

/// A single `.shoumei` file is called a module. It may export theorems, proofs, definitions, etc.
/// Module inclusions must be hierarchical and non-circular. This prevents circular proofs.
#[derive(Debug, Clone)]
pub struct Module {
    pub path: ModulePath,
}

impl Module {
    pub fn new(path: ModulePath) -> Self {
        Self { path }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Location {
    /// A 0-indexed line number.
    pub line: u32,
    /// A 0-indexed column number.
    pub col: u32,
}

impl Location {
    pub fn new(line: u32, col: u32) -> Self {
        Self { line, col }
    }
}

/// Loads resources from disk, lexing and parsing them.
pub struct ModuleLoader {
    /// When we begin loading a module, this set is updated. When a module is fully loaded, the corresponding value is removed.
    /// We can use this to track circular inclusions.
    currently_loading: HashSet<ModulePath>,
    /// A map containing all lexed and parsed modules.
    modules: HashMap<ModulePath, Module>,
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
        let file = match File::open(PathBuf::from(&module_path)) {
            Ok(file) => file.into(),
            Err(_) => {
                let message = ErrorMessage::new(
                    String::from("cannot open file"),
                    Severity::Error,
                    Diagnostic::in_file(module_path.clone()),
                );
                DiagnosticResult::fail(message)
            },
        };

        let lines = file.bind(|file| {
            let mut lines = Vec::new();
            for (line, line_number) in BufReader::new(file).lines().zip(0..) {
                match line {
                    Ok(line) => {
                        lines.push(line);
                    }
                    Err(_) => {
                        return DiagnosticResult::fail(ErrorMessage::new(
                            format!("file contained invalid UTF-8 on line {}", line_number + 1),
                            Severity::Error,
                            Diagnostic::in_file(module_path),
                        ));
                    }
                }
            }
            DiagnosticResult::ok(lines)
        });

        let lines = self.error_emitter.consume_diagnostic(lines);
    }

    /// Call this to retrieve all errors emitted while loading the modules.
    pub fn take_error_emitter(&mut self) -> ErrorEmitter {
        std::mem::take(&mut self.error_emitter)
    }
}
