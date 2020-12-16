use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    fs::File,
    io::{BufRead, BufReader},
    ops::{Deref, DerefMut},
    path::PathBuf,
};

use crate::{Diagnostic, DiagnosticResult, ErrorEmitter, ErrorMessage, Severity, interpreter::{Token, TypeConstructor}};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Range {
    /// The start of this range of characters, inclusive.
    pub start: Location,
    /// The end of this range of characters, exclusive.
    pub end: Location,
}

impl From<Location> for Range {
    fn from(location: Location) -> Self {
        Self {
            start: location,
            end: Location {
                line: location.line,
                col: location.col + 1,
            },
        }
    }
}

impl Range {
    pub fn union(self, other: Range) -> Range {
        Range {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

/// A list of path segments. These cannot contain forward or backward slashes, or colons.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
/// This `Module` struct contains the parsed abstract syntax tree of a module.
/// Module inclusions must be hierarchical and non-circular. This prevents circular proofs.
#[derive(Debug)]
pub struct Module {
    pub data: Vec<Data>,
    pub definitions: Vec<Definition>,
}

/// An object associated with an area in code.
/// Automatically derefs to the contained value.
#[derive(Debug)]
pub struct Ranged<T> {
    value: T,
    module_path: ModulePath,
    range: Range,
}

impl<T> Deref for Ranged<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for Ranged<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> Ranged<T> {
    pub fn module_path(&self) -> &ModulePath {
        &self.module_path
    }

    pub fn range(&self) -> &Range {
        &self.range
    }
}

#[derive(Debug)]
pub enum Type {
    /// An explicitly named type without type parameters, e.g. `Bool`.
    Named(Ranged<String>),
    /// A function `a -> b`.
    /// Functions with more arguments, e.g. `a -> b -> c` are represented as
    /// curried functions, e.g. `a -> (b -> c)`.
    Function(Box<Type>, Box<Type>),
}

/// A `data` block, used to define sum or product types.
#[derive(Debug)]
pub struct Data {
    pub name: Token,
    pub type_ctors: Vec<TypeConstructor>,
}

/// A `def` block. Defines a symbol's type and what values it takes under what circumstances.
#[derive(Debug)]
pub struct Definition {
    pub name: Token,
    pub symbol_type: Type,
}

/// Loads resources from disk, lexing and parsing them.
pub struct ModuleLoader {
    /// When we begin loading a module, this set is updated. When a module is fully loaded, the corresponding value is removed.
    /// We can use this to track circular inclusions.
    currently_loading: HashSet<ModulePath>,
    /// A map containing all lexed and parsed modules.
    /// If a module could not be parsed, the result here is None to show that
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

        // This chain of `bind`s is very similar to monadic `do` notation in Haskell.
        // file <- ...
        // lines <- ...
        let file = match File::open(PathBuf::from(&module_path)) {
            Ok(file) => file.into(),
            Err(_) => {
                let message = ErrorMessage::new(
                    String::from("cannot open file"),
                    Severity::Error,
                    Diagnostic::in_file(module_path.clone()),
                );
                DiagnosticResult::fail(message)
            }
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
                            Diagnostic::in_file(module_path.clone()),
                        ));
                    }
                }
            }
            DiagnosticResult::ok(lines)
        });

        let tokens = lines.bind(|lines| crate::interpreter::lex(&module_path, lines));
        let token_block =
            tokens.bind(|tokens| crate::interpreter::process_indent(&module_path, tokens));
        let token_block = token_block
            .bind(|token_block| crate::interpreter::process_brackets(&module_path, token_block));
        let module =
            token_block.bind(|token_block| crate::interpreter::parse(&module_path, token_block));
        println!("{:#?}", module);

        let module = self.error_emitter.consume_diagnostic(module);

        self.currently_loading.remove(&module_path);
        self.modules.insert(module_path, module);
    }

    /// Call this to retrieve all errors emitted while loading the modules.
    pub fn take_error_emitter(&mut self) -> ErrorEmitter {
        std::mem::take(&mut self.error_emitter)
    }
}
