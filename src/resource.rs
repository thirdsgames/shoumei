use std::fs::File;

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, Severity};

#[derive(Debug, Clone)]
pub struct Resource {
    pub file_path: String,
}

impl Resource {
    pub fn new(file_path: String) -> Self {
        Self { file_path }
    }

    pub fn open_file(&self) -> DiagnosticResult<File> {
        match File::open(self.file_path.as_str()) {
            Ok(file) => file.into(),
            Err(_) => {
                let message = ErrorMessage::new(
                    String::from("cannot open file"),
                    Severity::Error,
                    Diagnostic::in_file(self.clone()),
                );
                DiagnosticResult::fail(message)
            },
        }
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
