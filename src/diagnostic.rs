use crate::{Location, ModulePath};

#[derive(Debug)]
pub struct Diagnostic {
    pub module_path: ModulePath,
    /// If the location is not specified, then the diagnostic refers to the entire file.
    pub location: Option<Location>,
}

impl Diagnostic {
    pub fn in_file(module_path: ModulePath) -> Self {
        Self {
            module_path,
            location: None,
        }
    }

    pub fn at(module_path: ModulePath, location: Location) -> Self {
        Self {
            module_path,
            location: Some(location),
        }
    }
}

/// https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-levels
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HelpType {
    Help,
    Note,
}

/// Represents an error/warning/lint message displayed to the user.
#[derive(Debug)]
pub struct ErrorMessage {
    pub message: String,
    pub severity: Severity,
    pub diagnostic: Diagnostic,
    pub help: Vec<HelpMessage>,
}

/// TODO: consider https://doc.rust-lang.org/nightly/nightly-rustc/rustc_errors/enum.Applicability.html
#[derive(Debug)]
pub struct HelpMessage {
    pub message: String,
    pub help_type: HelpType,
    pub diagnostic: Diagnostic,
}

impl ErrorMessage {
    pub fn new(message: String, severity: Severity, diagnostic: Diagnostic) -> Self {
        Self {
            message,
            severity,
            diagnostic,
            help: Vec::new(),
        }
    }
}

/// Even if warnings or errors are emitted, we may still be able to continue parsing the code.
/// So we need some kind of result type that allows us to raise errors or other messages while still
/// retaining an 'Ok' state, as far as the rest of the code is aware.
///
/// Upon exiting the program, all error messages will be scanned to check the most severe error level.
/// If any errors exist, no warnings will be emitted.
#[must_use = "errors must be processed by an ErrorEmitter"]
pub struct DiagnosticResult<T> {
    /// If this is `None`, then the computation failed. Error messages will be contained inside `messages.
    /// If this is `Some`, then the computation succeeded, but there may still be some messages (e.g. warnings
    /// or errors) inside `messages`.
    value: Option<T>,
    messages: Vec<ErrorMessage>,
}

impl<T> From<T> for DiagnosticResult<T> {
    fn from(value: T) -> Self {
        Self::ok(value)
    }
}

impl<T> DiagnosticResult<T> {
    /// The computation succeeded with no messages.
    pub fn ok(value: T) -> Self {
        Self {
            value: Some(value),
            messages: Vec::new(),
        }
    }

    /// The computation succeeded, but there was some error or warning message.
    pub fn ok_with(value: T, message: ErrorMessage) -> Self {
        Self {
            value: Some(value),
            messages: vec![message],
        }
    }

    /// The computation failed. An error message is mandatory if the computation failed.
    pub fn fail(message: ErrorMessage) -> Self {
        assert!(message.severity == Severity::Error);
        Self {
            value: None,
            messages: vec![message],
        }
    }

    /// Apply an infallible operation to the value inside this result. If the operation could fail, use [`DiagnosticResult::bind`] instead.
    pub fn map<F, U>(self, f: F) -> DiagnosticResult<U> where
        F: FnOnce(T) -> U,
    {
        match self.value {
            Some(value) => {
                DiagnosticResult {
                    value: Some(f(value)),
                    messages: self.messages,
                }
            }
            None => {
                DiagnosticResult {
                    value: None,
                    messages: self.messages,
                }
            }
        }
    }

    /// A monadic bind operation that consumes this diagnostic result and uses the value it contains, if it exists,
    /// to produce a new diagnostic result.
    pub fn bind<F, U>(mut self, f: F) -> DiagnosticResult<U> where
        F: FnOnce(T) -> DiagnosticResult<U>,
    {
        match self.value {
            Some(value) => {
                let mut result = f(value);
                self.messages.append(&mut result.messages);
                DiagnosticResult {
                    value: result.value,
                    messages: self.messages,
                }
            },
            None => {
                DiagnosticResult {
                    value: None,
                    messages: self.messages,
                }
            },
        }
    }
}

/// Prints error and warning messages.
#[must_use = "error messages must be emitted using the emit_all method"]
pub struct ErrorEmitter {
    /// The error emitter caches warnings and will not output them until we have verified that there are no errors.
    /// Order of emission of the error messages is preserved.
    warnings: Vec<ErrorMessage>,

    /// If this is true, warnings will not be cached or emitted.
    has_emitted_error: bool,
}

impl Default for ErrorEmitter {
    fn default() -> Self {
        Self {
            warnings: Vec::new(),
            has_emitted_error: false,
        }
    }
}

impl ErrorEmitter {
    pub fn new() -> Self {
        Default::default()
    }

    /// Consumes the errors of a diagnostic result, yielding the encapsulated value.
    pub fn consume_diagnostic<T>(&mut self, diagnostic_result: DiagnosticResult<T>) -> Option<T> {
        let DiagnosticResult { value, messages } = diagnostic_result;
        self.process(messages);
        value
    }

    pub fn process(&mut self, messages: impl IntoIterator<Item=ErrorMessage>) {
        for message in messages {
            match message.severity {
                Severity::Warning => {
                    if !self.has_emitted_error {
                        self.warnings.push(message);
                    }
                },
                Severity::Error => {
                    self.has_emitted_error = true;
                    self.emit(message);
                    self.warnings.clear();
                },
            }
        }
    }

    fn emit(&self, message: ErrorMessage) {
        use console::style;

        match message.severity {
            Severity::Error => println!("{}: {}", style("error").red().bright(), message.message),
            Severity::Warning => println!("{}: {}", style("warning").yellow().bright(), message.message),
        }

        if let Some(location) = message.diagnostic.location {
            println!("{} {}:{}:{}", style("-->").cyan().bright(), message.diagnostic.module_path, location.line + 1, location.col + 1);
        } else {
            // Amount of spaces before the --> should depend on the amount of digits in the line number.
            println!("{} {}", style("-->").cyan().bright(), message.diagnostic.module_path);
        }
    }

    pub fn emit_all(mut self) {
        let warnings = std::mem::take(&mut self.warnings);
        for message in warnings {
            self.emit(message);
        }
    }
}
