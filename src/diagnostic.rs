use std::{
    convert::TryInto,
    fs::File,
    io::{BufRead, BufReader},
    iter::FromIterator,
    path::PathBuf,
};

use crate::{Location, ModulePath, Range};

#[derive(Debug)]
pub struct Diagnostic {
    pub module_path: ModulePath,
    /// If the location is not specified, then the diagnostic refers to the entire file.
    pub range: Option<Range>,
}

impl Diagnostic {
    pub fn in_file(module_path: ModulePath) -> Self {
        Self {
            module_path,
            range: None,
        }
    }

    pub fn at_location(module_path: ModulePath, location: Location) -> Self {
        Self {
            module_path,
            range: Some(location.into()),
        }
    }

    pub fn at(module_path: ModulePath, range: Range) -> Self {
        Self {
            module_path,
            range: Some(range),
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

    pub fn new_with(
        message: String,
        severity: Severity,
        diagnostic: Diagnostic,
        help: HelpMessage,
    ) -> Self {
        Self {
            message,
            severity,
            diagnostic,
            help: vec![help],
        }
    }
}

/// Even if warnings or errors are emitted, we may still be able to continue parsing the code.
/// So we need some kind of result type that allows us to raise errors or other messages while still
/// retaining an 'Ok' state, as far as the rest of the code is aware.
///
/// Upon exiting the program, all error messages will be scanned to check the most severe error level.
/// If any errors exist, no warnings will be emitted.
#[derive(Debug)]
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
    /// This is the monadic `return` operation.
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

    pub fn ok_with_many(value: T, messages: Vec<ErrorMessage>) -> Self {
        Self {
            value: Some(value),
            messages,
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
    pub fn map<F, U>(self, f: F) -> DiagnosticResult<U>
    where
        F: FnOnce(T) -> U,
    {
        match self.value {
            Some(value) => DiagnosticResult {
                value: Some(f(value)),
                messages: self.messages,
            },
            None => DiagnosticResult {
                value: None,
                messages: self.messages,
            },
        }
    }

    /// A monadic bind operation that consumes this diagnostic result and uses the value it contains, if it exists,
    /// to produce a new diagnostic result.
    pub fn bind<F, U>(mut self, f: F) -> DiagnosticResult<U>
    where
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
            }
            None => DiagnosticResult {
                value: None,
                messages: self.messages,
            },
        }
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    pub fn sequence(
        results: impl IntoIterator<Item = DiagnosticResult<T>>,
    ) -> DiagnosticResult<Vec<T>> {
        results
            .into_iter()
            .fold(DiagnosticResult::ok(Vec::new()), |acc, i| {
                acc.bind(|mut list| {
                    i.bind(|i| {
                        list.push(i);
                        DiagnosticResult::ok(list)
                    })
                })
            })
    }

    /// Returns true if the computation succeeded.
    pub fn succeeded(&self) -> bool {
        self.value.is_some()
    }

    /// Returns true if the computation failed.
    pub fn failed(&self) -> bool {
        self.value.is_none()
    }
}

impl<T> FromIterator<DiagnosticResult<T>> for DiagnosticResult<Vec<T>> {
    fn from_iter<U: IntoIterator<Item = DiagnosticResult<T>>>(iter: U) -> Self {
        DiagnosticResult::sequence(iter)
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

    pub fn process(&mut self, messages: impl IntoIterator<Item = ErrorMessage>) {
        for message in messages {
            match message.severity {
                Severity::Warning => {
                    if !self.has_emitted_error {
                        self.warnings.push(message);
                    }
                }
                Severity::Error => {
                    self.has_emitted_error = true;
                    self.emit(message);
                    self.warnings.clear();
                }
            }
        }
    }

    fn emit(&self, message: ErrorMessage) {
        use console::style;

        match message.severity {
            Severity::Error => println!(
                "{}{} {}",
                style("error").red().bright(),
                style(":").white().bright(),
                style(message.message).white().bright()
            ),
            Severity::Warning => println!(
                "{}: {}",
                style("warning").yellow().bright(),
                message.message
            ),
        }
        self.print_message(message.diagnostic);

        for help in message.help {
            match help.help_type {
                HelpType::Help => println!(
                    "{} {}",
                    style("help:").white().bright(),
                    style(help.message).white().bright()
                ),
                HelpType::Note => println!(
                    "{} {}",
                    style("note:").white().bright(),
                    style(help.message).white().bright()
                ),
            }
            self.print_message(help.diagnostic);
        }
    }

    fn print_message(&self, diagnostic: Diagnostic) {
        use console::style;

        if let Some(range) = diagnostic.range {
            // We calculate the amount of digits in the line number.
            let line_number_max_digits = range.start.line.max(range.end.line).to_string().len();

            println!(
                "{}{} {}:{}:{}",
                " ".repeat(line_number_max_digits),
                style("-->").cyan().bright(),
                diagnostic.module_path,
                range.start.line + 1,
                range.start.col + 1
            );

            // There's no point keeping the file content in memory just in case we need to print out errors.
            // So we'll re-open the offending file here.
            match File::open(PathBuf::from(&diagnostic.module_path)) {
                Ok(f) => {
                    let br = BufReader::new(f);
                    let mut lines = br.lines().skip(range.start.line.try_into().unwrap());

                    // Print out each relevant line of code, starting and finishing with an empty line.
                    // Empty line.
                    println!(
                        "{: >2$} {}",
                        "",
                        style("|").cyan().bright(),
                        line_number_max_digits,
                    );

                    // Relevant lines.
                    for line in range.start.line..=range.end.line {
                        let (line_data, line_length) = match lines.next() {
                            Some(Ok(line)) => {
                                let line_length = line.chars().count();
                                (style(line), line_length)
                            }
                            Some(Err(_)) => {
                                (style("could not decode line".to_string()).red().bright(), 0)
                            }
                            None => (style("could not read line".to_string()).red().bright(), 0),
                        };

                        // Signal where on the line the error occured if we're on the first line.
                        if line == range.start.line {
                            // If the error was on a single line, we'll just underline where the error occured.
                            // We don't need an overline.
                            if range.start.line != range.end.line {
                                println!(
                                    "{: >4$} {} {: >5$}{}",
                                    "",
                                    style("|").cyan().bright(),
                                    "",
                                    style("v".repeat(line_length - range.start.col as usize))
                                        .yellow()
                                        .bright(),
                                    line_number_max_digits,
                                    range.start.col as usize,
                                );
                            }
                        }

                        println!(
                            "{: >3$} {} {}",
                            style((line + 1).to_string()).cyan().bright(),
                            style("|").cyan().bright(),
                            line_data,
                            line_number_max_digits,
                        );

                        // Signal where on the line the error occured if we're on the last line.
                        if line == range.end.line {
                            if range.start.line == range.end.line {
                                // The error was on a single line. We'll just underline where the error occured.
                                println!(
                                    "{: >4$} {} {: >5$}{}",
                                    "",
                                    style("|").cyan().bright(),
                                    "",
                                    style(
                                        "^".repeat(
                                            range.end.col as usize - range.start.col as usize
                                        )
                                    )
                                    .yellow()
                                    .bright(),
                                    line_number_max_digits,
                                    range.start.col as usize,
                                );
                            } else {
                                // Underline from the start of the line to the end of the error.
                                println!(
                                    "{: >3$} {} {}",
                                    "",
                                    style("|").cyan().bright(),
                                    style("^".repeat(range.end.col as usize)).yellow().bright(),
                                    line_number_max_digits,
                                );
                            }
                        }
                    }

                    // Empty line.
                    println!(
                        "{: >2$} {}",
                        "",
                        style("|").cyan().bright(),
                        line_number_max_digits,
                    );
                }
                Err(_) => {
                    println!("{}", style("could not open file").red().bright());
                }
            }
        } else {
            println!(
                "{} {}",
                style("-->").cyan().bright(),
                diagnostic.module_path
            );
        }
    }

    pub fn emit_all(mut self) {
        let warnings = std::mem::take(&mut self.warnings);
        for message in warnings {
            self.emit(message);
        }
    }
}
