use std::{collections::binary_heap::Iter, iter::Peekable};

use crate::{Diagnostic, DiagnosticResult, ErrorMessage, Location, ModulePath, Range, Severity};

pub enum TokenType {
    Semicolon,
    Data,
    Identifier(String),
}

pub struct Token {
    token_type: TokenType,
    range: Range,
}

pub fn lex(module_path: &ModulePath, lines: Vec<String>) -> DiagnosticResult<Vec<Token>> {
    lines
        .into_iter()
        .enumerate()
        .map(|(line_number, line)| lex_line(module_path, line_number as u32, line))
        .collect::<DiagnosticResult<Vec<Vec<Token>>>>()
        .map(|list| list.into_iter().flatten().collect())
}

fn lex_line(
    module_path: &ModulePath,
    line_number: u32,
    line: String,
) -> DiagnosticResult<Vec<Token>> {
    let mut chars = line
        .chars()
        .enumerate()
        .map(|(i, c)| (i as u32, c))
        .peekable();
    let mut tokens = Vec::new();
    consume_whitespace(&mut chars);
    while let Some(&(col, _)) = chars.peek() {
        let token = lex_token(module_path, line_number, &mut chars);
        let should_break = token.failed();
        tokens.push(token);
        if should_break {
            break;
        }

        // Check that we actually consumed a character inside `lex_token`.
        if let Some(&(col2, _)) = chars.peek() {
            if col2 == col {
                panic!("no characters were consumed by `lex_token`, but it returned a success, at col {} of line \"{}\"", col, line);
            }
        }
        consume_whitespace(&mut chars);
    }
    DiagnosticResult::sequence(tokens)
}

/// This function parses a single token from the input stream.
/// It must consume at least one character from `chars` if it did not return a `DiagnosticResult::fail`,
/// otherwise we'll end up in an infinite loop.
fn lex_token(
    module_path: &ModulePath,
    line: u32,
    chars: &mut Peekable<impl Iterator<Item = (u32, char)>>,
) -> DiagnosticResult<Token> {
    let (col, ch) = *chars.peek().unwrap();
    let start = Location { line, col };
    let single_char_range = Range {
        start,
        end: Location { line, col: col + 1 },
    };

    match ch {
        ';' => {
            chars.next();
            DiagnosticResult::ok(Token {
                token_type: TokenType::Semicolon,
                range: single_char_range,
            })
        }
        _ => {
            if ch.is_alphabetic() {
                let (identifier, range) =
                    consume_predicate_one(line, chars, |c| c.is_alphanumeric());
                DiagnosticResult::ok(Token {
                    token_type: TokenType::Identifier(identifier),
                    range,
                })
            } else {
                DiagnosticResult::fail(ErrorMessage::new(
                    String::from("unexpected character"),
                    Severity::Error,
                    Diagnostic::at(module_path.clone(), start.into()),
                ))
            }
        }
    }
}

/// Consumes all characters conforming to a given predicate.
/// Returns the range of characters that the string contains.
/// If no characters were consumed, the range might be meaningless.
#[rustfmt::skip] // rustfmt messes up the Location blocks and makes them look different
fn consume_predicate<I, P>(line: u32, chars: &mut Peekable<I>, predicate: P) -> (String, Range)
where
    I: Iterator<Item = (u32, char)>,
    P: Fn(char) -> bool,
{
    let start_col = chars.peek().map(|value| value.0).unwrap_or(0);
    // Every loop iteration, we update end_col. This is because we can't be sure that there will be a next character to peek at.
    let mut end_col = start_col;

    let mut s = String::new();
    while let Some(&(_, ch)) = chars.peek() {
        if predicate(ch) {
            end_col += 1;
            s.push(ch);
            chars.next();
        } else {
            break;
        }
    }

    let start = Location { line, col: start_col };
    let end = Location { line, col: end_col };

    (s, Range { start, end })
}

/// Consumes one character, and then all characters conforming to a given predicate.
/// Returns the range of characters that the string contains.
/// If no characters were consumed, the range might be meaningless.
fn consume_predicate_one<I, P>(line: u32, chars: &mut Peekable<I>, predicate: P) -> (String, Range)
where
    I: Iterator<Item = (u32, char)>,
    P: Fn(char) -> bool,
{
    let (start_col, ch) = chars.next().unwrap();
    let (mut s, mut range) = consume_predicate(line, chars, predicate);
    if s.is_empty() {
        range.end.col = start_col + 1;
    }
    s.insert(0, ch);
    range.start.col = start_col;
    (s, range)
}

fn consume_whitespace<I>(chars: &mut Peekable<I>)
where
    I: Iterator<Item = (u32, char)>,
{
    consume_predicate(0, chars, |c| c.is_whitespace());
}
