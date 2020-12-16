use std::iter::Peekable;

use crate::{
    Data, Definition, Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Location,
    Module, ModulePath, Range, Severity, Type,
};

use super::{Token, TokenBlock, TokenLine, TokenTree, TokenType};

/// Any top level item such as a definition or theorem.
#[derive(Debug)]
enum Item {
    Data(Data),
    Definition(Definition),
}

pub fn parse(module_path: &ModulePath, token_block: TokenBlock) -> DiagnosticResult<Module> {
    let mut lines = token_block.lines.into_iter();
    let mut items = Vec::new();
    while let Some(next) = lines.next() {
        items.push(parse_line(module_path, next, &mut lines));
    }
    let items = DiagnosticResult::sequence_unfail(items);
    items.map(|items| {
        let mut data = Vec::new();
        let mut definitions = Vec::new();
        for item in items {
            match item {
                Item::Data(i) => data.push(i),
                Item::Definition(i) => definitions.push(i),
            }
        }
        Module { data, definitions }
    })
}

fn parse_line(
    module_path: &ModulePath,
    line: TokenLine,
    lines: &mut impl Iterator<Item = TokenLine>,
) -> DiagnosticResult<Item> {
    match line {
        TokenLine::Block(block) => DiagnosticResult::fail(ErrorMessage::new(
            String::from("unexpected indented block"),
            Severity::Error,
            Diagnostic::at(module_path.clone(), block.range()),
        )),
        TokenLine::Line(line) => {
            let mut line = line.into_iter().peekable();
            let first_token = line.next().unwrap();
            let first_token_range = first_token.range();
            match first_token {
                TokenTree::Token(token) => match token.token_type {
                    TokenType::Data => {
                        parse_data(module_path, line, lines, token.range.end).map(Item::Data)
                    }
                    TokenType::Def => parse_def(module_path, line, lines).map(Item::Definition),
                    _ => DiagnosticResult::fail(ErrorMessage::new(
                        String::from("expected `def` or `data`"),
                        Severity::Error,
                        Diagnostic::at(module_path.clone(), token.range),
                    )),
                },
                TokenTree::Tree { .. } => DiagnosticResult::fail(ErrorMessage::new(
                    String::from("expected `def` or `data`"),
                    Severity::Error,
                    Diagnostic::at(module_path.clone(), first_token_range),
                )),
            }
        }
    }
}

/// `data ::= "data" identifier "=" type_ctors "\n" data_block`
fn parse_data<I>(
    module_path: &ModulePath,
    mut line: Peekable<I>,
    lines: &mut impl Iterator<Item = TokenLine>,
    end_of_line: Location,
) -> DiagnosticResult<Data>
where
    I: Iterator<Item = TokenTree>,
{
    match line.next() {
        Some(TokenTree::Token(identifier)) => {
            if let TokenType::Identifier(_) = &identifier.token_type {
                // This is the correct syntax: `def something`
                // We now need an `=` symbol, then a series of type constructors separated by `|` symbols.
                let assign_symbol = parse_token(
                    module_path,
                    &mut line,
                    end_of_line,
                    |token| token.token_type == TokenType::Assign,
                    "expected assign symbol",
                );
                assign_symbol.bind(|_| {
                    let type_ctors = parse_type_ctors(module_path, line, end_of_line);
                    type_ctors.map(|type_ctors| Data {
                        name: identifier,
                        type_ctors,
                    })
                })
            } else {
                DiagnosticResult::fail(ErrorMessage::new(
                    String::from("expected the name of the new data type"),
                    Severity::Error,
                    Diagnostic::at(module_path.clone(), identifier.range),
                ))
            }
        }
        Some(TokenTree::Tree { open, .. }) => DiagnosticResult::fail(ErrorMessage::new_with(
            String::from("expected the name of the new data type"),
            Severity::Error,
            Diagnostic::at(module_path.clone(), open),
            HelpMessage {
                message: String::from("remove this set of brackets"),
                help_type: HelpType::Help,
                diagnostic: Diagnostic::at(module_path.clone(), open),
            },
        )),
        None => DiagnosticResult::fail(ErrorMessage::new(
            String::from("expected the name of the new data type"),
            Severity::Error,
            Diagnostic::at_location(module_path.clone(), end_of_line),
        )),
    }
}

#[derive(Debug)]
pub struct TypeConstructor {
    id: Identifier,
}

/// `type_ctors ::= type_ctor ("|" type_ctors)?`
fn parse_type_ctors<I>(
    module_path: &ModulePath,
    mut line: Peekable<I>,
    end_of_line: Location,
) -> DiagnosticResult<Vec<TypeConstructor>>
where
    I: Iterator<Item = TokenTree>,
{
    parse_type_ctor(module_path, &mut line, end_of_line).bind(|type_ctor| {
        let or_symbol = peek_token(module_path, &mut line, end_of_line, |token| {
            token.token_type == TokenType::TypeOr
        });
        if or_symbol {
            // We have another type to parse.
            // Consume the `|` symbol.
            line.next();
            // We use `unfail` here to try to recover parse errors.
            parse_type_ctors(module_path, line, end_of_line)
                .unfail()
                .map(|type_ctors| match type_ctors {
                    Some(mut type_ctors) => {
                        type_ctors.insert(0, type_ctor);
                        type_ctors
                    }
                    None => {
                        vec![type_ctor]
                    }
                })
        } else {
            // We must be at the end of the line.
            match line.next() {
                Some(tree) => DiagnosticResult::fail(ErrorMessage::new(
                    String::from("expected end of line"),
                    Severity::Error,
                    Diagnostic::at(module_path.clone(), tree.range()),
                )),
                None => DiagnosticResult::ok(vec![type_ctor]),
            }
        }
    })
}

/// `type_ctor ::= identifier`
fn parse_type_ctor<I>(
    module_path: &ModulePath,
    line: &mut Peekable<I>,
    end_of_line: Location,
) -> DiagnosticResult<TypeConstructor>
where
    I: Iterator<Item = TokenTree>,
{
    parse_identifier(module_path, line, end_of_line).map(|id| TypeConstructor { id })
}

fn parse_def(
    module_path: &ModulePath,
    mut line: impl Iterator<Item = TokenTree>,
    lines: &mut impl Iterator<Item = TokenLine>,
) -> DiagnosticResult<Definition> {
    DiagnosticResult::fail(ErrorMessage::new(
        String::from("parsed def block"),
        Severity::Error,
        Diagnostic::at(module_path.clone(), line.next().unwrap().range()),
    ))
}

#[derive(Debug)]
pub struct Identifier {
    name: String,
    range: Range,
}

fn parse_identifier(
    module_path: &ModulePath,
    line: &mut impl Iterator<Item = TokenTree>,
    end_of_line: Location,
) -> DiagnosticResult<Identifier> {
    parse_token(
        module_path,
        line,
        end_of_line,
        |token| matches!(token.token_type, TokenType::Identifier(_)),
        "expected identifier",
    )
    .map(|token| {
        if let TokenType::Identifier(name) = token.token_type {
            Identifier {
                name,
                range: token.range,
            }
        } else {
            panic!("parse_token returned a token that was not an identifier");
        }
    })
}

/// Checks if the next token on the line obeys the given predicate.
fn peek_token<I>(
    module_path: &ModulePath,
    line: &mut Peekable<I>,
    end_of_line: Location,
    predicate: impl FnOnce(&Token) -> bool,
) -> bool
where
    I: Iterator<Item = TokenTree>,
{
    match line.peek() {
        Some(TokenTree::Token(token)) => predicate(&token),
        Some(TokenTree::Tree { .. }) => false,
        None => false,
    }
}

/// Parses a single token matching the given predicate.
fn parse_token(
    module_path: &ModulePath,
    line: &mut impl Iterator<Item = TokenTree>,
    end_of_line: Location,
    predicate: impl FnOnce(&Token) -> bool,
    fail_message: &str,
) -> DiagnosticResult<Token> {
    match line.next() {
        Some(TokenTree::Token(token)) => {
            if predicate(&token) {
                DiagnosticResult::ok(token)
            } else {
                DiagnosticResult::fail(ErrorMessage::new(
                    String::from(fail_message),
                    Severity::Error,
                    Diagnostic::at(module_path.clone(), token.range),
                ))
            }
        }
        Some(TokenTree::Tree { open, .. }) => DiagnosticResult::fail(ErrorMessage::new_with(
            String::from(fail_message),
            Severity::Error,
            Diagnostic::at(module_path.clone(), open),
            HelpMessage {
                message: String::from("remove this set of brackets"),
                help_type: HelpType::Help,
                diagnostic: Diagnostic::at(module_path.clone(), open),
            },
        )),
        None => DiagnosticResult::fail(ErrorMessage::new(
            String::from(fail_message),
            Severity::Error,
            Diagnostic::at_location(module_path.clone(), end_of_line),
        )),
    }
}
