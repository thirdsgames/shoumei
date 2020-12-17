use std::iter::Peekable;

use crate::{
    Diagnostic, DiagnosticResult, ErrorMessage,
    HelpMessage, HelpType, Module, Severity,
};

use super::{Location, ModulePath, Range, indent::TokenBlock, indent::TokenLine, indent::TokenTree, lexer::Token, lexer::TokenType};

/// Any top level item such as a definition or theorem.
#[derive(Debug)]
enum Item {
    Data(Data),
    Definition(Definition),
}

#[derive(Debug)]
pub enum Type {
    /// An explicitly named type without type parameters, e.g. `Bool`.
    Named(Identifier),
    /// A function `a -> b`.
    /// Functions with more arguments, e.g. `a -> b -> c` are represented as
    /// curried functions, e.g. `a -> (b -> c)`.
    Function(Box<Type>, Box<Type>),
}

impl Type {
    pub fn range(&self) -> Range {
        match self {
            Type::Named(ident) => ident.range,
            Type::Function(left, right) => left.range().union(right.range()),
        }
    }
}

#[derive(Debug)]
pub struct Identifier {
    pub name: String,
    pub range: Range,
}

/// A `data` block, used to define sum or product types.
#[derive(Debug)]
pub struct Data {
    pub identifier: Identifier,
    pub type_ctors: Vec<TypeConstructor>,
}

#[derive(Debug)]
pub struct TypeConstructor {
    pub id: Identifier,
}

/// A `def` block. Defines a symbol's type and what values it takes under what circumstances.
#[derive(Debug)]
pub struct Definition {
    pub identifier: Identifier,
    pub symbol_type: Type,
    pub cases: Vec<DefinitionCase>,
}

/// Represents a case in a definition where we can replace the left hand side of a pattern with the right hand side.
#[derive(Debug)]
pub struct DefinitionCase {
    pub pattern: Expression,
    pub replacement: Expression,
}

#[derive(Debug)]
pub enum Expression {
    /// A named variable e.g. `x` or `+`.
    Variable(Identifier),
    /// Apply the left hand side to the right hand side, e.g. `a b`.
    /// More complicated expressions e.g. `a b c d` can be desugared into `((a b) c) d`.
    Apply(Box<Expression>, Box<Expression>),
    /// An underscore `_` representing an unknown.
    Unknown(Range),
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
            let end_of_line = line.last().unwrap().range().end;
            let mut line = line.into_iter().peekable();
            let first_token = line.next().unwrap();
            let first_token_range = first_token.range();
            match first_token {
                TokenTree::Token(token) => match token.token_type {
                    TokenType::Data => parse_data(module_path, line, end_of_line).map(Item::Data),
                    TokenType::Def => {
                        parse_def(module_path, line, lines, end_of_line).map(Item::Definition)
                    }
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

/// `data ::= identifier "=" type_ctors`
fn parse_data<I>(
    module_path: &ModulePath,
    mut line: Peekable<I>,
    end_of_line: Location,
) -> DiagnosticResult<Data>
where
    I: Iterator<Item = TokenTree>,
{
    parse_identifier(module_path, &mut line, end_of_line).bind(|identifier| {
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
                identifier,
                type_ctors,
            })
        })
    })
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
        let or_symbol = peek_token(&mut line, |token| {
            matches!(token.token_type, TokenType::TypeOr)
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
            assert_end_of_line(module_path, line).map(|_| vec![type_ctor])
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

/// `def ::= identifier ":" type "\n" def_cases`
fn parse_def<I>(
    module_path: &ModulePath,
    mut line: Peekable<I>,
    lines: &mut impl Iterator<Item = TokenLine>,
    end_of_line: Location,
) -> DiagnosticResult<Definition>
where
    I: Iterator<Item = TokenTree>,
{
    parse_identifier(module_path, &mut line, end_of_line)
        .bind(|identifier| {
            parse_token(
                module_path,
                &mut line,
                end_of_line,
                |token| matches!(token.token_type, TokenType::Type),
                "expected type symbol",
            )
            .bind(|_| parse_type(module_path, &mut line, end_of_line))
            .bind(|symbol_type| {
                assert_end_of_line(module_path, line).map(|_| Definition {
                    identifier,
                    symbol_type,
                    cases: Vec::new(),
                })
            })
        })
        .bind(|mut definition| {
            // Now that we've parsed the first line, we can iterate over all lines in the subsequent block.
            // These are the definition cases.
            match lines.next() {
                Some(TokenLine::Block(block)) => {
                    // Parse each line in the block.
                    parse_def_cases(module_path, block).map(|mut cases| {
                        definition.cases.append(&mut cases);
                        definition
                    })
                }
                Some(TokenLine::Line(line)) => DiagnosticResult::ok_with(
                    definition,
                    ErrorMessage::new(
                        String::from("expected indented block"),
                        Severity::Error,
                        Diagnostic::at(module_path.clone(), line.first().unwrap().range()),
                    ),
                ),
                None => DiagnosticResult::ok_with(
                    definition,
                    ErrorMessage::new(
                        String::from("expected indented block"),
                        Severity::Error,
                        Diagnostic::at_location(module_path.clone(), end_of_line),
                    ),
                ),
            }
        })
}

/// `def_cases ::= (def_case)+`
fn parse_def_cases(
    module_path: &ModulePath,
    token_block: TokenBlock,
) -> DiagnosticResult<Vec<DefinitionCase>> {
    token_block
        .lines
        .into_iter()
        .map(|line| parse_def_case(module_path, line))
        .collect()
}

/// `def_case ::= expr "=" expr`
/// The left expression is a pattern expression, and the right hand side is an actual expression.
fn parse_def_case(module_path: &ModulePath, line: TokenLine) -> DiagnosticResult<DefinitionCase> {
    match line {
        TokenLine::Block(block) => DiagnosticResult::fail(ErrorMessage::new(
            String::from("expected a definition case, got an indented block"),
            Severity::Error,
            Diagnostic::at(module_path.clone(), block.range()),
        )),
        TokenLine::Line(line) => {
            let end_of_line = line.last().unwrap().range().end;
            let mut line = line.into_iter().peekable();
            parse_expr(module_path, &mut line, end_of_line).bind(|lhs| {
                parse_token(
                    module_path,
                    &mut line,
                    end_of_line,
                    |token| matches!(token.token_type, TokenType::Assign),
                    "expected assign symbol",
                )
                .bind(|_| {
                    parse_expr(module_path, &mut line, end_of_line).bind(|rhs| {
                        assert_end_of_line(module_path, line).map(|_| DefinitionCase {
                            pattern: lhs,
                            replacement: rhs,
                        })
                    })
                })
            })
        }
    }
}

/// Expressions may contain `_` tokens, which represent data that we don't care about.
/// We will evaluate patterns and normal expressions differently in a later parse step.
fn parse_expr<I>(
    module_path: &ModulePath,
    line: &mut Peekable<I>,
    end_of_line: Location,
) -> DiagnosticResult<Expression>
where
    I: Iterator<Item = TokenTree>,
{
    let mut terms = Vec::new();
    while let Some(next_term) = parse_expr_term(module_path, line) {
        terms.push(next_term);
    }

    if terms.is_empty() {
        let start_location = line
            .peek()
            .map(|token| token.range().start)
            .unwrap_or(end_of_line);
        return DiagnosticResult::fail(ErrorMessage::new(
            String::from("expected expression"),
            Severity::Error,
            Diagnostic::at_location(module_path.clone(), start_location),
        ));
    }

    DiagnosticResult::sequence(terms).map(|terms| {
        let mut terms = terms.into_iter();
        let first = terms.next().unwrap();
        terms.into_iter().fold(first, |acc, i| {
            Expression::Apply(Box::new(acc), Box::new(i))
        })
    })
}

/// Parses a single term from an expression by consuming either zero or one token trees from the input.
/// If the following token did not constitute an expression, nothing is consumed.
fn parse_expr_term<I>(
    module_path: &ModulePath,
    line: &mut Peekable<I>,
) -> Option<DiagnosticResult<Expression>>
where
    I: Iterator<Item = TokenTree>,
{
    match line.peek() {
        Some(TokenTree::Tree { .. }) => {
            if let Some(TokenTree::Tree { tokens, .. }) = line.next() {
                let end_of_tree = tokens.last().unwrap().range().end;
                let mut tree_contents = tokens.into_iter().peekable();
                let result = parse_expr(module_path, &mut tree_contents, end_of_tree);
                Some(
                    result.bind(|result| {
                        assert_end_of_tree(module_path, tree_contents).map(|_| result)
                    }),
                )
            } else {
                panic!("line.next() != *line.peek()");
            }
        }
        Some(TokenTree::Token(token)) => match &token.token_type {
            TokenType::Identifier(_) => {
                if let Some(TokenTree::Token(token)) = line.next() {
                    if let TokenType::Identifier(name) = token.token_type {
                        Some(DiagnosticResult::ok(Expression::Variable(Identifier {
                            name,
                            range: token.range,
                        })))
                    } else {
                        panic!("line.next() != *line.peek()");
                    }
                } else {
                    panic!("line.next() != *line.peek()");
                }
            }
            TokenType::Underscore => {
                let token_range = token.range;
                line.next();
                Some(DiagnosticResult::ok(Expression::Unknown(token_range)))
            }
            _ => None,
        },
        None => None,
    }
}

/// `type ::= type_name ("->" type)?`
#[rustfmt::skip] // rustfmt messes up the `matches!` invocation, and makes it so clippy raises a warning
fn parse_type<I>(
    module_path: &ModulePath,
    line: &mut Peekable<I>,
    end_of_line: Location,
) -> DiagnosticResult<Type>
where
    I: Iterator<Item = TokenTree>,
{
    parse_identifier_with_message(module_path, line, end_of_line, "expected type name").bind(
        |type_name| {
            let parsed_type = Type::Named(type_name);
            if peek_token(line, |token| matches!(token.token_type, TokenType::Arrow)) {
                // Consume the `->` token.
                line.next();
                parse_type(module_path, line, end_of_line)
                    .map(|rhs_type| Type::Function(Box::new(parsed_type), Box::new(rhs_type)))
            } else {
                DiagnosticResult::ok(parsed_type)
            }
        },
    )
}

fn parse_identifier(
    module_path: &ModulePath,
    line: &mut impl Iterator<Item = TokenTree>,
    end_of_line: Location,
) -> DiagnosticResult<Identifier> {
    parse_identifier_with_message(module_path, line, end_of_line, "expected identifier")
}

fn parse_identifier_with_message(
    module_path: &ModulePath,
    line: &mut impl Iterator<Item = TokenTree>,
    end_of_line: Location,
    fail_message: &str,
) -> DiagnosticResult<Identifier> {
    parse_token(
        module_path,
        line,
        end_of_line,
        |token| matches!(token.token_type, TokenType::Identifier(_)),
        fail_message,
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

/// Asserts that we are at the end of the line.
fn assert_end_of_line(
    module_path: &ModulePath,
    mut line: impl Iterator<Item = TokenTree>,
) -> DiagnosticResult<()> {
    if let Some(token) = line.next() {
        DiagnosticResult::ok_with(
            (),
            ErrorMessage::new(
                String::from("expected end of line"),
                Severity::Error,
                Diagnostic::at(module_path.clone(), token.range()),
            ),
        )
    } else {
        DiagnosticResult::ok(())
    }
}

/// Asserts that we are at the end of the current tree.
fn assert_end_of_tree(
    module_path: &ModulePath,
    mut line: impl Iterator<Item = TokenTree>,
) -> DiagnosticResult<()> {
    if let Some(token) = line.next() {
        DiagnosticResult::ok_with(
            (),
            ErrorMessage::new(
                String::from("expected closing bracket"),
                Severity::Error,
                Diagnostic::at(module_path.clone(), token.range()),
            ),
        )
    } else {
        DiagnosticResult::ok(())
    }
}

/// Checks if the next token on the line obeys the given predicate.
fn peek_token<I>(line: &mut Peekable<I>, predicate: impl FnOnce(&Token) -> bool) -> bool
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
