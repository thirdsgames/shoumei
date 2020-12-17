use crate::{Diagnostic, DiagnosticResult, ErrorMessage, Severity};

use super::{lexer::LeadingWhitespace, lexer::Token, ModulePath, Range};

/// A token block represents an indented block of content, or indeed the whole file.
#[derive(Debug, Default)]
pub struct TokenBlock {
    pub lines: Vec<TokenLine>,
}

impl TokenBlock {
    pub fn range(&self) -> Range {
        // It is a logic error to have a token block with zero lines.
        // Also it is a logic error to have a token line with zero trees.
        // Therefore, it is perfectly sound to unwrap the first/last line/tree etc in the `range` methods.
        self.lines
            .first()
            .unwrap()
            .range()
            .union(self.lines.last().unwrap().range())
    }
}

/// A block may contain multiple `TokenLine`s.
/// These lines may be single lines or entire sub-blocks contained within the parent block.
#[derive(Debug)]
pub enum TokenLine {
    Block(TokenBlock),
    Line(Vec<TokenTree>),
}

impl TokenLine {
    pub fn range(&self) -> Range {
        match self {
            TokenLine::Block(block) => block.range(),
            TokenLine::Line(line) => line
                .first()
                .unwrap()
                .range()
                .union(line.last().unwrap().range()),
        }
    }
}

/// A line is subdivided into token trees, which are essentially bracketed groups.
/// For example, in the expression `1 + (2 + 3) + 4`, the token trees are `[1, +, [2, +, 3], +, 4]`.
#[derive(Debug)]
pub enum TokenTree {
    Token(Token),
    Tree {
        /// The range representing the open bracket.
        open: Range,
        /// The range representing the close bracket.
        close: Range,
        /// The actual tokens inside this tree node.
        tokens: Vec<TokenTree>,
        /// What kind of brackets does this token tree represent?
        bracket_type: BracketType,
    },
}

#[derive(Debug)]
pub enum BracketType {
    Parentheses,
    Square,
    Brace,
}

impl TokenTree {
    pub fn range(&self) -> Range {
        match self {
            TokenTree::Token(token) => token.range,
            TokenTree::Tree { open, close, .. } => open.union(*close),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IndentLevel {
    amount: u32,
    indent: LeadingWhitespace,
}

impl IndentLevel {
    pub fn is_indented(&self) -> bool {
        self.amount != 0
    }
}

/// Processes leading whitespace to convert a list of lines to a sequence of logical blocks.
pub fn process_indent(
    module_path: &ModulePath,
    tokens: Vec<(LeadingWhitespace, Vec<Token>)>,
) -> DiagnosticResult<TokenBlock> {
    match tokens.first() {
        Some((whitespace, _)) => {
            if whitespace.string != *"" {
                return DiagnosticResult::fail(ErrorMessage::new(
                    String::from("first line of file should not be indented"),
                    Severity::Error,
                    Diagnostic::at(module_path.clone(), whitespace.range),
                ));
            }
        }
        None => {
            // File was empty.
            return DiagnosticResult::ok(TokenBlock::default());
        }
    }

    // A list of all indent levels and blocks, e.g. [(0, _), (4, _), (8, _), (12, _)]
    // if we're in a space-indented file inside three nested blocks, along with the entire file as the first block.
    let mut blocks: Vec<(u32, TokenBlock)> = Vec::new();
    // A block to represent the whole file.
    blocks.push((0, TokenBlock::default()));
    for (indent, line) in tokens {
        if line.is_empty() {
            continue;
        }

        let indent_level = if indent.string.chars().all(|ch| ch == ' ') {
            IndentLevel {
                amount: indent.string.chars().count() as u32,
                indent,
            }
        } else if indent.string.chars().all(|ch| ch == '\t') {
            return DiagnosticResult::fail(ErrorMessage::new(
                String::from("expected indent to be in spaces instead of tabs"),
                Severity::Error,
                Diagnostic::at(module_path.clone(), indent.range),
            ));
        } else {
            return DiagnosticResult::fail(ErrorMessage::new(
                String::from("inconsistent use of tabs and spaces on this line"),
                Severity::Error,
                Diagnostic::at(module_path.clone(), indent.range),
            ));
        };

        // Check if the indent level matches anything in the list of block indents.
        let mut exited_block = false;
        loop {
            let (block_indent, block) = blocks.last_mut().expect("no parent block found");
            match indent_level.amount.cmp(block_indent) {
                std::cmp::Ordering::Less => {
                    // We've exited this block.
                    exited_block = true;
                    let (_, block) = blocks.pop().unwrap();
                    match blocks.last_mut() {
                        Some((_, parent_block)) => {
                            // We'll place this completed block inside the parent block.
                            parent_block.lines.push(TokenLine::Block(block));
                        }
                        None => {
                            // There must always be a parent block!
                            panic!("no parent block found");
                        }
                    }
                }
                std::cmp::Ordering::Equal => {
                    block.lines.push(TokenLine::Line(
                        line.into_iter().map(TokenTree::Token).collect(),
                    ));
                    break;
                }
                std::cmp::Ordering::Greater => {
                    // We've just entered a new indented block.
                    if exited_block {
                        // We've exited and entered a block on the same line.
                        // This is invalid - realistically this means that we've indented by the wrong amount!
                        return DiagnosticResult::fail(ErrorMessage::new(
                            String::from("indented by the wrong amount"),
                            Severity::Error,
                            Diagnostic::at(module_path.clone(), indent_level.indent.range),
                        ));
                    }
                    blocks.push((
                        indent_level.amount,
                        TokenBlock {
                            lines: vec![TokenLine::Line(
                                line.into_iter().map(TokenTree::Token).collect(),
                            )],
                        },
                    ));
                    break;
                }
            }
        }
    }

    // Now that we've parsed all lines, we need to close any blocks that were not explicitly closed by having more data on a less-indented level.
    while blocks.len() > 1 {
        let (_, block) = blocks.pop().unwrap();
        let (_, parent_block) = blocks.last_mut().unwrap();
        parent_block.lines.push(TokenLine::Block(block));
    }

    let (_, file) = blocks.pop().unwrap();

    DiagnosticResult::ok(file)
}
