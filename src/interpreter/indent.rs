use crate::{
    Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, Location, ModulePath, Range, Severity,
};

use super::{LeadingWhitespace, Token};

/// A token tree represents the overall structure of the program.
/// Any program is divisible into such blocks. Indented blocks and bracketed blocks
/// create sub-trees.
#[derive(Debug)]
pub enum TokenTree {
    Token(Token),
    /// Represents an indented block (or indeed, the whole program).
    Block(Vec<TokenTree>),
    /// Represents a parenthesised block.
    Bracket(Vec<TokenTree>),
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
) -> DiagnosticResult<Vec<TokenTree>> {
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
            return DiagnosticResult::ok(Vec::new());
        }
    }

    // A list of all indent levels and blocks, e.g. [(0, _), (4, _), (8, _), (12, _)]
    // if we're in a space-indented file inside three nested blocks, along with the entire file as the first block.
    let mut blocks: Vec<(u32, Vec<TokenTree>)> = Vec::new();
    // A block to represent the whole file.
    blocks.push((0, Vec::new()));
    for (indent, mut line) in tokens {
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
                            parent_block.push(TokenTree::Block(block));
                        }
                        None => {
                            // There must always be a parent block!
                            panic!("no parent block found");
                        }
                    }
                }
                std::cmp::Ordering::Equal => {
                    block.extend(line.drain(..).map(TokenTree::Token));
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
                            Diagnostic::at(module_path.clone(), indent_level.indent.range)
                        ));
                    }
                    blocks.push((
                        indent_level.amount,
                        line.drain(..)
                            .map(TokenTree::Token)
                            .collect(),
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
        parent_block.push(TokenTree::Block(block));
    }

    let (_, file) = blocks.pop().unwrap();

    DiagnosticResult::ok(file)
}
