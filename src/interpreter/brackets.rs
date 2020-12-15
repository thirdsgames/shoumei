use crate::{
    Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, ModulePath, Range, Severity,
};

use super::{TokenBlock, TokenLine, TokenTree, TokenType};

/// Processes bracket pairs to remove explicit bracket characters in return for structural representation of operation order.
/// This uses `TokenTree`s to represent the structure.
pub fn process_brackets(
    module_path: &ModulePath,
    block: TokenBlock,
) -> DiagnosticResult<TokenBlock> {
    let new_lines = block
        .lines
        .into_iter()
        .map(|line| process_brackets_line(module_path, line))
        .collect::<DiagnosticResult<_>>();
    new_lines.map(|lines| TokenBlock { lines })
}

fn process_brackets_line(module_path: &ModulePath, line: TokenLine) -> DiagnosticResult<TokenLine> {
    match line {
        TokenLine::Block(block) => process_brackets(module_path, block).map(TokenLine::Block),
        TokenLine::Line(line) => {
            if line.is_empty() {
                panic!("line was unexpectedly empty");
            }

            // This is a list of all open-bracket tokens (specifically just their ranges, that's all that's important)
            // and the token trees that that bracket pair contains.
            let mut brackets: Vec<(Range, Vec<TokenTree>)> = Vec::new();
            // Add a dummy 'open bracket' representing the entire line.
            brackets.push((match line.first().unwrap() {
                TokenTree::Token(token) => {
                    // The fake open bracket will start at the first token on the line, and will span for one character.
                    token.range.start.into()
                }
                TokenTree::Tree(_) => { panic!("unexpected token tree node, the indent step is not supposed to create token trees"); }
            }, Vec::new()));

            let end_of_line = match line.last().unwrap() {
                TokenTree::Token(token) => token.range.end.into(),
                TokenTree::Tree(_) => {
                    panic!("unexpected token tree node, the indent step is not supposed to create token trees");
                }
            };

            for token in line {
                match token {
                    TokenTree::Token(token) => {
                        match &token.token_type {
                            TokenType::LeftParenthesis => {
                                // Add a new bracket pair to the list.
                                brackets.push((token.range, Vec::new()));
                            }
                            TokenType::RightParenthesis => {
                                // Terminate the current bracket pair.
                                let tree = brackets.pop().unwrap().1;
                                match brackets.last_mut() {
                                    Some((_, parent_bracket_tree)) => {
                                        parent_bracket_tree.push(TokenTree::Tree(tree));
                                    }
                                    None => {
                                        return DiagnosticResult::fail(ErrorMessage::new(
                                            String::from("too many closing brackets"),
                                            Severity::Error,
                                            Diagnostic::at(module_path.clone(), token.range),
                                        ));
                                    }
                                }
                            }
                            _ => {
                                // Add the token to the current bracket.
                                brackets.last_mut().unwrap().1.push(TokenTree::Token(token));
                            }
                        }
                    }
                    TokenTree::Tree(_) => {
                        panic!("unexpected token tree node, the indent step is not supposed to create token trees");
                    }
                }
            }

            match brackets.len() {
                1 => {
                    let (_, tree) = brackets.pop().unwrap();
                    DiagnosticResult::ok(TokenLine::Line(tree))
                }
                _ => DiagnosticResult::fail(ErrorMessage::new_with(
                    String::from("not enough closing brackets"),
                    Severity::Error,
                    Diagnostic::at(module_path.clone(), end_of_line),
                    HelpMessage {
                        message: String::from("this bracket was not closed"),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(module_path.clone(), brackets.pop().unwrap().0),
                    },
                )),
            }
        }
    }
}
