//! The interpreter module contains all of the different parse steps used to compile a `.shoumei` module.
//!
//! The compilation passes are (in order of execution):
//! - lexer
//! - indent
//! - brackets
//! - parser
//! - symbols
//!
//! As a general rule, each compilation pass may only use types declared in previous passes.
//!
//! Types may have certain suffixes to declare what information they have:
//! - `P`: just been parsed, no extra information has been deduced.
//!   No type has been deduced, and no effort has been made to ensure syntactic correctness
//!   past the (lenient) parser.
//! - (no suffix): types have been deduced and references have been resolved.
//!
//! Using type name suffixes as a form of type state helps to ensure that compiler phases can never leak bad
//! information between each other, ensuring (for example) that after a type check phase, all expressions
//! actually have a type.

use std::{fmt::Display, path::PathBuf};

pub mod brackets;
pub mod indent;
pub mod lexer;
pub mod parser;
pub mod symbols;

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
