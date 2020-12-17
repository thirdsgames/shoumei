//! Indexes all of the symbols in a module, specifically, all `data` and `def` statements.
//!
//! This module does not validate the contents of `def` blocks to check that their types match and patterns are exhaustive,
//! that is kept to a later type checking phase.
