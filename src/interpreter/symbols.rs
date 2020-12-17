//! Index all of the symbols in a module.
//! Specifically, we keep track of all `data` and `def` statements in this phase.
//! However, this module does not validate the contents of `def` blocks to check that their types match and patterns are exhaustive,
//! that is kept to a later type checking phase.


