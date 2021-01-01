//! A value is a constant expression, or a thunk to be evaluated.

use crate::parser::QualifiedName;

pub enum Value {
    Data(Data),
    Thunk(Thunk),
}

/// A data constant is a fully-evaluated monomorphic value.
/// It is by definition finitely expressible, since it exists in memory.
pub struct Data {
    data_type_name: QualifiedName,
    type_ctor: String,
    args: Vec<Data>,
}

/// A thunk is an invocation of a function.
/// This function need not even have arguments - a thunk may represent a
/// polymorphic constant to be determined, for example.
pub struct Thunk {
    function: QualifiedName,
    args: Vec<Value>,
}
