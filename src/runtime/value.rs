//! A value is a constant expression, or a thunk to be evaluated.

use std::{cell::RefCell, rc::Rc};

use crate::{
    parser::{type_check::DefinitionCase, QualifiedName},
    ModuleLoader,
};

/// A value is either
/// - data. It has a known type and type constructor. The arguments, if any, are also values.
/// - function. A lambda or a symbol from global scope.
/// - apply. An application of a function. The left hand side must be a function value.
#[derive(Debug, Clone)]
pub enum Value<'ml> {
    Data(Data<'ml>),
    Function(Function<'ml>),
    Apply(Apply<'ml>),
}

/// A ValueRef is a value that may be shared between multiple places. It may be (or contain) a thunk
/// value that is yet to be calculated.
///
/// For example, in `lambda x -> x * x * x`, the value `x` is used three times.
/// These would all be instances of a ValueRef containing the underlying value of `x`.
/// This has the advantage of memoising the value once computed. If any of the three instances of
/// `x` is evaluated or refined somehow, all others will see the change immediately.
///
/// # Panics
/// It is theoretically possible to end up with a deadlock if an expression requires its own value.
/// For example, `let x = x + 1 in x` requires the value of `x` in order to calculate `x`, which
/// would cause the internal cell containing `x`'s value to be aliased. This would cause a panic.
/// However, the language guarantees that the value of a variable is not used within its definition,
/// so this cannot happen in practice.
///
/// It is important to note, however, that functions are not offered the same memoisation treatment.
/// In the expression `foo + foo`, the function `foo` is evaluated twice. However, in `let x = foo in x + x`,
/// the function `foo` is evaluated once in order to calculate the value of `x`. This means that functions
/// are allowed to be recursive, for example the following code is valid.
/// ```notrust
/// def infinite_list :: [Bool]
///     infinite_list = True : infinite_list
/// ```
#[derive(Debug, Clone)]
pub struct ValueRef<'ml>(pub Rc<RefCell<Value<'ml>>>);

impl<'ml> From<Data<'ml>> for Value<'ml> {
    fn from(data: Data<'ml>) -> Self {
        Value::Data(data)
    }
}

impl<'ml> From<Function<'ml>> for Value<'ml> {
    fn from(function: Function<'ml>) -> Self {
        Value::Function(function)
    }
}

impl<'ml> From<Apply<'ml>> for Value<'ml> {
    fn from(apply: Apply<'ml>) -> Self {
        Value::Apply(apply)
    }
}

impl<'ml> From<Value<'ml>> for ValueRef<'ml> {
    fn from(value: Value<'ml>) -> Self {
        ValueRef(Rc::new(RefCell::new(value)))
    }
}

impl<'ml> From<Data<'ml>> for ValueRef<'ml> {
    fn from(data: Data<'ml>) -> Self {
        Value::from(data).into()
    }
}

impl<'ml> From<Function<'ml>> for ValueRef<'ml> {
    fn from(function: Function<'ml>) -> Self {
        Value::from(function).into()
    }
}

impl<'ml> From<Apply<'ml>> for ValueRef<'ml> {
    fn from(apply: Apply<'ml>) -> Self {
        Value::from(apply).into()
    }
}

/// A data value is a possibly partially-evaluated monomorphic value.
/// TODO make the names borrowed?
#[derive(Debug, Clone)]
pub struct Data<'ml> {
    pub data_type_name: QualifiedName,
    pub type_ctor: String,
    pub args: Vec<ValueRef<'ml>>,
}

/// This function need not even have arguments -
/// a polymorphic constant to be determined, for example.
#[derive(Debug, Clone)]
pub struct Function<'ml> {
    pub cases: &'ml Vec<DefinitionCase>,
}

impl<'ml> Function<'ml> {
    pub fn arity(&self) -> usize {
        self.cases[0].arg_patterns.len()
    }

    pub fn from_name(module_loader: &'ml ModuleLoader, name: QualifiedName) -> Option<Self> {
        module_loader
            .definition(&name)
            .map(|def| Self { cases: &def.cases })
    }

    pub fn apply_zero_args(self) -> Apply<'ml> {
        Apply {
            function: self.into(),
            args: Vec::new(),
        }
    }
}

/// An application of a variable to a function.
/// Once the amount of args matches the function arity,
/// the function is invoked.
#[derive(Debug, Clone)]
pub struct Apply<'ml> {
    pub function: ValueRef<'ml>,
    pub args: Vec<ValueRef<'ml>>,
}
