use std::collections::HashMap;

use crate::DiagnosticResult;

use super::{ModulePath, index::ProjectIndex, type_check::{BoundVariable, Expression}, type_resolve::Type};

/// Deduces the type of an expression.
/// Any error messages are added to the diagnostic result.
///
/// This mostly implements the algorithm from Generalizing Hindley-Milner Type Inference Algorithms (2002)
/// <https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.18.9348>.
pub fn deduce_expr_type(
    module_path: &ModulePath,
    project_index: &ProjectIndex,
    bound_variables: &HashMap<String, BoundVariable>,
    expected_type: Type,
    expr: &mut Expression,
) -> DiagnosticResult<()> {
    DiagnosticResult::ok(())
}
