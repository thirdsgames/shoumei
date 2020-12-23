use std::collections::HashMap;

use crate::DiagnosticResult;

use super::{
    index::ProjectIndex,
    type_check::{
        BoundVariable, Constraint, Constraints, Expression, ExpressionContents, ExpressionT,
    },
    type_resolve::Type,
    Location, ModulePath, QualifiedName,
};

/// Deduces the type of an expression.
/// Any error messages are added to the diagnostic result.
///
/// This mostly implements the algorithm from Generalizing Hindley-Milner Type Inference Algorithms (2002)
/// <https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.18.9348>.
pub fn deduce_expr_type(
    module_path: &ModulePath,
    project_index: &ProjectIndex,
    args: &HashMap<String, BoundVariable>,
    expected_type: Type,
    expr: ExpressionT,
    constraints: Constraints,
) -> DiagnosticResult<Expression> {
    println!("Deducing type of {:#?}", expr);
    println!("Constraints: {:#?}", constraints);
    // We implement the Bottom-Up rules from the above paper.
    DiagnosticResult::ok(Expression {
        ty: expected_type,
        contents: ExpressionContents::Symbol(QualifiedName {
            module_path: ModulePath(vec!["test".into()]),
            name: "test".into(),
            range: Location { line: 0, col: 0 }.into(),
        }),
    })
}
