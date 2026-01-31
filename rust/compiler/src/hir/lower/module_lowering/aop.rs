use simple_parser as ast;

use crate::hir::lower::lowerer::Lowerer;

impl Lowerer {
    /// Convert a PredicateExpr AST node back to its string representation.
    /// This preserves the predicate text for later evaluation by the weaving engine.
    ///
    /// Note: The AST parser uses a placeholder that stores the entire predicate string
    /// in the selector name field (with empty args). We detect this and return the
    /// name as-is, rather than adding extra parentheses.
    pub(super) fn predicate_to_string(&self, pred: &ast::PredicateExpr) -> String {
        match &pred.kind {
            ast::PredicateKind::Selector { name, args } => {
                if args.is_empty() {
                    // Check if this is a placeholder from the AST parser
                    // (entire predicate stored in name, like "import(*, crate.test.*)")
                    // If the name already contains parentheses, it's the full predicate
                    if name.contains('(') && name.contains(')') {
                        name.clone()
                    } else {
                        // Otherwise it's a simple selector without args
                        format!("{}()", name)
                    }
                } else {
                    format!("{}({})", name, args.join(", "))
                }
            }
            ast::PredicateKind::Not(inner) => {
                format!("!{}", self.predicate_to_string(inner))
            }
            ast::PredicateKind::And(left, right) => {
                format!(
                    "({} & {})",
                    self.predicate_to_string(left),
                    self.predicate_to_string(right)
                )
            }
            ast::PredicateKind::Or(left, right) => {
                format!(
                    "({} | {})",
                    self.predicate_to_string(left),
                    self.predicate_to_string(right)
                )
            }
        }
    }
}
