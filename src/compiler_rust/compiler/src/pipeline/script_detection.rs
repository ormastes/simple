//! Script vs module detection utilities.

use simple_parser::ast::Node;

/// Detect whether the module contains script-style statements (non-item code) at the top level.
///
/// These should be interpreted directly rather than lowered through HIR/MIR.
pub fn has_script_statements(items: &[Node]) -> bool {
    use Node::*;
    items.iter().any(|item| {
        matches!(
            item,
            Let(_)
                | Const(_)
                | Static(_)
                | Assignment(_)
                | Return(_)
                | If(_)
                | Match(_)
                | For(_)
                | While(_)
                | Loop(_)
                | Break(_)
                | Continue(_)
                | Context(_)
                | With(_)
                | Expression(_)
        )
    })
}
