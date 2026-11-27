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

/// Attribute `wrap_entry_script_as_main` puts on the `main` it synthesizes
/// from a script's top-level statements, so HIR lowering can tell a script
/// unit (where `any` is permitted) from a compiled module.
pub const SCRIPT_ENTRY_ATTR: &str = "__script_entry";
