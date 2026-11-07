//! Duplicate `impl` method detection shared by the interpreter and the HIR/JIT
//! lowering (bug: compiler_interpreter_integration_real_gaps_found_2026-09-06,
//! gap 1). Two `impl T:` blocks that both define the same method with the same
//! signature used to compile and run silently, the call binding to whichever
//! definition registered last.

use std::collections::HashSet;

use simple_parser::ast::{FunctionDef, Node};

fn signature_key(owner: &str, trait_name: &Option<String>, m: &FunctionDef) -> String {
    let params: Vec<String> = m.params.iter().map(|p| format!("{:?}", p.ty)).collect();
    format!("{owner}|{trait_name:?}|{}|{}|{}", m.name, m.is_static, params.join(","))
}

/// First duplicate method among the `impl` blocks of `items`, rendered as a
/// diagnostic. Methods carrying attributes (`@cfg(..)` variants, drivers) are
/// exempt: they can legitimately coexist under mutually exclusive conditions.
/// Blanket (`#[default]` generic) impls are exempt too.
pub fn find_duplicate_impl_method(items: &[Node]) -> Option<String> {
    let mut seen: HashSet<String> = HashSet::new();
    for item in items {
        let Node::Impl(block) = item else { continue };
        let is_blanket = !block.generic_params.is_empty() && block.attributes.iter().any(|a| a.name == "default");
        if is_blanket {
            continue;
        }
        let owner = format!("{:?}", block.target_type);
        for m in &block.methods {
            if !m.attributes.is_empty() {
                continue;
            }
            if !seen.insert(signature_key(&owner, &block.trait_name, m)) {
                return Some(format!(
                    "duplicate method `{}` in `impl` blocks of the same type (the same signature is defined twice)",
                    m.name
                ));
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::let_literal_mismatch;
    use super::find_duplicate_impl_method;
    use simple_parser::Parser;

    fn check(src: &str) -> Option<String> {
        let parsed = Parser::new(src).parse().expect("fixture");
        find_duplicate_impl_method(&parsed.items)
    }

    #[test]
    fn same_signature_in_two_impl_blocks_is_reported() {
        let src = "class Box:\n    v: i64\nimpl Box:\n    fn get() -> i64:\n        self.v\nimpl Box:\n    fn get() -> i64:\n        self.v + 1\n";
        assert!(check(src).unwrap().contains("`get`"));
    }

    #[test]
    fn different_methods_and_types_are_not_duplicates() {
        let src = "class A:\n    v: i64\nclass B:\n    v: i64\nimpl A:\n    fn get() -> i64:\n        1\nimpl B:\n    fn get() -> i64:\n        2\nimpl A:\n    fn other() -> i64:\n        3\n";
        assert!(check(src).is_none());
    }

    fn let_of(src: &str) -> Option<String> {
        let parsed = Parser::new(src).parse().expect("fixture");
        for item in &parsed.items {
            if let simple_parser::ast::Node::Let(l) = item {
                return let_literal_mismatch(l);
            }
        }
        None
    }

    #[test]
    fn text_literal_for_numeric_binding_is_a_mismatch() {
        assert!(let_of("val x: i64 = \"not a number\"
").unwrap().contains("i64"));
        assert!(let_of("val x: i64 = 5
").is_none());
        assert!(let_of("val s: text = \"ok\"
").is_none());
    }

    #[test]
    fn differently_typed_overloads_are_not_duplicates() {
        let src = "class A:\n    v: i64\nimpl A:\n    fn put(x: i64) -> i64:\n        x\nimpl A:\n    fn put(x: text) -> i64:\n        1\n";
        assert!(check(src).is_none());
    }
}

/// Static check shared by the interpreter and the HIR/JIT lowering (bug:
/// compiler_interpreter_integration_real_gaps_found_2026-09-06, gap 2):
/// a string literal initializer for a numeric or `bool` annotated binding
/// (`val x: i64 = "s"`) is a type error, not a value to be coerced.
pub fn let_literal_mismatch(let_stmt: &simple_parser::ast::LetStmt) -> Option<String> {
    use simple_parser::ast::{Expr, Pattern, Type};
    let declared = match (&let_stmt.ty, &let_stmt.pattern) {
        (Some(ty), _) => ty,
        (None, Pattern::Typed { ty, .. }) => ty,
        _ => return None,
    };
    let Type::Simple(name) = declared else { return None };
    let numeric_or_bool = matches!(
        name.as_str(),
        "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "f32" | "f64" | "bool"
    );
    match let_stmt.value.as_ref()? {
        Expr::String(_) | Expr::FString { .. } | Expr::TypedString(..) if numeric_or_bool => Some(format!(
            "type mismatch: cannot initialize `{name}` binding with a text literal"
        )),
        _ => None,
    }
}
