//! Regression: the JIT flattens imports into one unit, so unrelated modules can
//! declare a trait, a class and structs with the same bare name (`Pointcut`).
//! `self` inside a method of one of them must resolve to that type's own
//! declaration, not to whichever same-named declaration registered last.
//! These pin only that lowering succeeds: the ANY-receiver fallback in
//! type_resolver.rs can still find a uniquely named field, so a self that
//! resolved to ANY would also pass. They are not evidence against the open bug.
use super::parse_and_lower;

const CORE_STRUCT: &str = "enum PointcutKind:\n    NamePattern\n    All\n\nstruct Pointcut:\n    kind: PointcutKind\n    pattern: text\n\nimpl Pointcut:\n    fn matches_name(fn_name: text) -> bool:\n        if self.kind == PointcutKind.All:\n            return true\n        self.pattern == fn_name\n\n";
const SIBLING_TRAIT: &str = "trait Pointcut:\n    fn compile() -> text\n\n";
const SIBLING_CLASS: &str = "class Pointcut:\n    expr: text\n    matched: [text]\n\n";
const SIBLING_STRUCT: &str = "struct Pointcut:\n    label: text\n    weight: i64\n\n";

fn lowers(src: &str) {
    let module = parse_and_lower(src).unwrap_or_else(|e| panic!("lowering failed: {e:?}\n{src}"));
    assert!(module.functions.iter().any(|f| f.name == "Pointcut.matches_name"));
}

#[test]
fn lowering_succeeds_when_same_named_trait_follows() {
    lowers(&format!("{CORE_STRUCT}{SIBLING_TRAIT}"));
}

#[test]
fn lowering_succeeds_when_same_named_class_follows() {
    lowers(&format!("{CORE_STRUCT}{SIBLING_CLASS}"));
}

#[test]
fn lowering_succeeds_when_same_named_struct_follows() {
    lowers(&format!("{CORE_STRUCT}{SIBLING_STRUCT}"));
}

#[test]
fn lowering_succeeds_with_trait_class_and_struct_all_coexisting() {
    lowers(&format!("{SIBLING_TRAIT}{SIBLING_CLASS}{CORE_STRUCT}{SIBLING_STRUCT}"));
}
