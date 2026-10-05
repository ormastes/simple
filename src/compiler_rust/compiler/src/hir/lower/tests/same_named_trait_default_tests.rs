//! Regression: the JIT flattens imports into one namespace, so unrelated
//! traits can share a name (`RenderBackend` exists in three stdlib modules).
//! Impl default-method materialisation must use the same-named trait the impl
//! actually implements, not the first one in the flattened item list.
use super::parse_and_lower;
use crate::hir::types::TypeId;

const UNRELATED_FIRST: &str = "trait Backend:\n    fn name() -> text\n\nclass Other:\n    var n: i64\n\nimpl Backend for Other:\n    fn name() -> text:\n        \"other\"\n\n";
const REAL_TRAIT: &str = "trait Backend:\n    fn read() -> i64\n    me read_twice() -> i64:\n        self.read() * 2\n\n";
const VK_IMPL: &str = "class Vk:\n    var v: i64\n\nimpl Backend for Vk:\n    fn read() -> i64:\n        self.v\n\n";

fn has_fn(module: &crate::hir::HirModule, name: &str) -> bool {
    module.functions.iter().any(|f| f.name == name)
}

#[test]
fn impl_materialises_defaults_of_its_own_same_named_trait() {
    let src = format!("{UNRELATED_FIRST}{REAL_TRAIT}{VK_IMPL}fn probe(k: Vk) -> i64:\n    val t = k.read_twice()\n    t\n");
    let module = parse_and_lower(&src).unwrap();
    assert!(has_fn(&module, "Vk.read_twice"), "default body must be lowered for Vk");
    let probe = module.functions.iter().find(|f| f.name == "probe").unwrap();
    assert_eq!(probe.locals.iter().find(|l| l.name == "t").unwrap().ty, TypeId::I64);
    let vk_impl = module.impls.iter().find(|i| i.type_name == "Vk").unwrap();
    assert!(vk_impl.methods.contains_key("read_twice"));
}

#[test]
fn trait_order_does_not_matter_and_unrelated_impl_is_untouched() {
    let src = format!("{REAL_TRAIT}{UNRELATED_FIRST}{VK_IMPL}fn probe(k: Vk) -> i64:\n    k.read_twice()\n");
    let module = parse_and_lower(&src).unwrap();
    assert!(has_fn(&module, "Vk.read_twice"));
    assert!(!has_fn(&module, "Other.read_twice"), "Other implements the unrelated trait");
}

#[test]
fn equal_overlap_prefers_the_extended_superset_trait() {
    // Older copy of the trait first (no default), extended copy second.
    let older = "trait Backend:\n    fn read() -> i64\n\n";
    let src = format!("{older}{REAL_TRAIT}{VK_IMPL}fn probe(k: Vk) -> i64:\n    k.read_twice()\n");
    let module = parse_and_lower(&src).unwrap();
    assert!(has_fn(&module, "Vk.read_twice"), "superset trait's default must be materialised");
}

#[test]
fn single_trait_defaults_unchanged() {
    let src = format!("{REAL_TRAIT}{VK_IMPL}fn probe(k: Vk) -> i64:\n    k.read_twice()\n");
    let module = parse_and_lower(&src).unwrap();
    assert!(has_fn(&module, "Vk.read_twice"));
}
