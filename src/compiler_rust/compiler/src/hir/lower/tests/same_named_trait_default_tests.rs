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

#[test]
fn implicit_trait_uses_separate_inherent_methods_and_keeps_defaults() {
    let src = "trait Probe:\n    fn read() -> i64\n    fn twice() -> i64:\n        self.read() * 2\n\nstruct Device(Probe):\n    pass\n\nimpl Device:\n    fn read() -> i64:\n        37\n";
    let module = parse_and_lower(src).unwrap();
    let implementation = module.impls.iter().find(|i| i.type_name == "Device" && i.trait_name.as_deref() == Some("Probe")).unwrap();
    assert_eq!(implementation.methods.get("read").map(String::as_str), Some("Device.read"));
    assert_eq!(implementation.methods.get("twice").map(String::as_str), Some("Device.twice"));
    assert!(has_fn(&module, "Device.twice"));
}

#[test]
fn implicit_trait_missing_required_method_is_diagnosed() {
    let error = parse_and_lower("trait Probe:\n    fn read() -> i64\n\nstruct Device(Probe):\n    pass\n").unwrap_err();
    assert!(error.to_string().contains("implicit trait implementation Probe for Device lacks required method read"));
}

#[test]
fn implicit_trait_cross_module_extension_refuses_incomplete_table() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("device.spl"),
        "trait Probe:\n    fn read() -> i64\n\nstruct Device(Probe):\n    pass\n").unwrap();
    std::fs::write(dir.path().join("main.spl"),
        "use .device.{Device as Alias}\n\nimpl Alias:\n    fn read() -> i64:\n        37\n\nfn main() -> i64:\n    0\n").unwrap();
    let ast = crate::pipeline::module_loader::load_module_with_imports(
        &dir.path().join("main.spl"), &mut std::collections::HashSet::new()).unwrap();
    // Cross-module inherent implementation is not supported by this loader
    // composition either. Preserve the exact case and require safe refusal;
    // importing a trait alias for a LOCAL implementation is tested separately.
    let error = super::lower(&ast).unwrap_err();
    assert_eq!(error.to_string(),
        "Unsupported feature: implicit trait implementation Probe for Device lacks required method read");
}

#[test]
fn implicit_trait_ambiguous_owner_refuses() {
    let ambiguous = "trait Probe:\n    fn read() -> i64\n\ntrait Probe:\n    fn other() -> i64\n\nstruct Device(Probe):\n    fn read() -> i64: 1\n";
    assert!(parse_and_lower(ambiguous).unwrap_err().to_string().contains("missing or ambiguous trait owner"));
}

#[test]
fn implicit_trait_per_file_import_keeps_selected_required_and_default_methods() {
    use crate::hir::lower::lowerer::Lowerer;
    use crate::module_resolver::ModuleResolver;
    use simple_parser::Parser;

    let dir = tempfile::tempdir().unwrap();
    let src = dir.path().join("src");
    std::fs::create_dir_all(&src).unwrap();
    std::fs::write(src.join("selected.spl"),
        "trait Probe:\n    fn read() -> i64\n    fn twice() -> i64:\n        self.read() * 2\n").unwrap();
    std::fs::write(src.join("unrelated.spl"),
        "trait Probe:\n    fn unrelated() -> bool\n").unwrap();
    let source = "use selected.{Probe as SelectedProbe}\nuse unrelated.{Probe as OtherProbe}\n\nstruct Device(SelectedProbe):\n    pass\n\nimpl Device:\n    fn read() -> i64:\n        37\n\nfn consume(device: SelectedProbe) -> i64:\n    device.twice()\n";
    let main_path = src.join("main.spl");
    std::fs::write(&main_path, source).unwrap();
    // Deliberately parse only the consumer. No flattening can supply a local
    // Node::Trait; the selected import's retained declaration is authoritative.
    let ast = Parser::new(source).parse().unwrap();
    assert!(!ast.items.iter().any(|n| matches!(n, simple_parser::ast::Node::Trait(_))));
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let mut lowerer = Lowerer::with_module_resolver(resolver, main_path);
    let module = lowerer.lower_module(&ast).unwrap();
    let implementation = module.impls.iter().find(|i| i.type_name == "Device").unwrap();
    assert_eq!(implementation.methods.get("read").map(String::as_str), Some("Device.read"));
    assert_eq!(implementation.methods.get("twice").map(String::as_str), Some("Device.twice"));
    assert!(!implementation.methods.contains_key("unrelated"));
    assert!(has_fn(&module, "Device.twice"));

    let missing_source = "use selected.{Probe as SelectedProbe}\n\nstruct Missing(SelectedProbe):\n    pass\n";
    let missing_path = src.join("missing.spl");
    std::fs::write(&missing_path, missing_source).unwrap();
    let missing_ast = Parser::new(missing_source).parse().unwrap();
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src);
    let mut lowerer = Lowerer::with_module_resolver(resolver, missing_path);
    assert!(lowerer.lower_module(&missing_ast).unwrap_err().to_string()
        .contains("implicit trait implementation SelectedProbe for Missing lacks required method read"));
}

#[test]
fn implicit_trait_supertrait_keeps_existing_direct_slot_behavior() {
    let source = "trait Parent:\n    fn read() -> i64\n\ntrait Child: Parent:\n    fn own() -> i64\n\nstruct Device(Child):\n    fn read() -> i64:\n        1\n    fn own() -> i64:\n        2\n";
    let module = parse_and_lower(source).unwrap();
    let implementation = module.impls.iter().find(|i| i.type_name == "Device").unwrap();
    assert!(implementation.methods.contains_key("read"));
    assert!(implementation.methods.contains_key("own"));
    // This preserves acceptance, not proof of inherited dispatch support.
}
