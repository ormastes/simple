use simple_compiler::pipeline::module_loader::load_module_with_imports;
use simple_compiler::{hir, mir};
use simple_parser::ast::Node;
use std::collections::HashSet;

#[test]
fn flattened_import_retains_struct_trait_impl_for_mir_vtable_attribution() {
    let dir = tempfile::tempdir().expect("temp fixture directory");
    let trait_module = dir.path().join("kinded.spl");
    let impl_module = dir.path().join("block.spl");
    let entry = dir.path().join("main.spl");
    std::fs::write(&trait_module, "trait Kinded:\n    fn kind() -> i64:\n        pass\n").expect("trait fixture");
    std::fs::write(
        &impl_module,
        "use kinded.{Kinded}\nstruct ImportedBlock(Kinded):\n    fn kind() -> i64: 7\n",
    )
    .expect("implementation fixture");
    std::fs::write(
        &entry,
        "use block.{ImportedBlock}\nfn main() -> i64: ImportedBlock().kind()\n",
    )
    .expect("entry fixture");

    let ast = load_module_with_imports(&entry, &mut HashSet::new()).expect("flattened imports");
    let imported = ast
        .items
        .iter()
        .find_map(|node| match node {
            Node::Struct(definition) if definition.name == "ImportedBlock" => Some(definition),
            _ => None,
        })
        .expect("flattened imports retain the imported struct");
    assert!(
        imported
            .attributes
            .iter()
            .any(|attribute| attribute.name == "implements"),
        "flattened import lost synthetic implements(Trait) attribute"
    );
    let hir = hir::lower(&ast).expect("HIR lowering");
    assert!(
        hir.impls
            .iter()
            .any(|imp| imp.type_name == "ImportedBlock" && imp.trait_name.as_deref() == Some("Kinded")),
        "flattened import lost synthetic implements(Trait) before HIR"
    );
    let mir = mir::lower_to_mir(&hir).expect("MIR lowering");
    assert!(
        mir.vtable_impls
            .iter()
            .any(|(_, owner, _, slots, _)| owner == "ImportedBlock" && !slots.is_empty()),
        "HIR impl disappeared before MIR vtable attribution"
    );
}

#[test]
fn imported_trait_parameter_retains_owner_for_virtual_call() {
    let dir = tempfile::tempdir().expect("temp fixture directory");
    let trait_module = dir.path().join("gateway.spl");
    let impl_module = dir.path().join("adapter.spl");
    let entry = dir.path().join("main.spl");
    std::fs::write(&trait_module, "trait Gateway:\n    fn store() -> i64\n").unwrap();
    std::fs::write(
        &impl_module,
        "use gateway.{Gateway}\nstruct Adapter:\n    value: i64\nimpl Gateway for Adapter:\n    fn store(self) -> i64: self.value\n",
    )
    .unwrap();
    std::fs::write(
        &entry,
        "use gateway.{Gateway}\nuse adapter.{Adapter}\nfn consume(gateway: Gateway) -> i64:\n    gateway.store()\n",
    )
    .unwrap();

    let ast = load_module_with_imports(&entry, &mut HashSet::new()).expect("flattened imports");
    let hir = hir::lower(&ast).expect("HIR lowering");
    let consume_hir = hir.functions.iter().find(|function| function.name == "consume").unwrap();
    assert_eq!(consume_hir.params[0].type_name_hint.as_deref(), Some("Gateway"));
    let trait_impls = std::collections::HashMap::from([("Gateway".to_string(), vec!["Adapter".to_string()])]);
    let mir = mir::lower_to_mir_with_global_trait_impls(&hir, &trait_impls, false).expect("MIR lowering");
    let consume = mir.functions.iter().find(|function| function.name == "consume").unwrap();
    assert!(consume.blocks.iter().flat_map(|block| &block.instructions).any(
        |instruction| matches!(instruction, mir::MirInst::MethodCallVirtual { vtable_slot: 0, .. })
    ));
    assert!(consume.blocks.iter().flat_map(|block| &block.instructions).all(
        |instruction| !matches!(instruction, mir::MirInst::MethodCallStatic { func_name, .. } if func_name == "store")
    ));
}

#[test]
fn native_per_file_import_retains_trait_method_metadata() {
    let dir = tempfile::tempdir().expect("temp fixture directory");
    let project = dir.path();
    let compiler_root = project.join("src/compiler");
    let contract = compiler_root.join("00.common/cache_contract");
    std::fs::create_dir_all(&contract).unwrap();
    let trait_module = contract.join("gateway.spl");
    let entry = contract.join("registration.spl");
    std::fs::write(&trait_module, "pub trait Gateway:\n    fn store() -> i64\n").unwrap();
    std::fs::write(
        &entry,
        "use compiler.common.cache_contract.gateway (Gateway)\nfn consume(gateway: Gateway) -> i64:\n    gateway.store()\n",
    )
    .unwrap();

    let source = std::fs::read_to_string(&entry).unwrap();
    let ast = simple_parser::Parser::new(&source).parse().expect("entry parse");
    let resolver = simple_compiler::module_resolver::ModuleResolver::new(
        project.to_path_buf(),
        compiler_root,
    )
    .with_extra_source_roots(vec![project.join("src")]);
    let mut lowerer = simple_compiler::hir::Lowerer::with_module_resolver(resolver, entry);
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).expect("per-file HIR lowering");
    assert!(hir.trait_infos.contains_key("Gateway"), "imported trait metadata was not loaded");
    // Entry-closure builds may legitimately prune every concrete implementation
    // while retaining a helper whose parameter is explicitly trait-typed.
    let mir = mir::lower_to_mir(&hir).expect("per-file MIR lowering");
    let consume = mir.functions.iter().find(|function| function.name == "consume").unwrap();
    assert!(consume.blocks.iter().flat_map(|block| &block.instructions).any(
        |instruction| matches!(instruction, mir::MirInst::MethodCallVirtual { vtable_slot: 0, .. })
    ));
}

#[test]
fn native_vhdl_driver_imports_resolve_to_existing_plugin_owners() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..").canonicalize().unwrap();
    let source_root = repo.join("src");
    let resolver = simple_compiler::module_resolver::ModuleResolver::new(
        repo.clone(), source_root.join("compiler"),
    ).with_extra_source_roots(vec![source_root.clone()]);
    let mut resolved_plugin_imports = 0;
    for module in [
        "plugins/backend_vhdl/driver/driver_aot_vhdl_output.spl",
        "plugins/backend_vhdl/driver/driver_vhdl_artifact_build.spl",
    ] {
        let file = source_root.join(module);
        let source = std::fs::read_to_string(&file).unwrap();
        let ast = simple_parser::Parser::new(&source).parse().unwrap();
        for node in &ast.items {
            if let Node::UseStmt(import) = node {
                if import.path.segments.first().map(String::as_str) != Some("plugins") {
                    continue;
                }
                let resolved = resolver.resolve(&import.path, &file)
                    .unwrap_or_else(|error| panic!("{module}: {:?}: {error:?}", import.path));
                assert!(resolved.path.is_file(), "plugin owner must exist: {:?}", resolved.path);
                assert!(resolved.path.starts_with(source_root.join("plugins/backend_vhdl")));
                resolved_plugin_imports += 1;
            }
        }
    }
    assert_eq!(resolved_plugin_imports, 7, "all driver plugin imports must be checked");
}

fn virtual_and_bare_calls(mir: &mir::MirModule, function: &str, method: &str) -> (usize, usize) {
    let function = mir.functions.iter().find(|f| f.name == function).unwrap();
    let instructions: Vec<_> = function.blocks.iter().flat_map(|block| &block.instructions).collect();
    let virtual_calls = instructions
        .iter()
        .filter(|instruction| matches!(instruction, mir::MirInst::MethodCallVirtual { .. }))
        .count();
    let bare_calls = instructions
        .iter()
        .filter(|instruction| matches!(instruction, mir::MirInst::MethodCallStatic { func_name, .. } if func_name == method))
        .count();
    (virtual_calls, bare_calls)
}

// doc/08_tracking/bug/trait_receiver_cross_unit_bare_call_stubbed_2026-10-20.md
// The payload of an `Option<Trait>` keeps its declared trait: with no
// implementation in this unit the call used to become the bare-name
// `implementation_identity` (nil stub / first same-named method at link).
#[test]
fn optional_trait_payload_binding_lowers_to_virtual_call() {
    let source = "trait Ident:\n    fn identity() -> text\n    fn implementation_identity() -> text\n\n\
fn by_some(reducer: Ident?) -> text:\n    if val Some(strategy) = reducer:\n        return strategy.implementation_identity()\n    \"none\"\n\n\
fn by_plain(reducer: Ident?) -> text:\n    if val strategy = reducer:\n        return strategy.implementation_identity()\n    \"none\"\n\n\
fn by_match(reducer: Ident?) -> text:\n    match reducer:\n        case Some(strategy):\n            return strategy.implementation_identity()\n        case None:\n            return \"none\"\n    \"none\"\n\n\
fn by_local() -> text:\n    val reducer: Ident? = None\n    if val Some(strategy) = reducer:\n        return strategy.implementation_identity()\n    \"none\"\n";
    let ast = simple_parser::Parser::new(source).parse().expect("parse");
    let hir = hir::lower(&ast).expect("HIR lowering");
    let mir = mir::lower_to_mir(&hir).expect("MIR lowering");
    for function in ["by_some", "by_plain", "by_match", "by_local"] {
        let (virtual_calls, bare_calls) = virtual_and_bare_calls(&mir, function, "implementation_identity");
        assert_eq!(bare_calls, 0, "{function}: payload call lowered by bare name");
        assert_eq!(virtual_calls, 1, "{function}: payload call is not a vtable dispatch");
    }
}

// `class Name with Trait:` is a trait implementation: it must produce a HirImpl
// (and so a vtable) exactly like `impl Trait for Name`. A class missing an
// abstract method keeps the previous behaviour instead of failing to lower.
#[test]
fn class_with_trait_clause_records_trait_impl() {
    let source = "trait Ident:\n    fn identity() -> text\n    fn label() -> text:\n        \"default\"\n\n\
class Alpha with Ident:\n    tag: text\n    fn identity() -> text: self.tag\n\n\
class Partial with Ident:\n    tag: text\n\n\
trait Other:\n    fn other() -> i64\n\n\
class Both with Ident, Other:\n    tag: text\n    fn identity() -> text: self.tag\n    fn other() -> i64: 1\n";
    let ast = simple_parser::Parser::new(source).parse().expect("parse");
    let hir = hir::lower(&ast).expect("HIR lowering");
    let alpha = hir
        .impls
        .iter()
        .find(|imp| imp.type_name == "Alpha" && imp.trait_name.as_deref() == Some("Ident"))
        .expect("class-with trait clause recorded no impl");
    assert_eq!(alpha.methods.get("identity").map(String::as_str), Some("Alpha.identity"));
    assert_eq!(alpha.methods.get("label").map(String::as_str), Some("Alpha.label"), "default method not inherited");
    assert!(!hir.impls.iter().any(|imp| imp.type_name == "Partial"), "incomplete class must not get an impl");
    // One vtable header per object: two traits would share it with clashing slots.
    assert!(!hir.impls.iter().any(|imp| imp.type_name == "Both"), "multi-trait class must not get an impl");
    let mir = mir::lower_to_mir(&hir).expect("MIR lowering");
    assert!(mir.vtable_impls.iter().any(|(_, owner, _, slots, _)| owner == "Alpha" && slots.len() == 2));
}
