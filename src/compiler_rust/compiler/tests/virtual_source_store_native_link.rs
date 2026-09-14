//! Minimal Stage-2 oracle for an imported trait's `virtual_source_store` call.
//! It stops before LogicalSourcePath/public-summary projection and exercises the
//! per-file resolver, HIR/MIR dispatch attribution, and native object emitter.

use simple_compiler::codegen::Codegen;
use simple_compiler::hir::Lowerer;
use simple_compiler::mir::{self, MirInst};
use simple_compiler::module_resolver::ModuleResolver;

#[test]
fn imported_virtual_source_store_reaches_native_object_codegen() {
    let dir = tempfile::tempdir().expect("fixture directory");
    let root = dir.path();
    let contract = root.join("src/compiler/00.common/cache_contract");
    std::fs::create_dir_all(&contract).unwrap();
    std::fs::write(
        contract.join("cache_gateway_v1.spl"),
        "pub trait CacheGatewayV1:\n    fn virtual_source_store() -> i64\n",
    )
    .unwrap();
    let entry = contract.join("virtual_source_registration_v1.spl");
    std::fs::write(
        &entry,
        r#"use compiler.common.cache_contract.cache_gateway_v1 (CacheGatewayV1)
pub fn install(gateway: CacheGatewayV1) -> i64:
    gateway.virtual_source_store()
"#,
    )
    .unwrap();

    let source = std::fs::read_to_string(&entry).unwrap();
    let ast = simple_parser::Parser::new(&source).parse().expect("entry parse");
    let resolver = ModuleResolver::new(root.to_path_buf(), root.join("src/compiler"))
        .with_extra_source_roots(vec![root.join("src")]);
    let mut lowerer = Lowerer::with_module_resolver(resolver, entry);
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).expect("per-file HIR lowering");
    let mir = mir::lower_to_mir(&hir).expect("per-file MIR lowering");
    let install = mir.functions.iter().find(|function| function.name == "install").unwrap();
    assert!(install.blocks.iter().flat_map(|block| &block.instructions).any(
        |instruction| matches!(instruction, MirInst::MethodCallVirtual { vtable_slot: 0, .. })
    ));
    assert!(install.blocks.iter().flat_map(|block| &block.instructions).all(
        |instruction| !matches!(instruction, MirInst::MethodCallStatic { func_name, .. } if func_name == "virtual_source_store")
    ));

    let mut codegen = Codegen::new().expect("native codegen initialization");
    let object = codegen.compile_module(&mir).expect("virtual dispatch must reach native object codegen");
    assert!(!object.is_empty(), "native object must not be empty");
}
