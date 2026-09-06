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
    std::fs::write(&trait_module, "trait Kinded:\n    fn kind() -> i64:\n        pass\n")
        .expect("trait fixture");
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
    let imported = ast.items.iter().find_map(|node| match node {
        Node::Struct(definition) if definition.name == "ImportedBlock" => Some(definition),
        _ => None,
    }).expect("flattened imports retain the imported struct");
    assert!(imported.attributes.iter().any(|attribute| attribute.name == "implements"), "flattened import lost synthetic implements(Trait) attribute");
    let hir = hir::lower(&ast).expect("HIR lowering");
    assert!(hir.impls.iter().any(|imp| imp.type_name == "ImportedBlock" && imp.trait_name.as_deref() == Some("Kinded")), "flattened import lost synthetic implements(Trait) before HIR");
    let mir = mir::lower_to_mir(&hir).expect("MIR lowering");
    assert!(mir.vtable_impls.iter().any(|(_, owner, _, slots, _)| owner == "ImportedBlock" && !slots.is_empty()), "HIR impl disappeared before MIR vtable attribution");
}
