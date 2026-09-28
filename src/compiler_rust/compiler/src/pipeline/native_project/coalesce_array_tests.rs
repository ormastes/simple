use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;

use crate::hir::{HirExprKind, HirStmt, HirType, Lowerer, TypeId};
use crate::module_resolver::ModuleResolver;

fn fixture_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../test/fixtures/native/optional_array_coalesce")
}

#[test]
fn imported_optional_array_coalesce_preserves_nominal_loop_elements() {
    let root = fixture_root();
    let entry = root.join("main.spl");
    let sources: Vec<_> = ["main.spl", "probe/rows.spl", "probe/types.spl"]
        .into_iter()
        .map(|relative| {
            let path = root.join(relative);
            let source = std::fs::read_to_string(&path).unwrap();
            (path, source)
        })
        .collect();
    // Discover the actual declarations/imports, as NativeProjectBuilder does;
    // do not supply hand-authored return or layout metadata to the lowerer.
    let imports = super::imports::build_import_map(&sources, std::slice::from_ref(&root), &root);
    let mut field_indices: HashMap<String, HashSet<usize>> = HashMap::new();
    for fields in imports.struct_defs.values() {
        for (index, (field, _)) in fields.iter().enumerate() {
            field_indices.entry(field.clone()).or_default().insert(index);
        }
    }
    let ambiguous: HashSet<_> = field_indices
        .into_iter()
        .filter_map(|(name, indices)| (indices.len() > 1).then_some(name))
        .collect();
    assert!(ambiguous.contains("window_id"));
    let ast = simple_parser::Parser::new(&sources[0].1).parse().unwrap();
    let resolver = ModuleResolver::new(root.clone(), root.clone());
    let mut lowerer = Lowerer::with_module_resolver(resolver, entry);
    lowerer.set_lenient_types(true);
    lowerer.set_global_struct_defs(Arc::new(imports.struct_defs));
    lowerer.set_duplicate_global_struct_defs(Arc::new(imports.duplicate_struct_defs));
    lowerer.set_ambiguous_field_names(Arc::new(ambiguous));
    lowerer.set_global_fn_return_types(Arc::new(imports.fn_return_types));
    let module = lowerer.lower_module(&ast).expect("imported array coalesce must lower");
    for name in ["count_local", "count_direct"] {
        let function = module.functions.iter().find(|function| function.name == name).unwrap();
        let ws = function.locals.iter().find(|local| local.name == "ws").unwrap();
        let Some(HirType::Array { element, .. }) = module.types.get(ws.ty) else {
            panic!(
                "{name}: coalesced local must be Array, got {:?}",
                module.types.get(ws.ty)
            );
        };
        assert!(matches!(module.types.get(*element), Some(HirType::Struct { name, .. }) if name == "WindowInfo"));
        let w = function.locals.iter().find(|local| local.name == "w").unwrap();
        assert_eq!(w.ty, *element, "{name}: loop binding must retain nominal element type");
        let loop_body = function
            .body
            .iter()
            .find_map(|statement| match statement {
                HirStmt::For { body, .. } => Some(body),
                _ => None,
            })
            .unwrap();
        let field = loop_body
            .iter()
            .find_map(|statement| match statement {
                HirStmt::Let { value: Some(expr), .. } => Some(expr),
                _ => None,
            })
            .unwrap();
        assert_eq!(field.ty, TypeId::STRING);
        assert!(
            matches!(field.kind, HirExprKind::FieldAccess { field_index: 0, .. }),
            "{name}: window_id must use WindowInfo slot 0, not Decoy slot 1"
        );
    }
}
