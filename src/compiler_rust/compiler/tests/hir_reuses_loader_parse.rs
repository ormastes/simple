//! The JIT `run` path parses every imported module twice: once in the module
//! loader (`load_module_with_imports`) and again when HIR lowering loads the
//! same module's types through the cross-lane cache (`parsed_imported_module`
//! -> `shared_source_for_target`). On the web renderer (tab-bar) that is 375
//! second parses, the largest exclusive cost of HIR import loading (~250 ms).
//! When the loader parsed exactly the text the shared cache would parse, it
//! now seeds that cache, so the HIR lane parses nothing again.
//! Bug: doc/08_tracking/bug/hir_import_reparses_loader_modules_2026-11-24.md
//!
//! Pinned by COUNT, not wall clock. Own test binary: the counters are global.

use simple_compiler::perf_counters::{self, IMPORT_AST_HITS, IMPORT_AST_PARSES};
use std::collections::HashSet;
use std::sync::atomic::Ordering;

#[test]
fn hir_lowering_after_module_load_parses_no_import_again() {
    perf_counters::set_enabled(true);
    let dir = std::env::temp_dir().join(format!("hir-reuse-loader-parse-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    std::fs::write(
        dir.join("shapes.spl"),
        "pub struct Point:\n    x: i64\n    y: i64\n\npub fn origin() -> Point:\n    Point(x: 0, y: 0)\n",
    )
    .expect("write shapes");
    // A module whose text the loader rewrites (`@when` OS selection) must
    // still lower correctly; whether it is shared is the loader's call.
    std::fs::write(
        dir.join("geo.spl"),
        "use shapes.{Point}\n\n@when(os=\"windows\")\npub fn sep() -> i64:\n    92\n@else\npub fn sep() -> i64:\n    47\n@end\n\npub fn sum(p: Point) -> i64:\n    p.x + p.y\n",
    )
    .expect("write geo");
    let main_path = dir.join("main.spl");
    std::fs::write(&main_path, "use shapes.{Point, origin}\nuse geo.{sum, sep}\n\nfn main() -> i64:\n    sum(origin()) + sep()\n")
        .expect("write main");

    let ast = simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new())
        .expect("main must load");
    IMPORT_AST_PARSES.store(0, Ordering::Relaxed);
    IMPORT_AST_HITS.store(0, Ordering::Relaxed);
    let main_only = simple_parser::Parser::new(&std::fs::read_to_string(&main_path).unwrap()).parse().unwrap();
    let hir = simple_compiler::hir::lower_with_context(&main_only, &main_path).expect("main must lower");
    let parses = IMPORT_AST_PARSES.load(Ordering::Relaxed);
    let hits = IMPORT_AST_HITS.load(Ordering::Relaxed);
    let _ = std::fs::remove_dir_all(&dir);

    assert!(ast.items.len() > 2, "the loader flattened the imports");
    let point = hir.types.lookup("Point").expect("Point registered");
    assert!(
        matches!(hir.types.get(point), Some(simple_compiler::hir::HirType::Struct { fields, .. }) if fields.len() == 2),
        "Point must carry its two fields"
    );
    assert!(hits > 0, "HIR must have looked the imports up");
    // `shapes.spl` is byte-identical in both lanes; `geo.spl` is selected by
    // `@when` identically in both (the loader's extra arch-global strip is a
    // no-op on it), so neither needs a second parse.
    assert_eq!(parses, 0, "HIR re-parsed {parses} module(s) the loader already parsed");
}
