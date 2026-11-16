//! `.value` (no parens) on an IMPORTED `unit` newtype must lower like `.value()`.
//! Single-module lowering already works; the failure is cross-module, where
//! the unit erases to ANY in the importing module.
//! Bug: doc/08_tracking/bug/seed_unit_value_field_hir_2026-11-17.md

use crate::hir::Lowerer;
use crate::module_resolver::ModuleResolver;
use simple_parser::Parser;

const PROVIDER: &str = "pub unit Sha256Hex: text\n\npub struct Pin:\n    path: text\n    digest: Sha256Hex\n\npub fn decode() -> Result<[Pin], text>:\n    Ok([])\n\npub unit FreeBytes: i64 as fbytes\n\npub fn headroom(raw: i64) -> FreeBytes?:\n    None\n";

fn lower_main(source: &str) -> Result<crate::hir::HirModule, String> {
    let dir = tempfile::tempdir().unwrap();
    let src = dir.path().join("src");
    std::fs::create_dir(&src).unwrap();
    std::fs::write(src.join("hexmod.spl"), PROVIDER).unwrap();
    let path = src.join("main.spl");
    std::fs::write(&path, source).unwrap();
    let ast = Parser::new(source).parse().unwrap();
    let mut lowerer = Lowerer::with_module_resolver(ModuleResolver::new(dir.path().to_path_buf(), src.clone()), path);
    lowerer.lower_module(&ast).map_err(|e| e.to_string())
}

#[test]
fn imported_unit_value_field_through_loop_var_lowers() {
    let src = "use hexmod.{decode, Pin, Sha256Hex}\n\nfn run() -> Result<i64, text>:\n    val pins = decode()?\n    var n = 0\n    for pin in pins:\n        print(pin.digest.value)\n        n = n + 1\n    Ok(n)\n";
    lower_main(src).expect("`pin.digest.value` on an imported unit must lower");
}

#[test]
fn imported_unit_value_field_on_option_pattern_binding_lowers() {
    let src = "use hexmod.{headroom, FreeBytes}\n\nfn use_it(n: i64) -> i64:\n    n\n\nfn free_of(free: FreeBytes?) -> i64:\n    match free:\n        case Some(f): use_it(f.value)\n        case None: 0\n";
    lower_main(src).expect("`f.value` on an imported unit pattern binding must lower");
}

/// The rewrite must stay scoped: a plain dynamic receiver with ambiguous
/// `value` owners keeps the fail-closed diagnostic.
#[test]
fn dynamic_value_field_with_ambiguous_owners_still_fails_closed() {
    let src = "struct A:\n    value: i64\n\nstruct B:\n    flag: bool\n    value: text\n\nfn probe(x: any) -> i64:\n    return x.value\n";
    let err = super::parse_and_lower(src).err().expect("ambiguous dynamic `.value` must not be guessed");
    assert!(err.to_string().contains("cannot infer field type"), "got {err}");
}
