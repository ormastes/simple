//! E1012 "class X has no field Y": the class-registry note is a debug-only
//! diagnostic, gated by SIMPLE_DEBUG_FIELD_ACCESS / SIMPLE_BOOTSTRAP_DIAG.
//! One file per gate state: the gate is latched in a process-wide OnceLock.
//! bug: native_build_class_surface_misses_newly_added_field_2026-08-17
use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;

const SOURCE: &str = "struct Pt:\n    x: i64\n\nval p = Pt(x: 1)\nmain = p.y\n";

#[test]
fn class_registry_note_on() {
    std::env::set_var("SIMPLE_DEBUG_FIELD_ACCESS", "1");
    let module = Parser::new(SOURCE).parse().expect("parse module");
    let err = evaluate_module(&module.items).expect_err("missing field must error");
    let rendered = err.format_with_source(SOURCE, false);
    assert!(rendered.contains("has no field named"), "unexpected error: {rendered}");
    assert_eq!(rendered.contains("class registry:"), true, "rendered: {rendered}");
}
