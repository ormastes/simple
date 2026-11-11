//! `Some(None).?` is PRESENT: the outer layer is `Some`. The interpreter used
//! to unwrap it to the inner `Option::None`, which every truthiness consumer
//! then read as absent. Bug compiler_test_sweep_residuals_2026-08-16
//! (branch_coverage_30 "optional - all nil levels", branch_coverage_35
//! "optional of optional - nil inner").

use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(body: &str) -> i64 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("fn main() -> i64:\n{body}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse");
    interpreter::evaluate_module(&module.items).expect("source must run") as i64
}

#[test]
fn nested_none_payload_is_present() {
    let bits = run(
        "    val a = Some(None)\n    val b: i64? = None\n    val c = Some(5)\n    var bits = 0\n    if a.?: bits = bits + 1\n    if b.?: bits = bits + 2\n    if c.?: bits = bits + 4\n    if not a.?: bits = bits + 8\n    return bits",
    );
    assert_eq!(bits, 1 + 4);
}

#[test]
fn present_payload_still_unwraps() {
    assert_eq!(run("    val c = Some(7)\n    return c.? ?? 0"), 7);
}
