// Regression: element writes into a `mut xs: [u8]` parameter must reach the
// caller when the caller's binding is declared `[u8]` (packed
// `Value::ByteArray` storage), exactly like `[i64]` params do. Seed
// release100-7a0e6fe516f returned p0=0 here; fixed by bafc15f38a7.
// Locals only: module-level `var`s are passed by value in both JIT and
// interpreter today, for [i64] too, so they are not the subject here.
// Bug: doc/08_tracking/bug/seed_interp_mut_u8_array_param_element_write_lost_2026-11-04.md

use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;

fn parse_and_eval(source: &str) -> i32 {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse");
    evaluate_module(&module.items).expect("eval")
}

#[test]
fn typed_u8_mut_param_element_write_reaches_caller() {
    let source = r#"
fn fill(mut meta: [i64], mut pixels: [u8]):
    var i: i64 = 0
    while i < pixels.len():
        pixels[i] = 200u8
        i = i + 1
    meta[0] = 7
fn run() -> i64:
    var m: [i64] = [0; 4]
    var p: [u8] = [0u8; 5]
    fill(m, p)
    if m[0] == 7 and p[0] == 200u8 and p[4] == 200u8: 1 else: 0
main = run()
"#;
    assert_eq!(parse_and_eval(source), 1);
}

#[test]
fn typed_u8_mut_param_write_survives_call_depth_two() {
    let source = r#"
fn inner(mut xs: [u8], at: i64):
    xs[at * 2 + 1] = 42u8
fn outer(mut xs: [u8]):
    inner(xs, 1)
fn run() -> i64:
    var p: [u8] = [0u8; 4]
    outer(p)
    p[3]
main = run()
"#;
    assert_eq!(parse_and_eval(source), 42);
}
