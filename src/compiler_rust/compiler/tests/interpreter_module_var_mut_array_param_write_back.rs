// Regression: a module-level `var` array passed from MODULE SCOPE to a `mut`
// array parameter must observe the callee's element writes. The Bug #19
// write-back updated only the calling frame, while module-scope reads resolve
// through the module-global stores, so the caller saw the pre-call value.
// Bug: doc/08_tracking/bug/seed_interp_module_var_mut_array_param_write_back_lost_2026-11-04.md

use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;

fn parse_and_eval(source: &str) -> i32 {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse");
    evaluate_module(&module.items).expect("eval")
}

#[test]
fn module_var_i64_u8_f64_mut_param_writes_reach_module_scope() {
    let source = r#"
var gi: [i64] = [0; 4]
var gu: [u8] = [0u8; 4]
var gf: [f64] = [0.0; 4]
fn fill(mut meta: [i64], mut pixels: [u8]):
    pixels[3] = 200u8
    meta[0] = 7
fn setf(mut a: [f64]):
    a[1] = 2.5
fill(gi, gu)
setf(gf)
main = if gi[0] == 7 and gu[3] == 200u8 and gf[1] == 2.5: 1 else: 0
"#;
    assert_eq!(parse_and_eval(source), 1);
}

#[test]
fn module_var_mut_param_write_survives_call_depth_two() {
    let source = r#"
var gi: [i64] = [0; 4]
fn inner(mut xs: [i64]):
    xs[2] = 42
fn outer(mut xs: [i64]):
    inner(xs)
outer(gi)
main = gi[2]
"#;
    assert_eq!(parse_and_eval(source), 42);
}

#[test]
fn module_struct_array_field_mut_param_write_reaches_module_scope() {
    let source = r#"
class Holder:
    data: [i64]
var h = Holder(data: [0; 4])
fn put(mut xs: [i64]):
    xs[1] = 9
put(h.data)
main = h.data[1]
"#;
    assert_eq!(parse_and_eval(source), 9);
}
