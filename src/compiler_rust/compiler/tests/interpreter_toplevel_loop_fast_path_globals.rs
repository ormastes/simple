// Regression: the shape-specialised while/for fast paths in
// `interpreter_control.rs` read and wrote loop variables through `env` only.
// At module top level a `var` lives in `env` as a NON-local binding AND in
// MODULE_GLOBALS, and the identifier read treats MODULE_GLOBALS as
// authoritative for non-local names (interpreter/expr/literals.rs). So a
// top-level `while i < 5: a = inc(a); i = i + 1` left `a == 0` (the write never
// reached MODULE_GLOBALS), and a loop entered after a function had updated the
// global started from the stale `env` copy. The generic AST walk (forced by
// SIMPLE_COVERAGE=1) was correct; function-local loops were unaffected.

use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;

fn parse_and_eval(source: &str) -> i32 {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse");
    evaluate_module(&module.items).expect("eval")
}

#[test]
fn toplevel_while_one_arg_helper_writes_global() {
    let source = r#"
fn inc(x: i64) -> i64:
    x + 1
var a = 0
var i = 0
while i < 5:
    a = inc(a)
    i = i + 1
main = a * 100 + i
"#;
    assert_eq!(parse_and_eval(source), 505);
}

#[test]
fn toplevel_while_two_arg_helper_writes_global() {
    let source = r#"
fn add(x: i64, y: i64) -> i64:
    x + y
var a = 0
var i = 0
while i < 5:
    a = add(a, i)
    i = i + 1
main = a * 100 + i
"#;
    assert_eq!(parse_and_eval(source), 1005);
}

#[test]
fn toplevel_while_direct_int_writes_global() {
    let source = r#"
var a = 0
var i = 0
while i < 5:
    a = a + i
    i = i + 1
main = a * 100 + i
"#;
    assert_eq!(parse_and_eval(source), 1005);
}

#[test]
fn toplevel_while_inline_int_expr_writes_global() {
    let source = r#"
fn f(x: i64, y: i64) -> i64:
    x * y
var a = 0
var i = 0
while i < 5:
    a = a + f(i, 2)
    i = i + 1
main = a * 100 + i
"#;
    assert_eq!(parse_and_eval(source), 2005);
}

#[test]
fn toplevel_for_range_writes_global() {
    let source = r#"
var a = 0
for k in 0..5:
    a = a + k
main = a
"#;
    assert_eq!(parse_and_eval(source), 10);
}

#[test]
fn toplevel_while_inside_if_writes_global() {
    let source = r#"
fn inc(x: i64) -> i64:
    x + 1
var a = 0
var i = 0
if true:
    while i < 5:
        a = inc(a)
        i = i + 1
main = a
"#;
    assert_eq!(parse_and_eval(source), 5);
}

#[test]
fn toplevel_nested_while_writes_global() {
    let source = r#"
fn inc(x: i64) -> i64:
    x + 1
var a = 0
var j = 0
while j < 3:
    var i = 0
    while i < 5:
        a = inc(a)
        i = i + 1
    j = j + 1
main = a
"#;
    assert_eq!(parse_and_eval(source), 15);
}

#[test]
fn toplevel_while_reads_global_updated_by_function() {
    // `bump()` writes the global through MODULE_GLOBALS; the frame's `env`
    // copy of `a` is still 0. The loop must start from the live 10.
    let source = r#"
var a = 0
fn bump():
    a = a + 10
bump()
var i = 0
while i < 5:
    a = a + 1
    i = i + 1
main = a
"#;
    assert_eq!(parse_and_eval(source), 15);
}

#[test]
fn toplevel_for_range_reads_bound_updated_by_function() {
    let source = r#"
var n = 2
fn grow():
    n = 5
grow()
var a = 0
for k in 0..n:
    a = a + k
main = a
"#;
    assert_eq!(parse_and_eval(source), 10);
}

#[test]
fn function_local_while_unchanged() {
    let source = r#"
fn inc(x: i64) -> i64:
    x + 1
fn run() -> i64:
    var a = 0
    var i = 0
    while i < 5:
        a = inc(a)
        i = i + 1
    a
main = run()
"#;
    assert_eq!(parse_and_eval(source), 5);
}

#[test]
fn toplevel_compound_assign_writes_global() {
    // Not a fast-path shape: the generic compound-assignment path wrote `env`
    // only, so `i += 1` at top level was lost (and `while i < 5: i += 1` never
    // terminated). Deliberately loop-free so a regression cannot hang the run.
    let source = r#"
var i = 0
i += 1
i += 2
var s = 10
s -= 3
s *= 2
main = i * 100 + s
"#;
    assert_eq!(parse_and_eval(source), 314);
}
