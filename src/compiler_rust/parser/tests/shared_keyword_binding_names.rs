//! `shared` is a keyword token but a legal binding name. Every binding
//! position must keep the source spelling; a PascalCase `Shared` identifier
//! is later resolved as a global/variant and dies in LLVM codegen with
//! "llvm global load referenced undeclared symbol `Shared`".
//! Bug: doc/08_tracking/bug/simple_shared_parameter_llvm_global_load_2026-07-17.md
use simple_parser::Parser;

fn debug_ast(src: &str) -> String {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    format!("{:?}", module.items)
}

fn assert_keeps_case(src: &str) {
    let ast = debug_ast(src);
    assert!(!ast.contains("\"Shared\""), "capitalized Shared leaked into AST for:\n{src}\n{ast}");
    assert!(ast.contains("\"shared\""), "lowercase shared missing from AST for:\n{src}\n{ast}");
}

#[test]
fn val_binding() {
    assert_keeps_case("fn f() -> i64:\n    val shared = 1\n    return shared\n");
}

#[test]
fn var_binding() {
    assert_keeps_case("fn f() -> i64:\n    var shared = 1\n    shared = 2\n    return shared\n");
}

#[test]
fn tuple_destructure() {
    assert_keeps_case("fn f() -> i64:\n    val (shared, n) = (1, 2)\n    return shared + n\n");
}

#[test]
fn match_capture() {
    assert_keeps_case("fn f(c: i64) -> i64:\n    match c:\n        case shared:\n            return shared\n");
}

#[test]
fn enum_payload_capture() {
    assert_keeps_case("fn f(o: i64?) -> i64:\n    match o:\n        case Some(shared):\n            return shared\n        case _:\n            return 0\n");
}

#[test]
fn for_loop_variable() {
    assert_keeps_case("fn f(xs: [i64]) -> i64:\n    var t = 0\n    for shared in xs:\n        t = t + shared\n    return t\n");
}

#[test]
fn if_val_binding() {
    assert_keeps_case("fn f(o: i64?) -> i64:\n    if val shared = o:\n        return shared\n    return 0\n");
}

#[test]
fn lambda_parameter() {
    assert_keeps_case("fn f() -> i64:\n    val g = \\shared: shared + 1\n    return g(1)\n");
}
