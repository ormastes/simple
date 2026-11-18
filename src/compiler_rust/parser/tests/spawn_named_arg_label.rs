//! `spawn` is a soft keyword (actor spawn expression) but must still work as a
//! named-argument label: `R(spawn: X.Rejected("..."))`. Until 2026-11-18 the
//! seed rejected it with "function arguments: expected Comma, found Colon",
//! which broke the phase-1 native build of the full CLI (container providers).

use simple_parser::Parser;

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    if let Err(err) = parser.parse() {
        panic!("should parse, got error: {err}\n--- source ---\n{src}");
    }
}

#[test]
fn spawn_as_named_arg_label() {
    parse_ok("fn f() -> R:\n    return R(spawn: 1)\n");
}

#[test]
fn spawn_label_with_qualified_call_value_multiline() {
    parse_ok("fn f() -> R:\n    return R(spawn: S.Rejected(\"x\"),\n        refusal: 2)\n");
}

#[test]
fn spawn_still_prefixes_operand() {
    parse_ok("fn f():\n    val h = spawn worker\n");
}
