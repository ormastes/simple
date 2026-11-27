//! Regression: a bare list/tuple literal statement following `val x = match ...:`
//! whose arms end the block was parsed as an index/call on the last arm value
//! (`expected RBracket, found Comma`).
//! Bug: seed_bare_list_literal_after_match_parsed_as_index_2026-11-14.
use simple_parser::ast::{Expr, Node};
use simple_parser::Parser;

fn body(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().unwrap_or_else(|e| panic!("parse failed: {:?}", e));
    let Node::Function(f) = &module.items[0] else { panic!("expected fn") };
    f.body.statements.clone()
}


#[test]
fn multiline_list_after_match_val() {
    let s = body("fn f(x: i64) -> [text]:\n    val r = match x:\n        case 1: \"a\"\n        case _: \"\"\n    val q = \"z\"\n    [\"p=\" + r, \"q=\" + q]\n");
    assert_eq!(s.len(), 3, "{:?}", s);
    assert!(matches!(&s[2], Node::Expression(Expr::Array(_))), "{:?}", s[2]);
}

#[test]
fn list_directly_after_match_val() {
    let s = body("fn f(x: i64) -> [text]:\n    val a = 1\n    val r = match x:\n        case 1: \"a\"\n        case _: \"\"\n    [\"p=\" + r, \"q\"]\n");
    assert_eq!(s.len(), 3, "{:?}", s);
    assert!(matches!(&s[2], Node::Expression(Expr::Array(_))), "{:?}", s[2]);
}

#[test]
fn one_line_arm_list_after_match_val() {
    let s = body("fn f(x: i64) -> [text]:\n    val a = 1\n    val r = match x:\n        case 1: \"a\"\n        case _: \"\"\n    [r, r]\n");
    assert_eq!(s.len(), 3, "{:?}", s);
    assert!(matches!(&s[2], Node::Expression(Expr::Array(_))), "{:?}", s[2]);
}

#[test]
fn tuple_after_match_val() {
    let s = body("fn f(x: i64) -> (text, text):\n    val a = 1\n    val r = match x:\n        case 1: \"a\"\n        case _: \"\"\n    (r, r)\n");
    assert_eq!(s.len(), 3, "{:?}", s);
    assert!(matches!(&s[2], Node::Expression(Expr::Tuple(_))), "{:?}", s[2]);
}

// Bug seed_parse_multiline_list_driver_compile_options_2026-11-15: the exact
// driver_compile_options.spl shape (list continuing over lines) plus siblings.
const MATCH_PREFIX: &str = "fn f(x: i64) -> [text]:\n    val a = 1\n    val r = match x:\n        case 1: \"a\"\n        case _: \"\"\n";

fn last_after_match(tail: &str) -> Node {
    let s = body(&format!("{MATCH_PREFIX}{tail}"));
    assert_eq!(s.len(), 3, "{:?}", s);
    s[2].clone()
}

#[test]
fn multiline_continued_list_after_match_val() {
    let n = last_after_match("    [\"s=1\", \"m=\" + r,\n        \"q=\" + r, \"t=\" + r,\n        \"z=\" + r]\n");
    assert!(matches!(&n, Node::Expression(Expr::Array(v)) if v.len() == 5), "{:?}", n);
}

#[test]
fn multiline_list_trailing_comma_after_match_val() {
    let n = last_after_match("    [\"s=1\", \"m=\" + r,\n        \"z\",\n    ]\n");
    assert!(matches!(&n, Node::Expression(Expr::Array(v)) if v.len() == 3), "{:?}", n);
}

#[test]
fn multiline_nested_list_after_match_val() {
    let n = last_after_match("    [[\"a\", r],\n        [\"b\" + r]]\n");
    assert!(matches!(&n, Node::Expression(Expr::Array(v)) if v.len() == 2), "{:?}", n);
}

#[test]
fn multiline_list_in_call_arg_after_match_val() {
    let n = last_after_match("    g([\"s=1\", \"m=\" + r,\n        \"z\"])\n");
    assert!(matches!(&n, Node::Expression(Expr::Call { .. })), "{:?}", n);
}
