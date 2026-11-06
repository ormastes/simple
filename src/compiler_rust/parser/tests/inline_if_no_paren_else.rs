//! Regression: statement-form inline `if c: print "a" else: print "b"` parsed
//! the else branch with plain `parse_expression`, so `print` became a bare
//! identifier and `"b"` leaked out as a separate tail statement. That stray
//! string became `fn main()`'s value and `run` died with
//! "cannot convert string to int".
//! Bug: seed_run_main_tail_if_print_coerced_to_exit_code_2026-11-06.
use simple_parser::ast::{Expr, Node};
use simple_parser::Parser;

fn main_body(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    let Node::Function(f) = &module.items[0] else { panic!("expected fn") };
    f.body.statements.clone()
}

fn tail_if(body: &[Node]) -> (&Expr, &Expr) {
    match body.last() {
        Some(Node::Expression(Expr::If { then_branch, else_branch: Some(e), .. })) => (then_branch, e),
        other => panic!("expected tail inline if expr, got {:?}", other),
    }
}

#[test]
fn inline_if_no_paren_call_in_else_is_one_statement() {
    let body = main_body("fn main():\n    val c = true\n    if c: print \"a\" else: print \"b\"\n");
    assert_eq!(body.len(), 2, "stray else-arg statement leaked: {:?}", body);
    let (t, e) = tail_if(&body);
    assert!(matches!(t, Expr::Call { .. }), "then: {:?}", t);
    assert!(matches!(e, Expr::Call { .. }), "else: {:?}", e);
}

#[test]
fn inline_if_no_paren_else_not_tail_keeps_next_statement() {
    let body = main_body("fn main():\n    if true: print \"a\" else: print \"b\"\n    print \"after\"\n");
    assert_eq!(body.len(), 2, "{:?}", body);
}

#[test]
fn inline_if_no_paren_else_nested_in_block_if() {
    let body = main_body("fn main():\n    if true:\n        if false: print \"a\" else: print \"b\"\n");
    let Some(Node::If(outer)) = body.last() else { panic!("{:?}", body) };
    assert_eq!(outer.then_block.statements.len(), 1, "{:?}", outer.then_block.statements);
    let (_, e) = tail_if(&outer.then_block.statements);
    assert!(matches!(e, Expr::Call { .. }), "else: {:?}", e);
}

#[test]
fn inline_if_unit_fn_call_tail_paren_form() {
    let mut parser = Parser::new("fn u():
    print \"u\"
fn main():
    if true: u() else: u()
");
    let module = parser.parse().expect("parse ok");
    let Node::Function(m) = &module.items[1] else { panic!("expected main") };
    assert_eq!(m.body.statements.len(), 1);
    let (_, e) = tail_if(&m.body.statements);
    assert!(matches!(e, Expr::Call { .. }));
    let body = main_body("fn main():\n    if true: print(\"a\") else: print(\"b\")\n");
    assert_eq!(body.len(), 1);
    let (_, e) = tail_if(&body);
    assert!(matches!(e, Expr::Call { .. }));
}

#[test]
fn inline_if_int_tail_in_annotated_main_stays_values() {
    let body = main_body("fn main() -> i64:\n    if true: 1 else: 2\n");
    assert_eq!(body.len(), 1);
    let (t, e) = tail_if(&body);
    assert!(matches!(t, Expr::Integer(1)));
    assert!(matches!(e, Expr::Integer(2)));
}

#[test]
fn inline_if_bare_text_tail_stays_strings() {
    let body = main_body("fn main():\n    if true: \"a\" else: \"b\"\n");
    assert_eq!(body.len(), 1);
    let (t, e) = tail_if(&body);
    assert!(!matches!(t, Expr::Call { .. }) && !matches!(e, Expr::Call { .. }), "{:?} {:?}", t, e);
}

#[test]
fn match_tail_with_no_paren_print_arms_is_one_statement() {
    let body = main_body("fn main():\n    val n = 3\n    match n:\n        3: print \"m\"\n        _: print \"z\"\n");
    assert_eq!(body.len(), 2, "{:?}", body);
}
