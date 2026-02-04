use simple_parser::ast::{BinOp, Expr, Node};
use simple_parser::Parser;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    parser.parse().expect("should parse");
}

fn parse_err(src: &str) {
    let mut parser = Parser::new(src);
    assert!(parser.parse().is_err(), "should fail to parse");
}

// Error cases
#[test]
fn parse_unclosed_paren() {
    parse_err("let x = (1 + 2");
}

#[test]
fn parse_unclosed_bracket() {
    parse_err("let x = [1, 2, 3");
}

#[test]
fn parse_missing_colon() {
    parse_err("if x > 0\n    y = 1");
}

#[test]
fn parse_missing_indent() {
    parse_err("if x > 0:");
}

// Complex programs
#[test]
fn parse_multiple_statements() {
    parse_ok("let x = 1\nlet y = 2\nlet z = x + y");
}

/// `expect await f == 42` should parse as `expect((await f) == 42)`
/// This tests that `await` is recognized as starting an argument in no-paren calls.
#[test]
fn test_expect_await_parsing() {
    let items = parse("expect await f == 42");
    // Should parse as a single expression (function call), not two separate statements
    assert_eq!(items.len(), 1, "should be single statement, not two");
    // The expression should be a call to 'expect'
    match &items[0] {
        Node::Expression(Expr::Call { callee, args }) => {
            assert!(matches!(**callee, Expr::Identifier(ref name) if name == "expect"));
            assert_eq!(args.len(), 1);
            // The argument should be: (await f) == 42
            match &args[0].value {
                Expr::Binary {
                    op: BinOp::Eq,
                    left,
                    right,
                } => {
                    assert!(matches!(**left, Expr::Await(_)));
                    assert!(matches!(**right, Expr::Integer(42)));
                }
                other => panic!("expected Binary Eq, got {:#?}", other),
            }
        }
        other => panic!("expected Call expression, got {:#?}", other),
    }
}
