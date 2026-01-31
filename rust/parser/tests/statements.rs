use simple_parser::ast::Node;
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

// Let statements
#[test]
fn parse_let_statement() {
    let items = parse("let x = 42");
    assert_eq!(items.len(), 1);
    assert!(matches!(&items[0], Node::Let(_)));
}

#[test]
fn parse_let_mut_statement() {
    let items = parse("let mut x = 42");
    assert!(matches!(&items[0], Node::Let(_)));
}

// Const statement
#[test]
fn parse_const_statement() {
    let items = parse("const X = 100");
    assert!(matches!(&items[0], Node::Const(_)));
}

// Static statements
#[test]
fn parse_static_statement() {
    let items = parse("static counter = 0");
    assert!(matches!(&items[0], Node::Static(_)));
}

#[test]
fn parse_static_mut_statement() {
    let items = parse("static mut counter = 0");
    assert!(matches!(&items[0], Node::Static(_)));
}

// Main binding
#[test]
fn parse_main_binding() {
    parse_ok("main = 42");
}

// Return statement
#[test]
fn parse_return_statement() {
    parse_ok("fn test():\n    return 42");
}

// Break/continue need newline after them
#[test]
fn parse_break_continue() {
    parse_ok("while true:\n    break\n");
    parse_ok("while true:\n    continue\n");
}

// Assignment statements
#[test]
fn parse_assignment_statement() {
    let items = parse("x = 42");
    assert!(matches!(&items[0], Node::Assignment(_)));
}

#[test]
fn parse_augmented_assignment() {
    parse_ok("x += 1");
    parse_ok("x -= 1");
    parse_ok("x *= 2");
    parse_ok("x /= 2");
}

// Context statement
#[test]
fn parse_context_statement() {
    parse_ok("context obj:\n    x = 1");
}
