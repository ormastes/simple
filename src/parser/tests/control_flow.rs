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

// If statements
#[test]
fn parse_if_statement() {
    let items = parse("if x > 0:\n    y = 1");
    assert!(matches!(&items[0], Node::If(_)));
}

#[test]
fn parse_if_else_statement() {
    parse_ok("if x > 0:\n    y = 1\nelse:\n    y = 0");
}

// Uses 'elif' not 'else if'
#[test]
fn parse_complex_if_else() {
    parse_ok("if a:\n    x = 1\nelif b:\n    x = 2\nelse:\n    x = 3");
}

// While loop
#[test]
fn parse_while_loop() {
    let items = parse("while x < 10:\n    x = x + 1");
    assert!(matches!(&items[0], Node::While(_)));
}

// For loop
#[test]
fn parse_for_loop() {
    let items = parse("for i in range(0, 10):\n    sum = sum + i");
    assert!(matches!(&items[0], Node::For(_)));
}

// Match statement
#[test]
fn parse_match_statement() {
    let items = parse("match x:\n    1 =>\n        y = 1\n    _ =>\n        y = 0");
    assert!(matches!(&items[0], Node::Match(_)));
}

#[test]
fn parse_match_with_guard() {
    parse_ok("match x:\n    n if n > 0 =>\n        y = 1\n    _ =>\n        y = 0");
}

// Match patterns use full enum paths or simple identifiers
#[test]
fn parse_match_with_patterns() {
    parse_ok("match opt:\n    Option::Some(x) =>\n        x\n    Option::None =>\n        0");
}

// Loop with break - needs newline after break
#[test]
fn parse_loop_statement() {
    parse_ok("loop:\n    x = x + 1\n    if x > 10:\n        break\n");
}

// Suspension control flow (async-by-default #45)
#[test]
fn parse_if_suspend_statement() {
    let items = parse("if~ x > 0:\n    y = 1");
    if let Node::If(if_stmt) = &items[0] {
        assert!(if_stmt.is_suspend);
    } else {
        panic!("Expected If node");
    }
}

#[test]
fn parse_while_suspend_loop() {
    let items = parse("while~ x < 10:\n    x = x + 1");
    if let Node::While(while_stmt) = &items[0] {
        assert!(while_stmt.is_suspend);
    } else {
        panic!("Expected While node");
    }
}

#[test]
fn parse_for_suspend_loop() {
    let items = parse("for~ i in range(0, 10):\n    sum = sum + i");
    if let Node::For(for_stmt) = &items[0] {
        assert!(for_stmt.is_suspend);
    } else {
        panic!("Expected For node");
    }
}

#[test]
fn parse_suspend_assignment() {
    let items = parse("x ~= async_function()");
    if let Node::Assignment(assign) = &items[0] {
        assert!(matches!(
            assign.op,
            simple_parser::ast::AssignOp::SuspendAssign
        ));
    } else {
        panic!("Expected Assignment node");
    }
}

#[test]
fn parse_regular_vs_suspend_if() {
    // Regular if
    let items = parse("if x > 0:\n    y = 1");
    if let Node::If(if_stmt) = &items[0] {
        assert!(!if_stmt.is_suspend);
    } else {
        panic!("Expected If node");
    }

    // Suspension if
    let items = parse("if~ x > 0:\n    y = 1");
    if let Node::If(if_stmt) = &items[0] {
        assert!(if_stmt.is_suspend);
    } else {
        panic!("Expected If node");
    }
}
