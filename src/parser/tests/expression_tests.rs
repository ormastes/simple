use simple_parser::ast::*;
use simple_parser::error::ParseError;
use simple_parser::{Parser, ParserMode};
use pretty_assertions::assert_eq;

fn parse(source: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::new(source);
    parser.parse()
}

// === Expression Tests ===

#[test]
fn test_integer_literal() {
    let module = parse("42").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Integer(n)) = &module.items[0] {
        assert_eq!(*n, 42);
    } else {
        panic!("Expected integer expression");
    }
}

#[test]
fn test_binary_expression() {
    let module = parse("1 + 2").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
        assert_eq!(*op, BinOp::Add);
        assert_eq!(**left, Expr::Integer(1));
        assert_eq!(**right, Expr::Integer(2));
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_operator_precedence() {
    let module = parse("1 + 2 * 3").unwrap();
    // Should parse as 1 + (2 * 3)
    if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
        assert_eq!(*op, BinOp::Add);
        assert_eq!(**left, Expr::Integer(1));
        if let Expr::Binary { op: inner_op, .. } = &**right {
            assert_eq!(*inner_op, BinOp::Mul);
        } else {
            panic!("Expected nested binary");
        }
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_function_call() {
    let module = parse("foo(1, 2)").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("foo".to_string()));
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_method_call() {
    let module = parse("obj.method(x)").unwrap();
    if let Node::Expression(Expr::MethodCall {
        receiver,
        method,
        args,
    }) = &module.items[0]
    {
        assert_eq!(**receiver, Expr::Identifier("obj".to_string()));
        assert_eq!(method, "method");
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected method call");
    }
}

#[test]
fn test_array_literal() {
    let module = parse("[1, 2, 3]").unwrap();
    if let Node::Expression(Expr::Array(elements)) = &module.items[0] {
        assert_eq!(elements.len(), 3);
    } else {
        panic!("Expected array literal");
    }
}

// === Infix Keyword Tests (to, not_to) ===

#[test]
fn test_infix_to_keyword() {
    // `expect 5 to eq 5` should parse as `expect(5).to(eq(5))`
    let module = parse("expect 5 to eq 5").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::MethodCall { receiver, method, args }) = &module.items[0] {
        assert_eq!(method, "to");
        // Receiver should be expect(5)
        if let Expr::Call { callee, args: call_args } = &**receiver {
            assert_eq!(**callee, Expr::Identifier("expect".to_string()));
            assert_eq!(call_args.len(), 1);
            assert_eq!(call_args[0].value, Expr::Integer(5));
        } else {
            panic!("Expected Call expression as receiver");
        }
        // Argument should be eq(5)
        assert_eq!(args.len(), 1);
        if let Expr::Call { callee, args: matcher_args } = &args[0].value {
            assert_eq!(**callee, Expr::Identifier("eq".to_string()));
            assert_eq!(matcher_args.len(), 1);
            assert_eq!(matcher_args[0].value, Expr::Integer(5));
        } else {
            panic!("Expected Call expression as argument to .to()");
        }
    } else {
        panic!("Expected MethodCall expression");
    }
}

#[test]
fn test_infix_not_to_keyword() {
    // `expect 5 not_to eq 6` should parse as `expect(5).not_to(eq(6))`
    let module = parse("expect 5 not_to eq 6").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::MethodCall { method, .. }) = &module.items[0] {
        assert_eq!(method, "not_to");
    } else {
        panic!("Expected MethodCall expression");
    }
}

#[test]
fn test_infix_to_with_include_matcher() {
    // `expect arr to include 3` should parse as `expect(arr).to(include(3))`
    let module = parse("expect arr to include 3").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::MethodCall { receiver, method, args }) = &module.items[0] {
        assert_eq!(method, "to");
        // Receiver: expect(arr)
        if let Expr::Call { callee, .. } = &**receiver {
            assert_eq!(**callee, Expr::Identifier("expect".to_string()));
        } else {
            panic!("Expected Call for receiver");
        }
        // Arg: include(3)
        if let Expr::Call { callee, .. } = &args[0].value {
            assert_eq!(**callee, Expr::Identifier("include".to_string()));
        } else {
            panic!("Expected Call for matcher arg");
        }
    } else {
        panic!("Expected MethodCall expression");
    }
}

#[test]
fn test_infix_to_with_paren_call() {
    // `expect(5) to eq(5)` should also work
    let module = parse("expect(5) to eq(5)").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::MethodCall { method, .. }) = &module.items[0] {
        assert_eq!(method, "to");
    } else {
        panic!("Expected MethodCall expression");
    }
}

#[test]
fn test_infix_to_strict_mode() {
    // In strict mode, `expect 5 to eq 5` should still work (infix keywords allowed)
    fn parse_strict(source: &str) -> Result<Module, ParseError> {
        let mut parser = Parser::with_mode(source, ParserMode::Strict);
        parser.parse()
    }

    let module = parse_strict("expect 5 to eq 5").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::MethodCall { method, .. }) = &module.items[0] {
        assert_eq!(method, "to");
    } else {
        panic!("Expected MethodCall expression in strict mode");
    }
}
