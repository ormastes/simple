use pretty_assertions::assert_eq;
use simple_parser::ast::*;
use simple_parser::error::ParseError;
use simple_parser::{Parser, ParserMode};

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
    if let Node::Expression(Expr::MethodCall { receiver, method, args }) = &module.items[0] {
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
        if let Expr::Call {
            callee,
            args: call_args,
        } = &**receiver
        {
            assert_eq!(**callee, Expr::Identifier("expect".to_string()));
            assert_eq!(call_args.len(), 1);
            assert_eq!(call_args[0].value, Expr::Integer(5));
        } else {
            panic!("Expected Call expression as receiver");
        }
        // Argument should be eq(5)
        assert_eq!(args.len(), 1);
        if let Expr::Call {
            callee,
            args: matcher_args,
        } = &args[0].value
        {
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

// === Go Keyword Tests ===

#[test]
fn test_go_capture_form() {
    // `go |x| \: x * 2` should parse as go expression with capture
    let module = parse("go |x| \\: x * 2").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go {
        args,
        params,
        is_capture_form,
        body,
    }) = &module.items[0]
    {
        assert_eq!(*is_capture_form, true);
        assert_eq!(args.len(), 1);
        if let Expr::Identifier(name) = &args[0] {
            assert_eq!(name, "x");
        }
        assert_eq!(params.len(), 0); // \: has no params
                                     // Body should be x * 2
        if let Expr::Binary { op, .. } = &**body {
            assert_eq!(*op, BinOp::Mul);
        }
    } else {
        panic!("Expected Go expression with capture form");
    }
}

#[test]
fn test_go_args_form() {
    // `go(x, y) \a, b: a + b` should parse as go expression with args
    let module = parse("go(x, y) \\a, b: a + b").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go {
        args,
        params,
        is_capture_form,
        body,
    }) = &module.items[0]
    {
        assert_eq!(*is_capture_form, false);
        assert_eq!(args.len(), 2);
        assert_eq!(params.len(), 2);
        assert_eq!(params[0], "a");
        assert_eq!(params[1], "b");
        // Body should be a + b
        if let Expr::Binary { op, .. } = &**body {
            assert_eq!(*op, BinOp::Add);
        }
    } else {
        panic!("Expected Go expression with args form");
    }
}

#[test]
fn test_go_multiple_captures() {
    // `go |x, y, z| \: x + y + z`
    let module = parse("go |x, y, z| \\: x + y + z").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go {
        args, is_capture_form, ..
    }) = &module.items[0]
    {
        assert_eq!(*is_capture_form, true);
        assert_eq!(args.len(), 3);
    } else {
        panic!("Expected Go expression");
    }
}

// === Channel Receive Operator Tests ===

#[test]
fn test_channel_receive_operator() {
    // `<-rx` should parse as unary receive operation
    let module = parse("<-rx").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Unary { op, operand }) = &module.items[0] {
        assert_eq!(*op, UnaryOp::ChannelRecv);
        assert_eq!(**operand, Expr::Identifier("rx".to_string()));
    } else {
        panic!("Expected Unary expression with ChannelRecv");
    }
}

#[test]
fn test_channel_receive_in_assignment() {
    // `val x = <-rx` should parse correctly
    let module = parse("val x = <-rx").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Identifier(name) = &stmt.pattern {
            assert_eq!(name, "x");
        }
        if let Some(Expr::Unary { op, operand }) = &stmt.value {
            assert_eq!(*op, UnaryOp::ChannelRecv);
            assert_eq!(**operand, Expr::Identifier("rx".to_string()));
        } else {
            panic!("Expected Unary expression in val initializer");
        }
    } else {
        panic!("Expected Let statement");
    }
}

#[test]
fn test_channel_receive_nested() {
    // `<-<-nested_rx` should parse as nested unary receive operations
    let module = parse("<-<-nested_rx").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Unary { op, operand }) = &module.items[0] {
        assert_eq!(*op, UnaryOp::ChannelRecv);
        // Inner operand should also be a channel receive
        if let Expr::Unary {
            op: inner_op,
            operand: inner_operand,
        } = &**operand
        {
            assert_eq!(*inner_op, UnaryOp::ChannelRecv);
            assert_eq!(**inner_operand, Expr::Identifier("nested_rx".to_string()));
        } else {
            panic!("Expected nested Unary expression");
        }
    } else {
        panic!("Expected Unary expression with ChannelRecv");
    }
}
