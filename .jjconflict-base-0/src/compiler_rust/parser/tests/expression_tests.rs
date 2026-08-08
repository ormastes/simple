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
fn cast_before_bitwise_or_is_binary() {
    let module = parse("bytes[off] as u32 | ((bytes[off + 1] as u32) << 8)").unwrap();
    let Node::Expression(Expr::Binary {
        op: BinOp::BitOr, left, ..
    }) = &module.items[0]
    else {
        panic!("Expected bitwise-or expression, got {:?}", module.items[0]);
    };
    let Expr::Cast { target_type, .. } = &**left else {
        panic!("Expected cast on left side, got {left:?}");
    };

    assert_eq!(target_type, &Type::Simple("u32".to_string()));
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
fn test_danger_block_is_unsafe_boundary_not_call() {
    let module = parse("danger:\n    val x = 40\n    x + 2\n").unwrap();
    let Node::Expression(Expr::UnsafeBlock(statements)) = &module.items[0] else {
        panic!("Expected unsafe block, got {:?}", module.items[0]);
    };
    assert_eq!(statements.len(), 2);

    let ordinary_call = parse("danger(1)").unwrap();
    assert!(matches!(ordinary_call.items[0], Node::Expression(Expr::Call { .. })));
}

#[test]
fn test_method_call() {
    let module = parse("obj.method(x)").unwrap();
    if let Node::Expression(Expr::MethodCall {
        receiver, method, args, ..
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
fn grid_is_an_identifier_outside_grid_literal_syntax() {
    parse(
        "fn f(grid: i64, block: i64) -> i64:\n    val cfg = GpuLaunchConfig(grid_x: grid, block_x: block)\n    grid.len()\n    grid[0]\n",
    )
    .expect("grid identifier uses should parse");
}

#[test]
fn grid_literal_remains_contextual() {
    for source in ["grid:\n    | 1 | 2 |\n", "grid device=\"cuda\":\n    | 1 | 2 |\n"] {
        let module = parse(source).expect("grid literal should parse");
        assert!(matches!(module.items[0], Node::Expression(Expr::GridLiteral { .. })));
    }
}

#[test]
fn test_constant_method_call_is_not_parsed_as_static_type_path() {
    let module = parse("FRAME_HEADER_WORDS.to_u32()").unwrap();
    let Node::Expression(Expr::MethodCall { receiver, method, .. }) = &module.items[0] else {
        panic!("Expected method call, got {:?}", module.items[0]);
    };
    assert_eq!(**receiver, Expr::Identifier("FRAME_HEADER_WORDS".to_string()));
    assert_eq!(method, "to_u32");

    for source in ["FrameHeader.new()", "TCB.empty(1)"] {
        let static_call = parse(source).unwrap();
        assert!(matches!(
            static_call.items[0],
            Node::Expression(Expr::MethodCall { .. })
        ));
    }
}

#[test]
fn test_map_placeholder_inside_fstring_interpolation() {
    let module = parse("[\"a\"].map(\"item:{_1}\")").unwrap();
    if let Node::Expression(Expr::MethodCall { method, args, .. }) = &module.items[0] {
        assert_eq!(method, "map");
        assert_eq!(args.len(), 1);
        match &args[0].value {
            Expr::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].name, "__p0");
                match &**body {
                    Expr::FString { parts, type_meta } => {
                        assert_eq!(type_meta.const_keys(), Some(&vec!["__p0".to_string()]));
                        assert_eq!(parts[0], FStringPart::Literal("item:".to_string()));
                        assert_eq!(parts[1], FStringPart::Expr(Expr::Identifier("__p0".to_string())));
                    }
                    other => panic!("Expected f-string lambda body, got {other:?}"),
                }
            }
            other => panic!("Expected lambda argument, got {other:?}"),
        }
    } else {
        panic!("Expected map method call");
    }
}

#[test]
fn test_map_tuple_placeholder_inside_fstring_interpolation() {
    let module = parse("[\"i64\"].enumerate().map(\"{_1.0}:{_1.1}\")").unwrap();
    if let Node::Expression(Expr::MethodCall { method, args, .. }) = &module.items[0] {
        assert_eq!(method, "map");
        assert_eq!(args.len(), 1);
        match &args[0].value {
            Expr::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].name, "__p0");
                match &**body {
                    Expr::FString { parts, .. } => {
                        assert_eq!(
                            parts[0],
                            FStringPart::Expr(Expr::TupleIndex {
                                receiver: Box::new(Expr::Identifier("__p0".to_string())),
                                index: 0,
                            })
                        );
                        assert_eq!(parts[1], FStringPart::Literal(":".to_string()));
                        assert_eq!(
                            parts[2],
                            FStringPart::Expr(Expr::TupleIndex {
                                receiver: Box::new(Expr::Identifier("__p0".to_string())),
                                index: 1,
                            })
                        );
                    }
                    other => panic!("Expected f-string lambda body, got {other:?}"),
                }
            }
            other => panic!("Expected lambda argument, got {other:?}"),
        }
    } else {
        panic!("Expected map method call");
    }
}

#[test]
fn nested_string_literals_remain_fstring_expressions() {
    for source in [
        r#""j={xs.join("-")}""#,
        r#""std::tuple<{types.join(", ")}>""#,
        r#""struct_{member_ids.map("{_}").join("_")}""#,
    ] {
        let module = parse(source).expect("nested string interpolation should parse");
        let Node::Expression(Expr::FString { parts, .. }) = &module.items[0] else {
            panic!("Expected outer FString, got {:?}", module.items[0]);
        };
        assert!(
            parts.iter().any(|part| matches!(part, FStringPart::Expr(_))),
            "nested string interpolation must not silently fall back to a literal: {parts:?}"
        );
    }
}

#[test]
fn test_coalesce_default_parses_full_arithmetic_expression() {
    let module = parse("value ?? -1 * 100").unwrap();
    if let Node::Expression(Expr::Coalesce { expr, default }) = &module.items[0] {
        assert_eq!(**expr, Expr::Identifier("value".to_string()));
        match &**default {
            Expr::Binary { op, left, right } => {
                assert_eq!(*op, BinOp::Mul);
                assert_eq!(
                    **left,
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        operand: Box::new(Expr::Integer(1)),
                    }
                );
                assert_eq!(**right, Expr::Integer(100));
            }
            other => panic!("Expected arithmetic default expression, got {other:?}"),
        }
    } else {
        panic!("Expected coalesce expression");
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

#[test]
fn test_region_domain_custom_block_expression() {
    let module = parse("schema{Building: id Uuid}").unwrap();
    if let Node::Expression(Expr::BlockExpr { kind, payload }) = &module.items[0] {
        assert_eq!(kind, "schema");
        assert_eq!(payload, "Building: id Uuid");
    } else {
        panic!("Expected schema block expression");
    }
}

// === Infix Keyword Tests (to, not_to) ===

#[test]
fn test_infix_to_keyword() {
    // `expect 5 to eq 5` should parse as `expect(5).to(eq(5))`
    let module = parse("expect 5 to eq 5").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::MethodCall {
        receiver, method, args, ..
    }) = &module.items[0]
    {
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
    if let Node::Expression(Expr::MethodCall {
        receiver, method, args, ..
    }) = &module.items[0]
    {
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
    // `go(x) \: x * 2` should parse as go expression that captures x
    let module = parse("go(x) \\: x * 2").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go { args, params, body }) = &module.items[0] {
        // With args but no params, it's capture form
        assert_eq!(args.len(), 1);
        if let Expr::Identifier(name) = &args[0] {
            assert_eq!(name, "x");
        }
        assert_eq!(params.len(), 0); // \: has no params (capture form)
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
    // `go(x, y) \a, b: a + b` should parse as go expression with args passed to params
    let module = parse("go(x, y) \\a, b: a + b").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go { args, params, body }) = &module.items[0] {
        // With both args and params, it's args form (passing args to params)
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
    // `go(x, y, z) \: x + y + z` - capture multiple variables
    let module = parse("go(x, y, z) \\: x + y + z").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go { args, params, .. }) = &module.items[0] {
        // Multiple args with no params = capture those specific vars
        assert_eq!(args.len(), 3);
        assert_eq!(params.len(), 0);
    } else {
        panic!("Expected Go expression");
    }
}

#[test]
fn test_go_capture_all_shorthand() {
    // `go \ *: expr` - capture all immutables (shorthand)
    let module = parse("go \\ *: 42").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go { args, params, body }) = &module.items[0] {
        // Empty args and params = capture all
        assert_eq!(args.len(), 0);
        assert_eq!(params.len(), 0);
        // Body should be 42
        assert!(matches!(**body, Expr::Integer(42)));
    } else {
        panic!("Expected Go expression with capture-all");
    }
}

#[test]
fn test_go_capture_all_empty_parens() {
    // `go() \ *: expr` - capture all immutables (with parens)
    let module = parse("go() \\ *: 42").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go { args, params, body }) = &module.items[0] {
        // Empty args and params = capture all
        assert_eq!(args.len(), 0);
        assert_eq!(params.len(), 0);
        // Body should be 42
        assert!(matches!(**body, Expr::Integer(42)));
    } else {
        panic!("Expected Go expression with capture-all");
    }
}

#[test]
fn test_go_capture_all_colon_only() {
    // `go \: expr` - capture all immutables (empty colon)
    let module = parse("go \\: 42").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Go { args, params, body }) = &module.items[0] {
        // Empty args and params = capture all
        assert_eq!(args.len(), 0);
        assert_eq!(params.len(), 0);
        // Body should be 42
        assert!(matches!(**body, Expr::Integer(42)));
    } else {
        panic!("Expected Go expression with capture-all");
    }
}

// === Lambda Tests ===

#[test]
fn test_lambda_with_params() {
    // `\x: x * 2` - lambda with parameter
    let module = parse("\\x: x * 2").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Lambda {
        params, capture_all, ..
    }) = &module.items[0]
    {
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].name, "x");
        assert_eq!(*capture_all, false);
    } else {
        panic!("Expected Lambda expression");
    }
}

#[test]
fn test_lambda_capture_all_star() {
    // `\ *: expr` - lambda that captures all immutables
    let module = parse("\\ *: 42").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Lambda {
        params,
        capture_all,
        body,
        ..
    }) = &module.items[0]
    {
        assert_eq!(params.len(), 0);
        assert_eq!(*capture_all, true);
        assert!(matches!(**body, Expr::Integer(42)));
    } else {
        panic!("Expected Lambda expression with capture-all");
    }
}

#[test]
fn test_lambda_capture_all_empty_colon() {
    // `\: expr` - lambda with empty colon (also captures all)
    let module = parse("\\: 42").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Lambda {
        params,
        capture_all,
        body,
        ..
    }) = &module.items[0]
    {
        assert_eq!(params.len(), 0);
        assert_eq!(*capture_all, true);
        assert!(matches!(**body, Expr::Integer(42)));
    } else {
        panic!("Expected Lambda expression with capture-all");
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
