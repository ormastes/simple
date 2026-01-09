use pretty_assertions::assert_eq;
use simple_parser::ast::*;
use simple_parser::error::ParseError;
use simple_parser::{Parser, ParserMode};

fn parse(source: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::new(source);
    parser.parse()
}

fn parse_strict(source: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::with_mode(source, ParserMode::Strict);
    parser.parse()
}

// === Statement Tests ===

#[test]
fn test_let_statement() {
    let module = parse("let x = 42").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Immutable);
        if let Pattern::Identifier(name) = &stmt.pattern {
            assert_eq!(name, "x");
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_let_mut_statement() {
    let module = parse("let mut x = 42").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Mutable);
    } else {
        panic!("Expected let statement");
    }
}

// === Control Flow Tests ===

#[test]
fn test_if_statement() {
    let source = "if x > 0:\n    print(x)";
    let module = parse(source).unwrap();
    if let Node::If(stmt) = &module.items[0] {
        assert!(stmt.else_block.is_none());
        assert!(stmt.elif_branches.is_empty());
    } else {
        panic!("Expected if statement");
    }
}

#[test]
fn test_for_loop() {
    let source = "for i in range(10):\n    print(i)";
    let module = parse(source).unwrap();
    if let Node::For(stmt) = &module.items[0] {
        if let Pattern::Identifier(name) = &stmt.pattern {
            assert_eq!(name, "i");
        }
    } else {
        panic!("Expected for statement");
    }
}

#[test]
fn test_while_loop() {
    let source = "while x > 0:\n    x = x - 1";
    let module = parse(source).unwrap();
    assert!(matches!(&module.items[0], Node::While(_)));
}

// === Pattern Tests ===

#[test]
fn test_tuple_pattern() {
    let source = "let (x, y) = point";
    let module = parse(source).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Tuple(patterns) = &stmt.pattern {
            assert_eq!(patterns.len(), 2);
        } else {
            panic!("Expected tuple pattern");
        }
    }
}

// === Strict Mode Tests (ParserMode::Strict) ===

#[test]
fn test_strict_mode_allows_simple_no_paren_call() {
    // In strict mode, `func arg` is OK (one level of no-paren call)
    let module = parse_strict("func arg").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("func".to_string()));
        assert_eq!(args.len(), 1);
        assert_eq!(args[0].value, Expr::Identifier("arg".to_string()));
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_strict_mode_allows_no_paren_with_literal() {
    // In strict mode, `func 42` is OK
    let module = parse_strict("func 42").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("func".to_string()));
        assert_eq!(args.len(), 1);
        assert_eq!(args[0].value, Expr::Integer(42));
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_strict_mode_allows_inner_paren_call() {
    // In strict mode, `func1 func2(arg)` is OK (inner has parens)
    let module = parse_strict("func1 func2(arg)").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("func1".to_string()));
        assert_eq!(args.len(), 1);
        // The argument should be a call expression: func2(arg)
        if let Expr::Call {
            callee: inner_callee,
            args: inner_args,
        } = &args[0].value
        {
            assert_eq!(**inner_callee, Expr::Identifier("func2".to_string()));
            assert_eq!(inner_args.len(), 1);
        } else {
            panic!("Expected inner call expression, got {:?}", args[0].value);
        }
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_strict_mode_space_separated_args() {
    // In strict mode, `func1 func2 arg` parses as func1(func2, arg) - space-separated args
    let module = parse_strict("func1 func2 arg").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("func1".to_string()));
        assert_eq!(args.len(), 2);
        assert_eq!(args[0].value, Expr::Identifier("func2".to_string()));
        assert_eq!(args[1].value, Expr::Identifier("arg".to_string()));
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_strict_mode_allows_explicit_parens() {
    // In strict mode, `func1(func2(arg))` is OK (all explicit parens)
    let module = parse_strict("func1(func2(arg))").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("func1".to_string()));
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_strict_mode_allows_multiple_simple_args() {
    // In strict mode, `func a, b, c` is OK (simple identifiers as args)
    let module = parse_strict("func a, b, c").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("func".to_string()));
        assert_eq!(args.len(), 3);
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_strict_mode_allows_mixed_simple_and_paren_args() {
    // In strict mode, `outer a, inner(x)` is OK (inner has parens)
    let module = parse_strict("outer a, inner(x)").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("outer".to_string()));
        assert_eq!(args.len(), 2);
        // Second arg should be a call
        if let Expr::Call { .. } = &args[1].value {
            // OK
        } else {
            panic!("Expected second arg to be a call");
        }
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_strict_mode_mixed_comma_and_space() {
    // In strict mode, `outer a, inner x` parses as outer(a, inner, x) - mixed separators
    let module = parse_strict("outer a, inner x").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert_eq!(**callee, Expr::Identifier("outer".to_string()));
        assert_eq!(args.len(), 3);
        assert_eq!(args[0].value, Expr::Identifier("a".to_string()));
        assert_eq!(args[1].value, Expr::Identifier("inner".to_string()));
        assert_eq!(args[2].value, Expr::Identifier("x".to_string()));
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_normal_mode_allows_nested_no_paren() {
    // In normal mode (default), nested no-paren calls are allowed
    // Note: they may not parse as intended, but they don't error
    let result = parse("func1 func2 arg");
    // Normal mode should not error (though parsing may be ambiguous)
    assert!(
        result.is_ok(),
        "Normal mode should allow nested no-paren syntax"
    );
}

// === GPU/Shared Memory Tests ===

#[test]
fn test_shared_let_basic() {
    // GPU shared memory declaration with type annotation
    let src = "shared let local_data: [f32; 256]\n";
    let module = parse(src).unwrap();
    if let Node::Let(let_stmt) = &module.items[0] {
        assert!(let_stmt.storage_class.is_shared());
        assert!(let_stmt.mutability.is_mutable());
        // Type is in the pattern
        if let Pattern::Typed { ty, .. } = &let_stmt.pattern {
            if let Type::Array { element, size } = ty {
                assert!(matches!(element.as_ref(), Type::Simple(name) if name == "f32"));
                assert!(size.is_some()); // Fixed size
            } else {
                panic!("Expected array type");
            }
        } else {
            panic!("Expected typed pattern");
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_shared_let_in_function() {
    // Shared memory inside a function
    let src = r#"fn reduce_sum():
    shared let buffer: [i32; 512]
    buffer[0] = 1
"#;
    let module = parse(src).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "reduce_sum");
        // Check first statement is shared let
        if let Node::Let(let_stmt) = &func.body.statements[0] {
            assert!(let_stmt.storage_class.is_shared());
            assert!(let_stmt.mutability.is_mutable());
        } else {
            panic!("Expected let statement, got {:?}", func.body.statements[0]);
        }
    } else {
        panic!("Expected function");
    }
}
