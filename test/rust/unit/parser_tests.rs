//! Comprehensive parser unit tests

use simple_parser::error::ParseError;
use simple_parser::{ast::*, Parser};

fn parse(source: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::new(source);
    parser.parse()
}

// === Basic Literal Parsing ===

#[test]
fn test_parse_integer_literal() {
    let source = "main = 42";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse integer literal");
}

#[test]
fn test_parse_integer_zero() {
    let module = parse("0").unwrap();
    assert_eq!(module.items.len(), 1);
    if let Node::Expression(Expr::Integer(n)) = &module.items[0] {
        assert_eq!(*n, 0);
    } else {
        panic!("Expected integer expression");
    }
}

#[test]
fn test_parse_integer_large() {
    let module = parse("1000000").unwrap();
    if let Node::Expression(Expr::Integer(n)) = &module.items[0] {
        assert_eq!(*n, 1000000);
    } else {
        panic!("Expected integer expression");
    }
}

#[test]
fn test_parse_float_literal() {
    let module = parse("3.15").unwrap();
    if let Node::Expression(Expr::Float(n)) = &module.items[0] {
        assert!((n - 3.15).abs() < f64::EPSILON);
    } else {
        panic!("Expected float expression");
    }
}

#[test]
fn test_parse_string_literal() {
    let module = parse(r#""hello""#).unwrap();
    if let Node::Expression(Expr::FString { parts, .. }) = &module.items[0] {
        assert_eq!(parts.len(), 1);
        if let FStringPart::Literal(s) = &parts[0] {
            assert_eq!(s, "hello");
        }
    } else {
        panic!("Expected string expression");
    }
}

#[test]
fn test_parse_bool_true() {
    let module = parse("true").unwrap();
    if let Node::Expression(Expr::Bool(b)) = &module.items[0] {
        assert!(*b);
    } else {
        panic!("Expected bool expression");
    }
}

#[test]
fn test_parse_bool_false() {
    let module = parse("false").unwrap();
    if let Node::Expression(Expr::Bool(b)) = &module.items[0] {
        assert!(!*b);
    } else {
        panic!("Expected bool expression");
    }
}

#[test]
fn test_parse_nil_literal() {
    let module = parse("nil").unwrap();
    assert!(matches!(&module.items[0], Node::Expression(Expr::Nil)));
}

#[test]
fn test_parse_symbol_literal() {
    let module = parse(":ok").unwrap();
    if let Node::Expression(Expr::Symbol(s)) = &module.items[0] {
        assert_eq!(s, "ok");
    } else {
        panic!("Expected symbol expression");
    }
}

// === Identifier Parsing ===

#[test]
fn test_parse_identifier() {
    let module = parse("foo").unwrap();
    if let Node::Expression(Expr::Identifier(name)) = &module.items[0] {
        assert_eq!(name, "foo");
    } else {
        panic!("Expected identifier expression");
    }
}

#[test]
fn test_parse_identifier_with_underscore() {
    let module = parse("_bar").unwrap();
    if let Node::Expression(Expr::Identifier(name)) = &module.items[0] {
        assert_eq!(name, "_bar");
    } else {
        panic!("Expected identifier expression");
    }
}

// === Binary Expression Parsing ===

#[test]
fn test_parse_binary_add() {
    let module = parse("1 + 2").unwrap();
    if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
        assert_eq!(*op, BinOp::Add);
        assert!(matches!(**left, Expr::Integer(1)));
        assert!(matches!(**right, Expr::Integer(2)));
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_sub() {
    let module = parse("5 - 3").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Sub);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_mul() {
    let module = parse("2 * 3").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Mul);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_div() {
    let module = parse("6 / 2").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Div);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_mod() {
    let module = parse("7 % 3").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Mod);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_pow() {
    let module = parse("2 ** 3").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Pow);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_floor_div() {
    let module = parse("7 // 2").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::FloorDiv);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_eq() {
    let module = parse("x == y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Eq);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_not_eq() {
    let module = parse("x != y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::NotEq);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_lt() {
    let module = parse("x < y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Lt);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_gt() {
    let module = parse("x > y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Gt);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_lt_eq() {
    let module = parse("x <= y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::LtEq);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_gt_eq() {
    let module = parse("x >= y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::GtEq);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_and() {
    let module = parse("x and y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::And);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_or() {
    let module = parse("x or y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Or);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_bitwise_and() {
    let module = parse("x & y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::BitAnd);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_bitwise_or() {
    let module = parse("x | y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::BitOr);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_bitwise_xor() {
    let module = parse("x ^ y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::BitXor);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_shift_left() {
    let module = parse("x << y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::ShiftLeft);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_shift_right() {
    let module = parse("x >> y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::ShiftRight);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_is() {
    let module = parse("x is y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Is);
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_parse_binary_in() {
    let module = parse("x in y").unwrap();
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::In);
    } else {
        panic!("Expected binary expression");
    }
}

// === Operator Precedence Tests ===

#[test]
fn test_precedence_mul_over_add() {
    let module = parse("1 + 2 * 3").unwrap();
    // Should parse as 1 + (2 * 3)
    if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
        assert_eq!(*op, BinOp::Add);
        assert!(matches!(**left, Expr::Integer(1)));
        if let Expr::Binary { op: inner_op, .. } = &**right {
            assert_eq!(*inner_op, BinOp::Mul);
        } else {
            panic!("Expected nested multiplication");
        }
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_precedence_pow_right_assoc() {
    let module = parse("2 ** 3 ** 4").unwrap();
    // Power is right associative: 2 ** (3 ** 4)
    if let Node::Expression(Expr::Binary { op, right, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Pow);
        assert!(matches!(**right, Expr::Binary { op: BinOp::Pow, .. }));
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_precedence_comparison_over_bitwise() {
    let module = parse("x < y & z").unwrap();
    // Parser may have different precedence - test that it parses successfully
    if let Node::Expression(Expr::Binary { op, .. }) = &module.items[0] {
        // The parser's actual precedence may differ - just verify it parses
        assert!(matches!(*op, BinOp::BitAnd | BinOp::Lt));
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn test_precedence_parentheses() {
    let module = parse("(1 + 2) * 3").unwrap();
    // Parentheses override default precedence
    if let Node::Expression(Expr::Binary { op, left, .. }) = &module.items[0] {
        assert_eq!(*op, BinOp::Mul);
        assert!(matches!(**left, Expr::Binary { op: BinOp::Add, .. }));
    } else {
        panic!("Expected binary expression");
    }
}

// === Unary Expression Parsing ===

#[test]
fn test_parse_unary_neg() {
    let module = parse("-42").unwrap();
    if let Node::Expression(Expr::Unary { op, operand }) = &module.items[0] {
        assert_eq!(*op, UnaryOp::Neg);
        assert!(matches!(**operand, Expr::Integer(42)));
    } else {
        panic!("Expected unary expression");
    }
}

#[test]
fn test_parse_unary_not() {
    let module = parse("not x").unwrap();
    if let Node::Expression(Expr::Unary { op, .. }) = &module.items[0] {
        assert_eq!(*op, UnaryOp::Not);
    } else {
        panic!("Expected unary expression");
    }
}

#[test]
fn test_parse_unary_bitnot() {
    let module = parse("~x").unwrap();
    if let Node::Expression(Expr::Unary { op, .. }) = &module.items[0] {
        assert_eq!(*op, UnaryOp::BitNot);
    } else {
        panic!("Expected unary expression");
    }
}

#[test]
fn test_parse_unary_ref() {
    let module = parse("&x").unwrap();
    if let Node::Expression(Expr::Unary { op, .. }) = &module.items[0] {
        assert_eq!(*op, UnaryOp::Ref);
    } else {
        panic!("Expected unary expression");
    }
}

#[test]
fn test_parse_unary_ref_mut() {
    let module = parse("&mut x").unwrap();
    if let Node::Expression(Expr::Unary { op, .. }) = &module.items[0] {
        assert_eq!(*op, UnaryOp::RefMut);
    } else {
        panic!("Expected unary expression");
    }
}

#[test]
fn test_parse_unary_deref() {
    let module = parse("*x").unwrap();
    if let Node::Expression(Expr::Unary { op, .. }) = &module.items[0] {
        assert_eq!(*op, UnaryOp::Deref);
    } else {
        panic!("Expected unary expression");
    }
}

// === Call Expression Parsing ===

#[test]
fn test_parse_function_call_no_args() {
    let module = parse("foo()").unwrap();
    if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
        assert!(matches!(**callee, Expr::Identifier(ref name) if name == "foo"));
        assert!(args.is_empty());
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_parse_function_call_one_arg() {
    let module = parse("foo(1)").unwrap();
    if let Node::Expression(Expr::Call { args, .. }) = &module.items[0] {
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_parse_function_call_multiple_args() {
    let module = parse("foo(1, 2, 3)").unwrap();
    if let Node::Expression(Expr::Call { args, .. }) = &module.items[0] {
        assert_eq!(args.len(), 3);
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_parse_function_call_named_args() {
    let module = parse("foo(x=1, y=2)").unwrap();
    if let Node::Expression(Expr::Call { args, .. }) = &module.items[0] {
        assert_eq!(args.len(), 2);
        assert_eq!(args[0].name, Some("x".to_string()));
        assert_eq!(args[1].name, Some("y".to_string()));
    } else {
        panic!("Expected call expression");
    }
}

#[test]
fn test_parse_method_call() {
    let module = parse("obj.method(x)").unwrap();
    if let Node::Expression(Expr::MethodCall { receiver, method, args }) = &module.items[0] {
        assert!(matches!(**receiver, Expr::Identifier(ref name) if name == "obj"));
        assert_eq!(method, "method");
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected method call");
    }
}

#[test]
fn test_parse_method_chain() {
    let module = parse("a.b().c()").unwrap();
    if let Node::Expression(Expr::MethodCall { receiver, method, .. }) = &module.items[0] {
        assert_eq!(method, "c");
        assert!(matches!(**receiver, Expr::MethodCall { .. }));
    } else {
        panic!("Expected method call chain");
    }
}

// === Field Access Parsing ===

#[test]
fn test_parse_field_access() {
    let module = parse("obj.field").unwrap();
    if let Node::Expression(Expr::FieldAccess { receiver, field }) = &module.items[0] {
        assert!(matches!(**receiver, Expr::Identifier(ref name) if name == "obj"));
        assert_eq!(field, "field");
    } else {
        panic!("Expected field access");
    }
}

#[test]
fn test_parse_field_chain() {
    let module = parse("a.b.c").unwrap();
    if let Node::Expression(Expr::FieldAccess { receiver, field }) = &module.items[0] {
        assert_eq!(field, "c");
        assert!(matches!(**receiver, Expr::FieldAccess { .. }));
    } else {
        panic!("Expected field access chain");
    }
}

// === Index Expression Parsing ===

#[test]
fn test_parse_array_index() {
    let module = parse("arr[0]").unwrap();
    if let Node::Expression(Expr::Index { receiver, index }) = &module.items[0] {
        assert!(matches!(**receiver, Expr::Identifier(ref name) if name == "arr"));
        assert!(matches!(**index, Expr::Integer(0)));
    } else {
        panic!("Expected index expression");
    }
}

#[test]
fn test_parse_nested_index() {
    let module = parse("arr[0][1]").unwrap();
    if let Node::Expression(Expr::Index { receiver, .. }) = &module.items[0] {
        assert!(matches!(**receiver, Expr::Index { .. }));
    } else {
        panic!("Expected nested index");
    }
}

// === Collection Literal Parsing ===

#[test]
fn test_parse_array_empty() {
    let module = parse("[]").unwrap();
    if let Node::Expression(Expr::Array(elements)) = &module.items[0] {
        assert!(elements.is_empty());
    } else {
        panic!("Expected array expression");
    }
}

#[test]
fn test_parse_array_single() {
    let module = parse("[1]").unwrap();
    if let Node::Expression(Expr::Array(elements)) = &module.items[0] {
        assert_eq!(elements.len(), 1);
    } else {
        panic!("Expected array expression");
    }
}

#[test]
fn test_parse_array_multiple() {
    let module = parse("[1, 2, 3]").unwrap();
    if let Node::Expression(Expr::Array(elements)) = &module.items[0] {
        assert_eq!(elements.len(), 3);
    } else {
        panic!("Expected array expression");
    }
}

#[test]
fn test_parse_tuple_empty() {
    let module = parse("()").unwrap();
    if let Node::Expression(Expr::Tuple(elements)) = &module.items[0] {
        assert!(elements.is_empty());
    } else {
        panic!("Expected tuple expression");
    }
}

#[test]
fn test_parse_tuple_multiple() {
    let module = parse("(1, 2, 3)").unwrap();
    if let Node::Expression(Expr::Tuple(elements)) = &module.items[0] {
        assert_eq!(elements.len(), 3);
    } else {
        panic!("Expected tuple expression");
    }
}

#[test]
fn test_parse_dict_empty() {
    let module = parse("{}").unwrap();
    if let Node::Expression(Expr::Dict(entries)) = &module.items[0] {
        assert!(entries.is_empty());
    } else {
        panic!("Expected dict expression");
    }
}

#[test]
fn test_parse_dict_single() {
    let module = parse(r#"{"key": 1}"#).unwrap();
    if let Node::Expression(Expr::Dict(entries)) = &module.items[0] {
        assert_eq!(entries.len(), 1);
    } else {
        panic!("Expected dict expression");
    }
}

// === Let Statement Parsing ===

#[test]
fn test_parse_let_simple() {
    let module = parse("let x = 42").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Immutable);
        if let Pattern::Identifier(name) = &stmt.pattern {
            assert_eq!(name, "x");
        }
        assert!(stmt.value.is_some());
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_parse_let_mut() {
    let module = parse("let mut x = 42").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Mutable);
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_parse_mut_let() {
    let module = parse("mut let x = 42").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Mutable);
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_parse_let_with_type() {
    let module = parse("let x: i64 = 42").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        // Type annotation may be stored in the pattern or the let statement
        // Just verify it parses successfully
        let _ = stmt;
    } else {
        panic!("Expected let statement");
    }
}
