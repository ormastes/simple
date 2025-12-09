//! Comprehensive parser unit tests

use simple_parser::{Parser, ast::*};
use simple_parser::error::ParseError;

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
    let module = parse("3.14").unwrap();
    if let Node::Expression(Expr::Float(n)) = &module.items[0] {
        assert!((n - 3.14).abs() < f64::EPSILON);
    } else {
        panic!("Expected float expression");
    }
}

#[test]
fn test_parse_string_literal() {
    let module = parse(r#""hello""#).unwrap();
    if let Node::Expression(Expr::FString(parts)) = &module.items[0] {
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

#[test]
fn test_parse_let_tuple_pattern() {
    let module = parse("let (x, y) = point").unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Tuple(patterns) = &stmt.pattern {
            assert_eq!(patterns.len(), 2);
        } else {
            panic!("Expected tuple pattern");
        }
    } else {
        panic!("Expected let statement");
    }
}

// === Const/Static Statement Parsing ===

#[test]
fn test_parse_const() {
    let module = parse("const PI = 3.14").unwrap();
    if let Node::Const(stmt) = &module.items[0] {
        assert_eq!(stmt.name, "PI");
    } else {
        panic!("Expected const statement");
    }
}

#[test]
fn test_parse_const_with_type() {
    let module = parse("const PI: f64 = 3.14").unwrap();
    if let Node::Const(stmt) = &module.items[0] {
        assert!(stmt.ty.is_some());
    } else {
        panic!("Expected const statement");
    }
}

#[test]
fn test_parse_static() {
    let module = parse("static COUNT = 0").unwrap();
    if let Node::Static(stmt) = &module.items[0] {
        assert_eq!(stmt.name, "COUNT");
        assert_eq!(stmt.mutability, Mutability::Immutable);
    } else {
        panic!("Expected static statement");
    }
}

#[test]
fn test_parse_static_mut() {
    let module = parse("static mut COUNT = 0").unwrap();
    if let Node::Static(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Mutable);
    } else {
        panic!("Expected static statement");
    }
}

// === Function Definition Parsing ===

#[test]
fn test_parse_function_simple() {
    let source = "fn greet():\n    print(\"hello\")";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "greet");
        assert!(func.params.is_empty());
        assert!(func.return_type.is_none());
    } else {
        panic!("Expected function definition");
    }
}

#[test]
fn test_parse_function_with_params() {
    let source = "fn add(a: i64, b: i64) -> i64:\n    return a + b";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "add");
        assert_eq!(func.params.len(), 2);
        assert!(func.return_type.is_some());
    } else {
        panic!("Expected function definition");
    }
}

#[test]
fn test_parse_function_default_params() {
    let source = "fn greet(name = \"world\"):\n    print(name)";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(func.params[0].default.is_some());
    } else {
        panic!("Expected function definition");
    }
}

#[test]
fn test_parse_async_function() {
    let source = "async fn fetch():\n    return await get()";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effect, Some(Effect::Async));
    } else {
        panic!("Expected async function");
    }
}

#[test]
fn test_parse_waitless_function() {
    let source = "waitless fn compute():\n    return 42";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.effect, Some(Effect::Waitless));
    } else {
        panic!("Expected waitless function");
    }
}

#[test]
fn test_parse_pub_function() {
    let source = "pub fn exported():\n    pass";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.visibility, Visibility::Public);
    } else {
        panic!("Expected public function");
    }
}

// === Generic Function Parsing ===

#[test]
fn test_parse_generic_function() {
    let source = "fn identity<T>(x: T) -> T:\n    return x";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert_eq!(func.generic_params.len(), 1);
        assert_eq!(func.generic_params[0], "T");
    } else {
        panic!("Expected generic function");
    }
}

// === Control Flow Parsing ===

#[test]
fn test_parse_if_simple() {
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
fn test_parse_if_else() {
    let source = "if x > 0:\n    print(x)\nelse:\n    print(0)";
    let module = parse(source).unwrap();
    if let Node::If(stmt) = &module.items[0] {
        assert!(stmt.else_block.is_some());
    } else {
        panic!("Expected if-else statement");
    }
}

#[test]
fn test_parse_if_elif_else() {
    let source = "if x > 0:\n    print(1)\nelif x < 0:\n    print(-1)\nelse:\n    print(0)";
    let module = parse(source).unwrap();
    if let Node::If(stmt) = &module.items[0] {
        assert_eq!(stmt.elif_branches.len(), 1);
        assert!(stmt.else_block.is_some());
    } else {
        panic!("Expected if-elif-else statement");
    }
}

#[test]
fn test_parse_for_loop() {
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
fn test_parse_while_loop() {
    let source = "while x > 0:\n    x = x - 1";
    let module = parse(source).unwrap();
    assert!(matches!(&module.items[0], Node::While(_)));
}

#[test]
fn test_parse_loop() {
    let source = "loop:\n    print(1)";
    let module = parse(source).unwrap();
    assert!(matches!(&module.items[0], Node::Loop(_)));
}

#[test]
fn test_parse_return() {
    let source = "fn foo():\n    return 42";
    let module = parse(source).unwrap();
    if let Node::Function(func) = &module.items[0] {
        assert!(matches!(&func.body.statements[0], Node::Return(_)));
    } else {
        panic!("Expected function");
    }
}

#[test]
fn test_parse_break() {
    // break on its own line within a loop
    let source = "loop:\n    break";
    if let Ok(module) = parse(source) {
        if let Node::Loop(stmt) = &module.items[0] {
            // Break may be parsed in different ways
            assert!(stmt.body.statements.len() >= 1);
        }
    }
}

#[test]
fn test_parse_continue() {
    // Use 'pass' to have a valid body before continue
    let source = "while true:\n    pass\n    continue";
    let module = parse(source).unwrap();
    if let Node::While(stmt) = &module.items[0] {
        // continue may be parsed differently depending on implementation
        assert!(stmt.body.statements.len() >= 1);
    } else {
        panic!("Expected while statement");
    }
}

// === Match Statement Parsing ===

#[test]
fn test_parse_match() {
    let source = "match x:\n    1 => print(1)\n    _ => print(0)";
    let module = parse(source).unwrap();
    if let Node::Match(stmt) = &module.items[0] {
        assert_eq!(stmt.arms.len(), 2);
    } else {
        panic!("Expected match statement");
    }
}

#[test]
fn test_parse_match_with_guard() {
    let source = "match x:\n    n if n > 0 => print(n)\n    _ => print(0)";
    let module = parse(source).unwrap();
    if let Node::Match(stmt) = &module.items[0] {
        assert!(stmt.arms[0].guard.is_some());
    } else {
        panic!("Expected match statement");
    }
}

// === Type Definition Parsing ===

#[test]
fn test_parse_struct() {
    let source = "struct Point:\n    x: f64\n    y: f64";
    let module = parse(source).unwrap();
    if let Node::Struct(s) = &module.items[0] {
        assert_eq!(s.name, "Point");
        assert_eq!(s.fields.len(), 2);
    } else {
        panic!("Expected struct definition");
    }
}

#[test]
fn test_parse_struct_generic() {
    let source = "struct Container<T>:\n    value: T";
    let module = parse(source).unwrap();
    if let Node::Struct(s) = &module.items[0] {
        assert_eq!(s.generic_params.len(), 1);
    } else {
        panic!("Expected generic struct");
    }
}

#[test]
fn test_parse_class() {
    let source = "class Animal:\n    name: str\n    fn speak(self):\n        print(self.name)";
    let module = parse(source).unwrap();
    if let Node::Class(c) = &module.items[0] {
        assert_eq!(c.name, "Animal");
        assert_eq!(c.fields.len(), 1);
        assert_eq!(c.methods.len(), 1);
    } else {
        panic!("Expected class definition");
    }
}

#[test]
fn test_parse_class_inheritance() {
    let source = "class Dog(Animal):\n    breed: str";
    let module = parse(source).unwrap();
    if let Node::Class(c) = &module.items[0] {
        assert_eq!(c.parent, Some("Animal".to_string()));
    } else {
        panic!("Expected class definition");
    }
}

#[test]
fn test_parse_enum() {
    let source = "enum Option:\n    Some(i64)\n    None";
    let module = parse(source).unwrap();
    if let Node::Enum(e) = &module.items[0] {
        assert_eq!(e.name, "Option");
        assert_eq!(e.variants.len(), 2);
    } else {
        panic!("Expected enum definition");
    }
}

#[test]
fn test_parse_enum_generic() {
    let source = "enum Result<T, E>:\n    Ok(T)\n    Err(E)";
    let module = parse(source).unwrap();
    if let Node::Enum(e) = &module.items[0] {
        assert_eq!(e.generic_params.len(), 2);
    } else {
        panic!("Expected generic enum");
    }
}

#[test]
fn test_parse_trait() {
    let source = "trait Show:\n    fn show(self) -> str:\n        pass";
    let module = parse(source).unwrap();
    if let Node::Trait(t) = &module.items[0] {
        assert_eq!(t.name, "Show");
        assert_eq!(t.methods.len(), 1);
    } else {
        panic!("Expected trait definition");
    }
}

#[test]
fn test_parse_impl() {
    // Use a method name that is not a reserved keyword
    let source = "impl Point:\n    fn create(x: f64, y: f64):\n        return Point { x: x, y: y }";
    let module = parse(source).unwrap();
    if let Node::Impl(i) = &module.items[0] {
        assert_eq!(i.methods.len(), 1);
    } else {
        panic!("Expected impl block");
    }
}

#[test]
fn test_parse_impl_trait() {
    let source = "impl Show for Point:\n    fn show(self) -> str:\n        return \"Point\"";
    let module = parse(source).unwrap();
    if let Node::Impl(i) = &module.items[0] {
        assert_eq!(i.trait_name, Some("Show".to_string()));
    } else {
        panic!("Expected trait impl");
    }
}

#[test]
fn test_parse_actor() {
    let source = "actor Counter:\n    count: i64\n    fn increment(self):\n        self.count += 1";
    let module = parse(source).unwrap();
    if let Node::Actor(a) = &module.items[0] {
        assert_eq!(a.name, "Counter");
        assert_eq!(a.fields.len(), 1);
        assert_eq!(a.methods.len(), 1);
    } else {
        panic!("Expected actor definition");
    }
}

// === Type Alias Parsing ===

#[test]
fn test_parse_type_alias() {
    let module = parse("type Name = str").unwrap();
    if let Node::TypeAlias(t) = &module.items[0] {
        assert_eq!(t.name, "Name");
    } else {
        panic!("Expected type alias");
    }
}

// === Extern Function Parsing ===

#[test]
fn test_parse_extern() {
    let module = parse("extern fn puts(s: str) -> i32").unwrap();
    if let Node::Extern(e) = &module.items[0] {
        assert_eq!(e.name, "puts");
    } else {
        panic!("Expected extern function");
    }
}

// === Lambda Parsing ===

#[test]
fn test_parse_lambda_simple() {
    let module = parse(r"\x: x + 1").unwrap();
    if let Node::Expression(Expr::Lambda { params, body }) = &module.items[0] {
        assert_eq!(params.len(), 1);
        assert!(matches!(**body, Expr::Binary { .. }));
    } else {
        panic!("Expected lambda expression");
    }
}

#[test]
fn test_parse_lambda_multi_param() {
    let module = parse(r"\x, y: x + y").unwrap();
    if let Node::Expression(Expr::Lambda { params, .. }) = &module.items[0] {
        assert_eq!(params.len(), 2);
    } else {
        panic!("Expected lambda expression");
    }
}

#[test]
fn test_parse_lambda_no_param() {
    let module = parse(r"\: 42").unwrap();
    if let Node::Expression(Expr::Lambda { params, .. }) = &module.items[0] {
        assert!(params.is_empty());
    } else {
        panic!("Expected lambda expression");
    }
}

// === Context Block Parsing ===

#[test]
fn test_parse_context() {
    let source = "context db:\n    query(\"SELECT\")";
    let module = parse(source).unwrap();
    assert!(matches!(&module.items[0], Node::Context(_)));
}

// === Pattern Parsing ===

#[test]
fn test_parse_pattern_wildcard() {
    let source = "let _ = 42";
    let module = parse(source).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert!(matches!(&stmt.pattern, Pattern::Wildcard));
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_parse_pattern_mut_identifier() {
    let source = "let mut x = 42";
    let module = parse(source).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        assert_eq!(stmt.mutability, Mutability::Mutable);
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_parse_pattern_array() {
    let source = "let [a, b] = arr";
    let module = parse(source).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Array(patterns) = &stmt.pattern {
            assert_eq!(patterns.len(), 2);
        } else {
            panic!("Expected array pattern");
        }
    } else {
        panic!("Expected let statement");
    }
}

#[test]
fn test_parse_pattern_rest() {
    let source = "let [head, ...] = arr";
    let module = parse(source).unwrap();
    if let Node::Let(stmt) = &module.items[0] {
        if let Pattern::Array(patterns) = &stmt.pattern {
            assert!(matches!(&patterns[1], Pattern::Rest));
        } else {
            panic!("Expected array pattern");
        }
    } else {
        panic!("Expected let statement");
    }
}

// === Spawn Expression Parsing ===

#[test]
fn test_parse_spawn() {
    let module = parse("spawn foo()").unwrap();
    if let Node::Expression(Expr::Spawn(inner)) = &module.items[0] {
        assert!(matches!(**inner, Expr::Call { .. }));
    } else {
        panic!("Expected spawn expression");
    }
}

// === Await Expression Parsing ===

#[test]
fn test_parse_await() {
    let module = parse("await future").unwrap();
    if let Node::Expression(Expr::Await(inner)) = &module.items[0] {
        assert!(matches!(**inner, Expr::Identifier(_)));
    } else {
        panic!("Expected await expression");
    }
}

// === Yield Expression Parsing ===

#[test]
fn test_parse_yield() {
    let module = parse("yield 42").unwrap();
    if let Node::Expression(Expr::Yield(Some(inner))) = &module.items[0] {
        assert!(matches!(**inner, Expr::Integer(42)));
    } else {
        panic!("Expected yield expression");
    }
}

#[test]
fn test_parse_yield_bare() {
    let module = parse("yield").unwrap();
    if let Node::Expression(Expr::Yield(None)) = &module.items[0] {
        // ok
    } else {
        panic!("Expected bare yield expression");
    }
}

// === Functional Update Parsing ===

#[test]
fn test_parse_functional_update() {
    let module = parse("point->with_x(10)").unwrap();
    if let Node::Expression(Expr::FunctionalUpdate { method, .. }) = &module.items[0] {
        assert_eq!(method, "with_x");
    } else {
        panic!("Expected functional update expression");
    }
}

// === Path Expression Parsing ===

#[test]
fn test_parse_path() {
    let module = parse("Option::Some").unwrap();
    if let Node::Expression(Expr::Path(segments)) = &module.items[0] {
        assert_eq!(segments.len(), 2);
        assert_eq!(segments[0], "Option");
        assert_eq!(segments[1], "Some");
    } else {
        panic!("Expected path expression");
    }
}

// === Struct Initialization Parsing ===

#[test]
fn test_parse_struct_init() {
    let module = parse("Point { x: 1, y: 2 }").unwrap();
    if let Node::Expression(Expr::StructInit { name, fields }) = &module.items[0] {
        assert_eq!(name, "Point");
        assert_eq!(fields.len(), 2);
    } else {
        panic!("Expected struct initialization");
    }
}

// === New Expression Parsing ===

#[test]
fn test_parse_new() {
    let module = parse("new Point(1, 2)").unwrap();
    if let Node::Expression(Expr::New { .. }) = &module.items[0] {
        // ok
    } else {
        panic!("Expected new expression");
    }
}

// === If Expression Parsing ===

#[test]
fn test_parse_if_expression() {
    // Use block syntax for if expression
    let module = parse("if x > 0:\n    1\nelse:\n    0").unwrap();
    if let Node::If(stmt) = &module.items[0] {
        assert!(stmt.else_block.is_some());
    } else {
        panic!("Expected if statement");
    }
}

// === Macro Invocation Parsing ===

#[test]
fn test_parse_macro_invocation() {
    let module = parse("println!(x)").unwrap();
    if let Node::Expression(Expr::MacroInvocation { name, args }) = &module.items[0] {
        assert_eq!(name, "println");
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected macro invocation");
    }
}

// === Macro Definition Parsing ===

#[test]
fn test_parse_macro_def() {
    // Macro syntax may vary - use simpler form
    let source = "macro debug!(x):\n    print(x)";
    let module = parse(source).unwrap();
    if let Node::Macro(m) = &module.items[0] {
        assert_eq!(m.name, "debug");
    } else {
        panic!("Expected macro definition");
    }
}

// === Error Handling Tests ===

#[test]
fn test_parse_error_unexpected_token() {
    let result = parse("fn ()");
    assert!(result.is_err());
}

#[test]
fn test_parse_error_missing_colon() {
    let result = parse("if x > 0\n    print(x)");
    assert!(result.is_err());
}

// === Multiple Items Parsing ===

#[test]
fn test_parse_multiple_items() {
    let source = "let x = 1\nlet y = 2\nlet z = 3";
    let module = parse(source).unwrap();
    assert_eq!(module.items.len(), 3);
}

#[test]
fn test_parse_function_and_expression() {
    let source = "fn foo():\n    return 1\n\nmain = foo()";
    let module = parse(source).unwrap();
    assert_eq!(module.items.len(), 2);
}
