//! Parser crate integration tests
//! Tests Lexer, Parser, AST nodes, Token, and diagnostic functions
//! Focus: Public function coverage for simple_parser

#![allow(unused_imports, unused_variables)]

use simple_parser::{
    ast::{BinOp, Expr, Node, Pattern, PointerKind, Type as AstType, UnaryOp, MoveMode, Argument},
    diagnostic::{Diagnostic, Severity},
    error::ParseError,
    DocItem, DocItemKind, ModuleDocs,
    lexer::Lexer,
    parser::Parser,
    token::{Token, TokenKind, Span},
};

// =============================================================================
// Lexer Tests
// =============================================================================

#[test]
fn test_lexer_new() {
    let lexer = Lexer::new("main = 42");
    let _ = lexer;
}

#[test]
fn test_lexer_tokenize_integer() {
    let mut lexer = Lexer::new("42");
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty());
}

#[test]
fn test_lexer_tokenize_identifier() {
    let mut lexer = Lexer::new("main");
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty());
}

#[test]
fn test_lexer_tokenize_string() {
    let mut lexer = Lexer::new("\"hello\"");
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty());
}

#[test]
fn test_lexer_tokenize_operators() {
    let operators = ["+", "-", "*", "/", "==", "!=", "<", ">", "<=", ">="];
    for op in operators {
        let mut lexer = Lexer::new(op);
        let tokens = lexer.tokenize();
        assert!(!tokens.is_empty(), "Failed for: {}", op);
    }
}

#[test]
fn test_lexer_tokenize_keywords() {
    let keywords = ["fn", "let", "if", "else", "while", "for", "return", "class", "struct"];
    for kw in keywords {
        let mut lexer = Lexer::new(kw);
        let tokens = lexer.tokenize();
        assert!(!tokens.is_empty(), "Failed for: {}", kw);
    }
}

#[test]
fn test_lexer_tokenize_indentation() {
    let source = "if true:\n    return 1";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    let has_indent = tokens.iter().any(|t| matches!(t.kind, TokenKind::Indent));
    let _ = has_indent;
}

#[test]
fn test_lexer_tokenize_comment() {
    let mut lexer = Lexer::new("# this is a comment\nmain = 1");
    let tokens = lexer.tokenize();
    let _ = tokens;
}

#[test]
fn test_lexer_tokenize_multiline() {
    let source = "a = 1\nb = 2\nc = 3";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty());
}

#[test]
fn test_lexer_tokenize_empty() {
    let mut lexer = Lexer::new("");
    let tokens = lexer.tokenize();
    let _ = tokens;
}

#[test]
fn test_lexer_tokenize_float() {
    let mut lexer = Lexer::new("3.15159");
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty());
}

#[test]
fn test_lexer_tokenize_bool() {
    for s in ["true", "false"] {
        let mut lexer = Lexer::new(s);
        let tokens = lexer.tokenize();
        assert!(!tokens.is_empty());
    }
}

// =============================================================================
// Parser Tests
// =============================================================================

#[test]
fn test_parser_new() {
    let parser = Parser::new("main = 42");
    let _ = parser;
}

#[test]
fn test_parser_parse_simple() {
    let mut parser = Parser::new("main = 42");
    let result = parser.parse();
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
}

#[test]
fn test_parser_parse_function() {
    let source = "fn add(a: i64, b: i64) -> i64:\n    return a + b";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_parse_if() {
    let source = "if x > 0:\n    return 1\nelse:\n    return 0";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_parse_arithmetic() {
    let expressions = ["1 + 2", "3 - 4", "5 * 6", "7 / 8", "(1 + 2) * 3"];
    for expr in expressions {
        let source = format!("x = {}", expr);
        let mut parser = Parser::new(&source);
        let result = parser.parse();
        let _ = result;
    }
}

#[test]
fn test_parser_parse_comparison() {
    let comparisons = ["1 < 2", "3 > 4", "5 == 6", "7 != 8", "9 <= 10", "11 >= 12"];
    for cmp in comparisons {
        let source = format!("x = {}", cmp);
        let mut parser = Parser::new(&source);
        let result = parser.parse();
        let _ = result;
    }
}

#[test]
fn test_parser_parse_class() {
    let source = "class Point:\n    x: i64\n    y: i64";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_parse_struct() {
    let source = "struct Point:\n    x: i64\n    y: i64";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_parse_while() {
    let source = "while x > 0:\n    x = x - 1";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_parse_for() {
    let source = "for i in range(10):\n    print(i)";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_parse_match() {
    let source = "match x:\n    case 1:\n        return \"one\"\n    case _:\n        return \"other\"";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_parse_import() {
    let source = "import std.io";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_parse_use() {
    let source = "use std.*";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

#[test]
fn test_parser_syntax_error() {
    let source = "@#$%^&";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

// =============================================================================
// Token Tests
// =============================================================================

#[test]
fn test_token_kind_integer() {
    let kind = TokenKind::Integer(42);
    match kind {
        TokenKind::Integer(n) => assert_eq!(n, 42),
        _ => panic!("Expected Integer"),
    }
}

#[test]
fn test_token_kind_float() {
    let kind = TokenKind::Float(3.15);
    match kind {
        TokenKind::Float(f) => assert!((f - 3.15).abs() < 0.001),
        _ => panic!("Expected Float"),
    }
}

#[test]
fn test_token_kind_string() {
    let kind = TokenKind::String("hello".to_string());
    match kind {
        TokenKind::String(s) => assert_eq!(s, "hello"),
        _ => panic!("Expected String"),
    }
}

#[test]
fn test_token_kind_identifier() {
    use simple_parser::token::NamePattern;
    let kind = TokenKind::Identifier {
        name: "main".to_string(),
        pattern: NamePattern::Immutable,
    };
    match kind {
        TokenKind::Identifier { name, .. } => assert_eq!(name, "main"),
        _ => panic!("Expected Identifier"),
    }
}

#[test]
fn test_token_new() {
    let span = Span { start: 0, end: 2, line: 1, column: 0 };
    let token = Token::new(TokenKind::Integer(42), span, "42".to_string());
    assert_eq!(token.lexeme, "42");
}

#[test]
fn test_token_debug() {
    let span = Span { start: 0, end: 2, line: 1, column: 0 };
    let token = Token::new(TokenKind::Integer(42), span, "42".to_string());
    let debug = format!("{:?}", token);
    assert!(!debug.is_empty());
}

#[test]
fn test_span_fields() {
    let span = Span { start: 0, end: 10, line: 1, column: 5 };
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 10);
    assert_eq!(span.line, 1);
    assert_eq!(span.column, 5);
}

// =============================================================================
// AST Expr Tests
// =============================================================================

#[test]
fn test_expr_integer() {
    let expr = Expr::Integer(42);
    match expr {
        Expr::Integer(n) => assert_eq!(n, 42),
        _ => panic!("Expected Integer"),
    }
}

#[test]
fn test_expr_float() {
    let expr = Expr::Float(3.15);
    match expr {
        Expr::Float(f) => assert!((f - 3.15).abs() < 0.001),
        _ => panic!("Expected Float"),
    }
}

#[test]
fn test_expr_bool() {
    let expr = Expr::Bool(true);
    match expr {
        Expr::Bool(b) => assert!(b),
        _ => panic!("Expected Bool"),
    }
}

#[test]
fn test_expr_string() {
    let expr = Expr::String("test".to_string());
    match expr {
        Expr::String(s) => assert_eq!(s, "test"),
        _ => panic!("Expected String"),
    }
}

#[test]
fn test_expr_identifier() {
    let expr = Expr::Identifier("x".to_string());
    match expr {
        Expr::Identifier(name) => assert_eq!(name, "x"),
        _ => panic!("Expected Identifier"),
    }
}

#[test]
fn test_expr_nil() {
    let expr = Expr::Nil;
    assert!(matches!(expr, Expr::Nil));
}

#[test]
fn test_expr_binary() {
    let expr = Expr::Binary {
        left: Box::new(Expr::Integer(1)),
        right: Box::new(Expr::Integer(2)),
        op: BinOp::Add,
    };
    match expr {
        Expr::Binary { op, .. } => assert_eq!(op, BinOp::Add),
        _ => panic!("Expected Binary"),
    }
}

#[test]
fn test_expr_unary() {
    let expr = Expr::Unary {
        operand: Box::new(Expr::Integer(42)),
        op: UnaryOp::Neg,
    };
    match expr {
        Expr::Unary { op, .. } => assert_eq!(op, UnaryOp::Neg),
        _ => panic!("Expected Unary"),
    }
}

#[test]
fn test_expr_call() {
    let expr = Expr::Call {
        callee: Box::new(Expr::Identifier("print".to_string())),
        args: vec![Argument { name: None, value: Expr::String("hello".to_string()), span: Span::new(0,0,0,0), label: None }],
    };
    match expr {
        Expr::Call { args, .. } => assert_eq!(args.len(), 1),
        _ => panic!("Expected Call"),
    }
}

#[test]
fn test_expr_if() {
    let expr = Expr::If {
        condition: Box::new(Expr::Bool(true)),
        then_branch: Box::new(Expr::Integer(1)),
        else_branch: Some(Box::new(Expr::Integer(0))),
    };
    match expr {
        Expr::If { else_branch, .. } => assert!(else_branch.is_some()),
        _ => panic!("Expected If"),
    }
}

#[test]
fn test_expr_lambda() {
    let expr = Expr::Lambda {
        params: vec![],
        body: Box::new(Expr::Integer(42)),
        move_mode: MoveMode::Copy,
    };
    match expr {
        Expr::Lambda { body, .. } => {
            assert!(matches!(*body, Expr::Integer(42)));
        }
        _ => panic!("Expected Lambda"),
    }
}

#[test]
fn test_expr_array() {
    let expr = Expr::Array(vec![
        Expr::Integer(1),
        Expr::Integer(2),
        Expr::Integer(3),
    ]);
    match expr {
        Expr::Array(items) => assert_eq!(items.len(), 3),
        _ => panic!("Expected Array"),
    }
}

#[test]
fn test_expr_tuple() {
    let expr = Expr::Tuple(vec![
        Expr::Integer(1),
        Expr::String("a".to_string()),
    ]);
    match expr {
        Expr::Tuple(items) => assert_eq!(items.len(), 2),
        _ => panic!("Expected Tuple"),
    }
}

#[test]
fn test_expr_dict() {
    let expr = Expr::Dict(vec![
        (Expr::String("a".to_string()), Expr::Integer(1)),
    ]);
    match expr {
        Expr::Dict(pairs) => {
            assert_eq!(pairs.len(), 1);
        }
        _ => panic!("Expected Dict"),
    }
}

#[test]
fn test_expr_index() {
    let expr = Expr::Index {
        receiver: Box::new(Expr::Identifier("arr".to_string())),
        index: Box::new(Expr::Integer(0)),
    };
    match expr {
        Expr::Index { .. } => {}
        _ => panic!("Expected Index"),
    }
}

#[test]
fn test_expr_field_access() {
    let expr = Expr::FieldAccess {
        receiver: Box::new(Expr::Identifier("obj".to_string())),
        field: "field".to_string(),
    };
    match expr {
        Expr::FieldAccess { field, .. } => assert_eq!(field, "field"),
        _ => panic!("Expected FieldAccess"),
    }
}

// =============================================================================
// BinOp Tests
// =============================================================================

#[test]
fn test_binop_variants() {
    let ops = [
        BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div,
        BinOp::Eq, BinOp::NotEq, BinOp::Lt, BinOp::LtEq, BinOp::Gt, BinOp::GtEq,
        BinOp::And, BinOp::Or,
    ];
    for op in ops {
        let debug = format!("{:?}", op);
        assert!(!debug.is_empty());
    }
}

// =============================================================================
// UnaryOp Tests
// =============================================================================

#[test]
fn test_unaryop_variants() {
    let ops = [UnaryOp::Neg, UnaryOp::Not];
    for op in ops {
        let debug = format!("{:?}", op);
        assert!(!debug.is_empty());
    }
}

// =============================================================================
// Pattern Tests
// =============================================================================

#[test]
fn test_pattern_wildcard() {
    let pat = Pattern::Wildcard;
    assert!(matches!(pat, Pattern::Wildcard));
}

#[test]
fn test_pattern_identifier() {
    let pat = Pattern::Identifier("x".to_string());
    match pat {
        Pattern::Identifier(name) => assert_eq!(name, "x"),
        _ => panic!("Expected Identifier"),
    }
}

#[test]
fn test_pattern_literal() {
    let pat = Pattern::Literal(Box::new(Expr::Integer(42)));
    match pat {
        Pattern::Literal(_) => {}
        _ => panic!("Expected Literal"),
    }
}

#[test]
fn test_pattern_tuple() {
    let pat = Pattern::Tuple(vec![
        Pattern::Identifier("a".to_string()),
        Pattern::Identifier("b".to_string()),
    ]);
    match pat {
        Pattern::Tuple(items) => assert_eq!(items.len(), 2),
        _ => panic!("Expected Tuple"),
    }
}

// =============================================================================
// AstType Tests
// =============================================================================

#[test]
fn test_ast_type_simple() {
    let ty = AstType::Simple("i64".to_string());
    match ty {
        AstType::Simple(name) => assert_eq!(name, "i64"),
        _ => panic!("Expected Simple"),
    }
}

#[test]
fn test_ast_type_array() {
    let ty = AstType::Array {
        element: Box::new(AstType::Simple("i64".to_string())),
        size: None,
    };
    match ty {
        AstType::Array { .. } => {}
        _ => panic!("Expected Array"),
    }
}

#[test]
fn test_ast_type_tuple() {
    let ty = AstType::Tuple(vec![
        AstType::Simple("i64".to_string()),
        AstType::Simple("str".to_string()),
    ]);
    match ty {
        AstType::Tuple(items) => assert_eq!(items.len(), 2),
        _ => panic!("Expected Tuple"),
    }
}

#[test]
fn test_ast_type_function() {
    let ty = AstType::Function {
        params: vec![AstType::Simple("i64".to_string())],
        ret: Some(Box::new(AstType::Simple("bool".to_string()))),
    };
    match ty {
        AstType::Function { params, .. } => assert_eq!(params.len(), 1),
        _ => panic!("Expected Function"),
    }
}

#[test]
fn test_ast_type_optional() {
    let ty = AstType::Optional(Box::new(AstType::Simple("i64".to_string())));
    match ty {
        AstType::Optional(_) => {}
        _ => panic!("Expected Optional"),
    }
}

#[test]
fn test_ast_type_union() {
    let ty = AstType::Union(vec![
        AstType::Simple("i64".to_string()),
        AstType::Simple("str".to_string()),
    ]);
    match ty {
        AstType::Union(types) => assert_eq!(types.len(), 2),
        _ => panic!("Expected Union"),
    }
}

// =============================================================================
// PointerKind Tests
// =============================================================================

#[test]
fn test_pointer_kind_variants() {
    let kinds = [
        PointerKind::Unique,
        PointerKind::Shared,
        PointerKind::Weak,
        PointerKind::Borrow,
        PointerKind::BorrowMut,
    ];
    for kind in kinds {
        let debug = format!("{:?}", kind);
        assert!(!debug.is_empty());
    }
}

// =============================================================================
// Diagnostic Tests
// =============================================================================

#[test]
fn test_diagnostic_error() {
    let diag = Diagnostic::error("Test error");
    assert_eq!(diag.message, "Test error");
    assert_eq!(diag.severity, Severity::Error);
}

#[test]
fn test_diagnostic_warning() {
    let diag = Diagnostic::warning("Test warning");
    assert_eq!(diag.message, "Test warning");
    assert_eq!(diag.severity, Severity::Warning);
}

#[test]
fn test_severity_variants() {
    let levels = [
        Severity::Error,
        Severity::Warning,
        Severity::Note,
        Severity::Help,
    ];
    for level in levels {
        let debug = format!("{:?}", level);
        assert!(!debug.is_empty());
    }
}

// =============================================================================
// ParseError Tests
// =============================================================================

#[test]
fn test_parse_error_unexpected_token() {
    let span = Span { start: 0, end: 1, line: 1, column: 0 };
    let err = ParseError::UnexpectedToken {
        expected: "identifier".to_string(),
        found: "number".to_string(),
        span,
    };
    let display = format!("{}", err);
    assert!(!display.is_empty());
}

// =============================================================================
// DocGen Tests
// =============================================================================

#[test]
fn test_doc_item_kind_variants() {
    let kinds = [
        DocItemKind::Function,
        DocItemKind::Class,
        DocItemKind::Struct,
        DocItemKind::Enum,
        DocItemKind::Trait,
    ];
    for kind in kinds {
        let debug = format!("{:?}", kind);
        assert!(!debug.is_empty());
    }
}

#[test]
fn test_module_docs_default() {
    let docs = ModuleDocs::default();
    assert!(docs.items.is_empty());
}

// =============================================================================
// Argument Tests
// =============================================================================

#[test]
fn test_argument_positional() {
    let arg = Argument {
        name: None,
        value: Expr::Integer(42),
        span: Span::new(0, 0, 0, 0),
        label: None,
    };
    assert!(arg.name.is_none());
}

#[test]
fn test_argument_named() {
    let arg = Argument {
        name: Some("x".to_string()),
        value: Expr::Integer(42),
        span: Span::new(0, 0, 0, 0),
        label: None,
    };
    assert_eq!(arg.name, Some("x".to_string()));
}

// =============================================================================
// MoveMode Tests
// =============================================================================

#[test]
fn test_move_mode_variants() {
    let modes = [MoveMode::Move, MoveMode::Copy];
    for mode in modes {
        let debug = format!("{:?}", mode);
        assert!(!debug.is_empty());
    }
}

#[test]
fn test_move_mode_is_move() {
    assert!(MoveMode::Move.is_move());
    assert!(!MoveMode::Copy.is_move());
}
