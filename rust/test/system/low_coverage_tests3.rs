//! Low Coverage Type Tests Part 3
//! Tests for parser types, resolution types, and visibility types
#![allow(unused_imports)]

use std::path::PathBuf;

// =============================================================================
// Parser Token Coverage (parser/src/token.rs)
// =============================================================================

use simple_parser::{FStringToken, NumericSuffix, Span, Token, TokenKind};

#[test]
fn test_span_new() {
    let span = Span::new(0, 10, 1, 1);
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 10);
    assert_eq!(span.line, 1);
    assert_eq!(span.column, 1);
}

#[test]
fn test_span_equality() {
    let s1 = Span::new(0, 5, 1, 1);
    let s2 = Span::new(0, 5, 1, 1);
    let s3 = Span::new(5, 10, 2, 1);

    assert_eq!(s1, s2);
    assert_ne!(s1, s3);
}

#[test]
fn test_token_kind_literals() {
    let _ = TokenKind::Integer(42);
    let _ = TokenKind::Float(3.15);
    let _ = TokenKind::String("hello".to_string());
    let _ = TokenKind::Bool(true);
    let _ = TokenKind::Nil;
}

#[test]
fn test_token_kind_typed_literals() {
    let _ = TokenKind::TypedInteger(100, NumericSuffix::I64);
    let _ = TokenKind::TypedFloat(1.5, NumericSuffix::F32);
    let _ = TokenKind::TypedString("127.0.0.1".to_string(), "ip".to_string());
}

#[test]
fn test_token_kind_keywords() {
    let _ = TokenKind::Fn;
    let _ = TokenKind::Let;
    let _ = TokenKind::Mut;
    let _ = TokenKind::If;
    let _ = TokenKind::Else;
    let _ = TokenKind::For;
    let _ = TokenKind::While;
    let _ = TokenKind::Return;
    let _ = TokenKind::Match;
    let _ = TokenKind::Struct;
    let _ = TokenKind::Class;
    let _ = TokenKind::Enum;
    let _ = TokenKind::Trait;
    let _ = TokenKind::Impl;
    let _ = TokenKind::Actor;
    let _ = TokenKind::Pub;
    let _ = TokenKind::Import;
    let _ = TokenKind::Use;
    let _ = TokenKind::Async;
    let _ = TokenKind::Await;
}

#[test]
fn test_token_kind_operators() {
    let _ = TokenKind::Plus;
    let _ = TokenKind::Minus;
    let _ = TokenKind::Star;
    let _ = TokenKind::Slash;
    let _ = TokenKind::Eq; // ==
    let _ = TokenKind::NotEq; // !=
    let _ = TokenKind::Lt;
    let _ = TokenKind::LtEq; // <=
    let _ = TokenKind::Gt;
    let _ = TokenKind::GtEq; // >=
    let _ = TokenKind::And;
    let _ = TokenKind::Or;
    let _ = TokenKind::Not;
    let _ = TokenKind::DoubleStar; // **
    let _ = TokenKind::Parallel; // //
}

#[test]
fn test_token_kind_delimiters() {
    let _ = TokenKind::LParen;
    let _ = TokenKind::RParen;
    let _ = TokenKind::LBracket;
    let _ = TokenKind::RBracket;
    let _ = TokenKind::LBrace;
    let _ = TokenKind::RBrace;
    let _ = TokenKind::Colon;
    let _ = TokenKind::DoubleColon; // ::
    let _ = TokenKind::Comma;
    let _ = TokenKind::Dot;
    let _ = TokenKind::Arrow;
    let _ = TokenKind::FatArrow;
}

#[test]
fn test_token_creation() {
    let token = Token::new(TokenKind::Integer(42), Span::new(0, 2, 1, 1), "42".to_string());
    assert!(matches!(token.kind, TokenKind::Integer(42)));
}

#[test]
fn test_numeric_suffix_variants() {
    let _ = NumericSuffix::I8;
    let _ = NumericSuffix::I16;
    let _ = NumericSuffix::I32;
    let _ = NumericSuffix::I64;
    let _ = NumericSuffix::U8;
    let _ = NumericSuffix::U16;
    let _ = NumericSuffix::U32;
    let _ = NumericSuffix::U64;
    let _ = NumericSuffix::F32;
    let _ = NumericSuffix::F64;
    let _ = NumericSuffix::Unit("km".to_string());
}

#[test]
fn test_fstring_token_variants() {
    let _ = FStringToken::Literal("hello ".to_string());
    let _ = FStringToken::Expr("x + 1".to_string());
}

#[test]
fn test_fstring_token_in_tokenKind() {
    let parts = vec![
        FStringToken::Literal("Hello ".to_string()),
        FStringToken::Expr("name".to_string()),
        FStringToken::Literal("!".to_string()),
    ];
    let _ = TokenKind::FString(parts);
}

#[test]
fn test_token_kind_symbol() {
    let _ = TokenKind::Symbol("my_symbol".to_string());
}

#[test]
fn test_token_kind_raw_string() {
    let _ = TokenKind::RawString("raw content".to_string());
    let _ = TokenKind::TypedRawString("value".to_string(), "suffix".to_string());
}

// =============================================================================
// Resolution Coverage (dependency_tracker/src/resolution.rs - 0%)
// =============================================================================
// Visibility Coverage (dependency_tracker/src/visibility.rs - 3.70%)
// =============================================================================
// Type Crate Coverage (type/src/lib.rs)
// =============================================================================

use simple_type::{lean_infer, LeanExpr, LeanTy, Substitution, Type, TypeChecker, TypeError, TypeScheme};

#[test]
fn test_type_int() {
    let t = Type::Int;
    assert!(matches!(t, Type::Int));
}

#[test]
fn test_type_float() {
    let t = Type::Float;
    assert!(matches!(t, Type::Float));
}

#[test]
fn test_type_bool() {
    let t = Type::Bool;
    assert!(matches!(t, Type::Bool));
}

#[test]
fn test_type_str() {
    let t = Type::Str;
    assert!(matches!(t, Type::Str));
}

#[test]
fn test_type_nil() {
    let t = Type::Nil;
    assert!(matches!(t, Type::Nil));
}

#[test]
fn test_type_var() {
    let t = Type::Var(0);
    assert!(matches!(t, Type::Var(0)));
}

#[test]
fn test_type_function() {
    let t = Type::Function {
        params: vec![Type::Int],
        ret: Box::new(Type::Bool),
    };
    assert!(matches!(t, Type::Function { .. }));
}

#[test]
fn test_type_scheme_mono() {
    let scheme = TypeScheme::mono(Type::Int);
    assert!(scheme.vars.is_empty());
}

#[test]
fn test_type_scheme_poly() {
    let scheme = TypeScheme::poly(
        vec![0, 1],
        Type::Function {
            params: vec![Type::Var(0)],
            ret: Box::new(Type::Var(1)),
        },
    );
    assert_eq!(scheme.vars.len(), 2);
}

#[test]
fn test_substitution_new() {
    let sub = Substitution::new();
    let _ = sub;
}

#[test]
fn test_substitution_insert_and_get() {
    let mut sub = Substitution::new();
    sub.insert(0, Type::Int);
    assert!(sub.get(0).is_some());
    assert!(sub.get(1).is_none());
}

#[test]
fn test_type_apply_subst() {
    let mut sub = Substitution::new();
    sub.insert(0, Type::Int);

    let ty = Type::Var(0);
    let applied = ty.apply_subst(&sub);
    assert!(matches!(applied, Type::Int));
}

#[test]
fn test_type_contains_var() {
    let ty = Type::Function {
        params: vec![Type::Var(0)],
        ret: Box::new(Type::Int),
    };
    assert!(ty.contains_var(0));
    assert!(!ty.contains_var(1));
}

#[test]
fn test_type_checker_new() {
    let checker = TypeChecker::new();
    let _ = checker;
}

#[test]
fn test_type_error_mismatch() {
    let err = TypeError::Mismatch {
        expected: Type::Int,
        found: Type::Bool,
    };
    assert!(matches!(err, TypeError::Mismatch { .. }));
}

#[test]
fn test_type_error_undefined() {
    let err = TypeError::Undefined("x".to_string());
    assert!(matches!(err, TypeError::Undefined(_)));
}

#[test]
fn test_type_error_occurs_check() {
    let err = TypeError::OccursCheck {
        var_id: 0,
        ty: Type::Var(0),
    };
    assert!(matches!(err, TypeError::OccursCheck { .. }));
}

#[test]
fn test_type_error_other() {
    let err = TypeError::Other("some error".to_string());
    assert!(matches!(err, TypeError::Other(_)));
}

// =============================================================================
// Lean Type Inference Coverage (type/src/lib.rs)
// =============================================================================

#[test]
fn test_lean_ty_nat() {
    let t = LeanTy::Nat;
    assert!(matches!(t, LeanTy::Nat));
}

#[test]
fn test_lean_ty_bool() {
    let t = LeanTy::Bool;
    assert!(matches!(t, LeanTy::Bool));
}

#[test]
fn test_lean_ty_str() {
    let t = LeanTy::Str;
    assert!(matches!(t, LeanTy::Str));
}

#[test]
fn test_lean_ty_arrow() {
    let t = LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(LeanTy::Bool));
    assert!(matches!(t, LeanTy::Arrow(_, _)));
}

#[test]
fn test_lean_expr_lit_nat() {
    let e = LeanExpr::LitNat(42);
    assert!(matches!(e, LeanExpr::LitNat(42)));
}

#[test]
fn test_lean_expr_lit_bool() {
    let e = LeanExpr::LitBool(true);
    assert!(matches!(e, LeanExpr::LitBool(true)));
}

#[test]
fn test_lean_expr_lit_str() {
    let e = LeanExpr::LitStr("hello".to_string());
    assert!(matches!(e, LeanExpr::LitStr(_)));
}

#[test]
fn test_lean_expr_add() {
    let e = LeanExpr::Add(Box::new(LeanExpr::LitNat(1)), Box::new(LeanExpr::LitNat(2)));
    assert!(matches!(e, LeanExpr::Add(_, _)));
}

#[test]
fn test_lean_infer_nat() {
    let result = lean_infer(&LeanExpr::LitNat(42));
    assert_eq!(result, Some(LeanTy::Nat));
}

#[test]
fn test_lean_infer_bool() {
    let result = lean_infer(&LeanExpr::LitBool(true));
    assert_eq!(result, Some(LeanTy::Bool));
}

#[test]
fn test_lean_infer_str() {
    let result = lean_infer(&LeanExpr::LitStr("hello".to_string()));
    assert_eq!(result, Some(LeanTy::Str));
}

#[test]
fn test_lean_infer_add() {
    let e = LeanExpr::Add(Box::new(LeanExpr::LitNat(1)), Box::new(LeanExpr::LitNat(2)));
    let result = lean_infer(&e);
    assert_eq!(result, Some(LeanTy::Nat));
}
