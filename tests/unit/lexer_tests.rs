#![allow(unused_imports, dead_code, unused_variables)]
//! Comprehensive lexer unit tests

use simple_parser::lexer::Lexer;

use simple_parser::token::{FStringToken, Span, Token, TokenKind};

fn tokenize(source: &str) -> Vec<TokenKind> {
    let mut lexer = Lexer::new(source);
    lexer.tokenize().into_iter().map(|t| t.kind).collect()
}

fn tokenize_full(source: &str) -> Vec<Token> {
    let mut lexer = Lexer::new(source);
    lexer.tokenize()
}

// === Lexer Creation Tests ===

#[test]
fn test_lexer_new() {
    let lexer = Lexer::new("test");
    let _ = lexer; // Lexer should be created successfully
}

#[test]
fn test_lexer_empty_source() {
    let tokens = tokenize("");
    assert_eq!(tokens, vec![TokenKind::Eof]);
}

#[test]
fn test_lexer_whitespace_only() {
    let tokens = tokenize("   \t  ");
    // Lexer may emit INDENT/DEDENT for whitespace-only lines
    assert!(tokens.last() == Some(&TokenKind::Eof));
}

// === Integer Literal Tests ===

#[test]
fn test_integer_zero() {
    assert_eq!(tokenize("0"), vec![TokenKind::Integer(0), TokenKind::Eof]);
}

#[test]
fn test_integer_single_digit() {
    assert_eq!(tokenize("5"), vec![TokenKind::Integer(5), TokenKind::Eof]);
}

#[test]
fn test_integer_multi_digit() {
    assert_eq!(
        tokenize("12345"),
        vec![TokenKind::Integer(12345), TokenKind::Eof]
    );
}

#[test]
fn test_integer_with_underscores() {
    assert_eq!(
        tokenize("1_000_000"),
        vec![TokenKind::Integer(1000000), TokenKind::Eof]
    );
}

#[test]
fn test_integer_negative_parsed_as_minus() {
    let tokens = tokenize("-42");
    assert_eq!(tokens[0], TokenKind::Minus);
    assert_eq!(tokens[1], TokenKind::Integer(42));
}

// === Hex Literal Tests ===

#[test]
fn test_hex_lowercase() {
    assert_eq!(
        tokenize("0xff"),
        vec![TokenKind::Integer(255), TokenKind::Eof]
    );
}

#[test]
fn test_hex_uppercase() {
    assert_eq!(
        tokenize("0XFF"),
        vec![TokenKind::Integer(255), TokenKind::Eof]
    );
}

#[test]
fn test_hex_mixed_case() {
    assert_eq!(
        tokenize("0xAbCd"),
        vec![TokenKind::Integer(0xABCD), TokenKind::Eof]
    );
}

#[test]
fn test_hex_with_underscores() {
    assert_eq!(
        tokenize("0xff_ff"),
        vec![TokenKind::Integer(0xFFFF), TokenKind::Eof]
    );
}

// === Binary Literal Tests ===

#[test]
fn test_binary_lowercase() {
    assert_eq!(
        tokenize("0b1010"),
        vec![TokenKind::Integer(10), TokenKind::Eof]
    );
}

#[test]
fn test_binary_uppercase() {
    assert_eq!(
        tokenize("0B1111"),
        vec![TokenKind::Integer(15), TokenKind::Eof]
    );
}

#[test]
fn test_binary_with_underscores() {
    assert_eq!(
        tokenize("0b1111_0000"),
        vec![TokenKind::Integer(0xF0), TokenKind::Eof]
    );
}

// === Octal Literal Tests ===

#[test]
fn test_octal_lowercase() {
    assert_eq!(
        tokenize("0o77"),
        vec![TokenKind::Integer(63), TokenKind::Eof]
    );
}

#[test]
fn test_octal_uppercase() {
    assert_eq!(
        tokenize("0O77"),
        vec![TokenKind::Integer(63), TokenKind::Eof]
    );
}

#[test]
fn test_octal_with_underscores() {
    assert_eq!(
        tokenize("0o7_7_7"),
        vec![TokenKind::Integer(511), TokenKind::Eof]
    );
}

// === Float Literal Tests ===

#[test]
fn test_float_simple() {
    assert_eq!(
        tokenize("3.14"),
        vec![TokenKind::Float(3.14), TokenKind::Eof]
    );
}

#[test]
fn test_float_leading_zero() {
    assert_eq!(tokenize("0.5"), vec![TokenKind::Float(0.5), TokenKind::Eof]);
}

#[test]
fn test_float_with_exponent_lowercase() {
    assert_eq!(
        tokenize("1e10"),
        vec![TokenKind::Float(1e10), TokenKind::Eof]
    );
}

#[test]
fn test_float_with_exponent_uppercase() {
    assert_eq!(
        tokenize("1E10"),
        vec![TokenKind::Float(1e10), TokenKind::Eof]
    );
}

#[test]
fn test_float_with_negative_exponent() {
    assert_eq!(
        tokenize("2.5E-3"),
        vec![TokenKind::Float(2.5e-3), TokenKind::Eof]
    );
}

#[test]
fn test_float_with_positive_exponent() {
    assert_eq!(
        tokenize("1.5e+2"),
        vec![TokenKind::Float(1.5e2), TokenKind::Eof]
    );
}

#[test]
fn test_float_with_underscores() {
    assert_eq!(
        tokenize("1_000.5"),
        vec![TokenKind::Float(1000.5), TokenKind::Eof]
    );
}

// === String Literal Tests ===

#[test]
fn test_string_empty() {
    assert_eq!(
        tokenize(r#""""#),
        vec![TokenKind::FString(vec![]), TokenKind::Eof]
    );
}

#[test]
fn test_string_simple() {
    assert_eq!(
        tokenize(r#""hello""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello".to_string())]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_string_escape_newline() {
    assert_eq!(
        tokenize(r#""hello\nworld""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello\nworld".to_string())]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_string_escape_tab() {
    assert_eq!(
        tokenize(r#""hello\tworld""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello\tworld".to_string())]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_string_escape_carriage_return() {
    assert_eq!(
        tokenize(r#""hello\rworld""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello\rworld".to_string())]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_string_escape_backslash() {
    assert_eq!(
        tokenize(r#""hello\\world""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello\\world".to_string())]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_string_escape_quote() {
    assert_eq!(
        tokenize(r#""hello\"world""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello\"world".to_string())]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_string_escape_null() {
    assert_eq!(
        tokenize(r#""hello\0world""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello\0world".to_string())]),
            TokenKind::Eof
        ]
    );
}

// === Raw String Tests ===

#[test]
fn test_raw_string_empty() {
    assert_eq!(
        tokenize("''"),
        vec![TokenKind::RawString("".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_raw_string_simple() {
    assert_eq!(
        tokenize("'hello'"),
        vec![TokenKind::RawString("hello".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_raw_string_no_escape_processing() {
    assert_eq!(
        tokenize(r#"'hello\nworld'"#),
        vec![
            TokenKind::RawString("hello\\nworld".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_raw_string_no_interpolation() {
    assert_eq!(
        tokenize("'{name}'"),
        vec![TokenKind::RawString("{name}".to_string()), TokenKind::Eof]
    );
}

// === Interpolated String (FString) Tests ===

#[test]
fn test_fstring_with_interpolation() {
    assert_eq!(
        tokenize(r#""hello {name}""#),
        vec![
            TokenKind::FString(vec![
                FStringToken::Literal("hello ".to_string()),
                FStringToken::Expr("name".to_string()),
            ]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_fstring_multiple_interpolations() {
    assert_eq!(
        tokenize(r#""{x} + {y} = {z}""#),
        vec![
            TokenKind::FString(vec![
                FStringToken::Expr("x".to_string()),
                FStringToken::Literal(" + ".to_string()),
                FStringToken::Expr("y".to_string()),
                FStringToken::Literal(" = ".to_string()),
                FStringToken::Expr("z".to_string()),
            ]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_fstring_escaped_braces() {
    assert_eq!(
        tokenize(r#""literal {{braces}}""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("literal {braces}".to_string()),]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_fstring_complex_expression() {
    assert_eq!(
        tokenize(r#""{x + y}""#),
        vec![
            TokenKind::FString(vec![FStringToken::Expr("x + y".to_string()),]),
            TokenKind::Eof
        ]
    );
}

// === Boolean Literal Tests ===

#[test]
fn test_bool_true() {
    assert_eq!(
        tokenize("true"),
        vec![TokenKind::Bool(true), TokenKind::Eof]
    );
}

#[test]
fn test_bool_false() {
    assert_eq!(
        tokenize("false"),
        vec![TokenKind::Bool(false), TokenKind::Eof]
    );
}

// === Nil Literal Test ===

#[test]
fn test_nil_literal() {
    assert_eq!(tokenize("nil"), vec![TokenKind::Nil, TokenKind::Eof]);
}

// === Symbol Literal Tests ===

#[test]
fn test_symbol_simple() {
    assert_eq!(
        tokenize(":ok"),
        vec![TokenKind::Symbol("ok".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_symbol_with_underscore() {
    assert_eq!(
        tokenize(":error_code"),
        vec![TokenKind::Symbol("error_code".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_symbol_with_numbers() {
    assert_eq!(
        tokenize(":state123"),
        vec![TokenKind::Symbol("state123".to_string()), TokenKind::Eof]
    );
}

// === Identifier Tests ===

#[test]
fn test_identifier_simple() {
    assert_eq!(
        tokenize("foo"),
        vec![TokenKind::Identifier("foo".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_identifier_with_underscore_prefix() {
    assert_eq!(
        tokenize("_bar"),
        vec![TokenKind::Identifier("_bar".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_identifier_with_numbers() {
    assert_eq!(
        tokenize("baz123"),
        vec![TokenKind::Identifier("baz123".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_identifier_all_caps() {
    assert_eq!(
        tokenize("CONSTANT"),
        vec![
            TokenKind::Identifier("CONSTANT".to_string()),
            TokenKind::Eof
        ]
    );
}

// === Keyword Tests ===

#[test]
fn test_keyword_fn() {
    assert_eq!(tokenize("fn"), vec![TokenKind::Fn, TokenKind::Eof]);
}

#[test]
fn test_keyword_let() {
    assert_eq!(tokenize("let"), vec![TokenKind::Let, TokenKind::Eof]);
}

#[test]
fn test_keyword_mut() {
    assert_eq!(tokenize("mut"), vec![TokenKind::Mut, TokenKind::Eof]);
}

#[test]
fn test_keyword_if() {
    assert_eq!(tokenize("if"), vec![TokenKind::If, TokenKind::Eof]);
}

#[test]
fn test_keyword_elif() {
    assert_eq!(tokenize("elif"), vec![TokenKind::Elif, TokenKind::Eof]);
}

#[test]
fn test_keyword_else() {
    assert_eq!(tokenize("else"), vec![TokenKind::Else, TokenKind::Eof]);
}

#[test]
fn test_keyword_for() {
    assert_eq!(tokenize("for"), vec![TokenKind::For, TokenKind::Eof]);
}

#[test]
fn test_keyword_while() {
    assert_eq!(tokenize("while"), vec![TokenKind::While, TokenKind::Eof]);
}

#[test]
fn test_keyword_loop() {
    assert_eq!(tokenize("loop"), vec![TokenKind::Loop, TokenKind::Eof]);
}

#[test]
fn test_keyword_break() {
    assert_eq!(tokenize("break"), vec![TokenKind::Break, TokenKind::Eof]);
}

#[test]
fn test_keyword_continue() {
    assert_eq!(
        tokenize("continue"),
        vec![TokenKind::Continue, TokenKind::Eof]
    );
}

#[test]
fn test_keyword_return() {
    assert_eq!(tokenize("return"), vec![TokenKind::Return, TokenKind::Eof]);
}

#[test]
fn test_keyword_match() {
    assert_eq!(tokenize("match"), vec![TokenKind::Match, TokenKind::Eof]);
}

#[test]
fn test_keyword_struct() {
    assert_eq!(tokenize("struct"), vec![TokenKind::Struct, TokenKind::Eof]);
}

#[test]
fn test_keyword_class() {
    assert_eq!(tokenize("class"), vec![TokenKind::Class, TokenKind::Eof]);
}

#[test]
fn test_keyword_enum() {
    assert_eq!(tokenize("enum"), vec![TokenKind::Enum, TokenKind::Eof]);
}

#[test]
fn test_keyword_trait() {
    assert_eq!(tokenize("trait"), vec![TokenKind::Trait, TokenKind::Eof]);
}

#[test]
fn test_keyword_impl() {
    assert_eq!(tokenize("impl"), vec![TokenKind::Impl, TokenKind::Eof]);
}
