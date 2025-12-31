
// === Literal Tests ===

#[test]
fn test_integer_literals() {
    assert_eq!(tokenize("42"), vec![TokenKind::Integer(42), TokenKind::Eof]);
    assert_eq!(tokenize("0"), vec![TokenKind::Integer(0), TokenKind::Eof]);
    assert_eq!(
        tokenize("1_000_000"),
        vec![TokenKind::Integer(1000000), TokenKind::Eof]
    );
}

#[test]
fn test_hex_literals() {
    assert_eq!(
        tokenize("0xFF"),
        vec![TokenKind::Integer(255), TokenKind::Eof]
    );
    assert_eq!(
        tokenize("0x1A2B"),
        vec![TokenKind::Integer(0x1A2B), TokenKind::Eof]
    );
}

#[test]
fn test_binary_literals() {
    assert_eq!(
        tokenize("0b1010"),
        vec![TokenKind::Integer(10), TokenKind::Eof]
    );
    assert_eq!(
        tokenize("0b1111_0000"),
        vec![TokenKind::Integer(0xF0), TokenKind::Eof]
    );
}

#[test]
fn test_octal_literals() {
    assert_eq!(
        tokenize("0o77"),
        vec![TokenKind::Integer(63), TokenKind::Eof]
    );
}

#[test]
fn test_float_literals() {
    assert_eq!(
        tokenize("3.14"),
        vec![TokenKind::Float(3.14), TokenKind::Eof]
    );
    assert_eq!(
        tokenize("1.0e10"),
        vec![TokenKind::Float(1.0e10), TokenKind::Eof]
    );
    assert_eq!(
        tokenize("2.5E-3"),
        vec![TokenKind::Float(2.5e-3), TokenKind::Eof]
    );
}

#[test]
fn test_string_literals() {
    use crate::token::FStringToken;
    // Double-quoted strings are now FStrings (interpolated by default)
    assert_eq!(
        tokenize(r#""hello""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello".to_string())]),
            TokenKind::Eof
        ]
    );
    assert_eq!(
        tokenize(r#""hello\nworld""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello\nworld".to_string())]),
            TokenKind::Eof
        ]
    );
    assert_eq!(
        tokenize(r#""tab\there""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("tab\there".to_string())]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_raw_string_literals() {
    // Single-quoted strings are raw (no escape processing, no interpolation)
    assert_eq!(
        tokenize(r#"'hello'"#),
        vec![TokenKind::RawString("hello".to_string()), TokenKind::Eof]
    );
    // Backslashes are literal in raw strings
    assert_eq!(
        tokenize(r#"'hello\nworld'"#),
        vec![
            TokenKind::RawString("hello\\nworld".to_string()),
            TokenKind::Eof
        ]
    );
    // Braces are literal in raw strings (no interpolation)
    assert_eq!(
        tokenize(r#"'{name}'"#),
        vec![TokenKind::RawString("{name}".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_interpolated_strings() {
    use crate::token::FStringToken;
    // Test interpolation in double-quoted strings
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
    // Test escaped braces
    assert_eq!(
        tokenize(r#""literal {{braces}}""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("literal {braces}".to_string()),]),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_bool_literals() {
    assert_eq!(
        tokenize("true"),
        vec![TokenKind::Bool(true), TokenKind::Eof]
    );
    assert_eq!(
        tokenize("false"),
        vec![TokenKind::Bool(false), TokenKind::Eof]
    );
}

#[test]
fn test_nil_literal() {
    assert_eq!(tokenize("nil"), vec![TokenKind::Nil, TokenKind::Eof]);
}

#[test]
fn test_symbol_literals() {
    assert_eq!(
        tokenize(":ok"),
        vec![TokenKind::Symbol("ok".to_string()), TokenKind::Eof]
    );
    assert_eq!(
        tokenize(":error_code"),
        vec![TokenKind::Symbol("error_code".to_string()), TokenKind::Eof]
    );
}

// === Identifier and Keyword Tests ===

#[test]
fn test_identifiers() {
    assert_eq!(
        tokenize("foo"),
        vec![TokenKind::Identifier("foo".to_string()), TokenKind::Eof]
    );
    assert_eq!(
        tokenize("_bar"),
        vec![TokenKind::Identifier("_bar".to_string()), TokenKind::Eof]
    );
    assert_eq!(
        tokenize("baz123"),
        vec![TokenKind::Identifier("baz123".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_keywords() {
    assert_eq!(tokenize("fn"), vec![TokenKind::Fn, TokenKind::Eof]);
    assert_eq!(tokenize("let"), vec![TokenKind::Let, TokenKind::Eof]);
    assert_eq!(tokenize("if"), vec![TokenKind::If, TokenKind::Eof]);
    assert_eq!(tokenize("else"), vec![TokenKind::Else, TokenKind::Eof]);
    assert_eq!(tokenize("for"), vec![TokenKind::For, TokenKind::Eof]);
    assert_eq!(tokenize("while"), vec![TokenKind::While, TokenKind::Eof]);
    assert_eq!(tokenize("return"), vec![TokenKind::Return, TokenKind::Eof]);
    assert_eq!(tokenize("struct"), vec![TokenKind::Struct, TokenKind::Eof]);
    assert_eq!(tokenize("class"), vec![TokenKind::Class, TokenKind::Eof]);
    assert_eq!(tokenize("trait"), vec![TokenKind::Trait, TokenKind::Eof]);
    assert_eq!(tokenize("impl"), vec![TokenKind::Impl, TokenKind::Eof]);
    assert_eq!(tokenize("actor"), vec![TokenKind::Actor, TokenKind::Eof]);
    assert_eq!(tokenize("spawn"), vec![TokenKind::Spawn, TokenKind::Eof]);
}

