use super::*;
use pretty_assertions::assert_eq;

fn tokenize(source: &str) -> Vec<TokenKind> {
    let mut lexer = Lexer::new(source);
    lexer.tokenize().into_iter().map(|t| t.kind).collect()
}

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

// === Operator Tests ===

#[test]
fn test_arithmetic_operators() {
    assert_eq!(tokenize("+"), vec![TokenKind::Plus, TokenKind::Eof]);
    assert_eq!(tokenize("-"), vec![TokenKind::Minus, TokenKind::Eof]);
    assert_eq!(tokenize("*"), vec![TokenKind::Star, TokenKind::Eof]);
    assert_eq!(tokenize("/"), vec![TokenKind::Slash, TokenKind::Eof]);
    assert_eq!(tokenize("%"), vec![TokenKind::Percent, TokenKind::Eof]);
    assert_eq!(tokenize("**"), vec![TokenKind::DoubleStar, TokenKind::Eof]);
    assert_eq!(tokenize("//"), vec![TokenKind::DoubleSlash, TokenKind::Eof]);
}

#[test]
fn test_comparison_operators() {
    assert_eq!(tokenize("=="), vec![TokenKind::Eq, TokenKind::Eof]);
    assert_eq!(tokenize("!="), vec![TokenKind::NotEq, TokenKind::Eof]);
    assert_eq!(tokenize("<"), vec![TokenKind::Lt, TokenKind::Eof]);
    assert_eq!(tokenize(">"), vec![TokenKind::Gt, TokenKind::Eof]);
    assert_eq!(tokenize("<="), vec![TokenKind::LtEq, TokenKind::Eof]);
    assert_eq!(tokenize(">="), vec![TokenKind::GtEq, TokenKind::Eof]);
}

#[test]
fn test_assignment_operators() {
    assert_eq!(tokenize("="), vec![TokenKind::Assign, TokenKind::Eof]);
    assert_eq!(tokenize("+="), vec![TokenKind::PlusAssign, TokenKind::Eof]);
    assert_eq!(tokenize("-="), vec![TokenKind::MinusAssign, TokenKind::Eof]);
    assert_eq!(tokenize("*="), vec![TokenKind::StarAssign, TokenKind::Eof]);
    assert_eq!(tokenize("/="), vec![TokenKind::SlashAssign, TokenKind::Eof]);
}

#[test]
fn test_arrow_operators() {
    assert_eq!(tokenize("->"), vec![TokenKind::Arrow, TokenKind::Eof]);
    assert_eq!(tokenize("=>"), vec![TokenKind::FatArrow, TokenKind::Eof]);
}

#[test]
fn test_bitwise_operators() {
    assert_eq!(tokenize("&"), vec![TokenKind::Ampersand, TokenKind::Eof]);
    assert_eq!(tokenize("|"), vec![TokenKind::Pipe, TokenKind::Eof]);
    assert_eq!(tokenize("^"), vec![TokenKind::Caret, TokenKind::Eof]);
    assert_eq!(tokenize("~"), vec![TokenKind::Tilde, TokenKind::Eof]);
    assert_eq!(tokenize("<<"), vec![TokenKind::ShiftLeft, TokenKind::Eof]);
    assert_eq!(tokenize(">>"), vec![TokenKind::ShiftRight, TokenKind::Eof]);
}

// === Delimiter Tests ===

#[test]
fn test_delimiters() {
    assert_eq!(tokenize("("), vec![TokenKind::LParen, TokenKind::Eof]);
    assert_eq!(tokenize(")"), vec![TokenKind::RParen, TokenKind::Eof]);
    assert_eq!(tokenize("["), vec![TokenKind::LBracket, TokenKind::Eof]);
    assert_eq!(tokenize("]"), vec![TokenKind::RBracket, TokenKind::Eof]);
    assert_eq!(tokenize("{"), vec![TokenKind::LBrace, TokenKind::Eof]);
    assert_eq!(tokenize("}"), vec![TokenKind::RBrace, TokenKind::Eof]);
    assert_eq!(tokenize(","), vec![TokenKind::Comma, TokenKind::Eof]);
    assert_eq!(tokenize(":"), vec![TokenKind::Colon, TokenKind::Eof]);
    assert_eq!(tokenize("::"), vec![TokenKind::DoubleColon, TokenKind::Eof]);
    assert_eq!(tokenize("."), vec![TokenKind::Dot, TokenKind::Eof]);
    assert_eq!(tokenize(".."), vec![TokenKind::DoubleDot, TokenKind::Eof]);
    assert_eq!(tokenize("..."), vec![TokenKind::Ellipsis, TokenKind::Eof]);
}

// === Expression Tests ===

#[test]
fn test_simple_expression() {
    assert_eq!(
        tokenize("1 + 2"),
        vec![
            TokenKind::Integer(1),
            TokenKind::Plus,
            TokenKind::Integer(2),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_complex_expression() {
    assert_eq!(
        tokenize("x * (y + z)"),
        vec![
            TokenKind::Identifier("x".to_string()),
            TokenKind::Star,
            TokenKind::LParen,
            TokenKind::Identifier("y".to_string()),
            TokenKind::Plus,
            TokenKind::Identifier("z".to_string()),
            TokenKind::RParen,
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_function_call() {
    assert_eq!(
        tokenize("print(x, y)"),
        vec![
            TokenKind::Identifier("print".to_string()),
            TokenKind::LParen,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Comma,
            TokenKind::Identifier("y".to_string()),
            TokenKind::RParen,
            TokenKind::Eof,
        ]
    );
}

// === Indentation Tests ===

#[test]
fn test_indent_dedent() {
    let source = "if x:\n    y\nz";
    let tokens = tokenize(source);
    assert_eq!(
        tokens,
        vec![
            TokenKind::If,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Colon,
            TokenKind::Newline,
            TokenKind::Indent,
            TokenKind::Identifier("y".to_string()),
            TokenKind::Newline,
            TokenKind::Dedent,
            TokenKind::Identifier("z".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_nested_indent() {
    let source = "if a:\n    if b:\n        c\nd";
    let tokens = tokenize(source);
    assert_eq!(
        tokens,
        vec![
            TokenKind::If,
            TokenKind::Identifier("a".to_string()),
            TokenKind::Colon,
            TokenKind::Newline,
            TokenKind::Indent,
            TokenKind::If,
            TokenKind::Identifier("b".to_string()),
            TokenKind::Colon,
            TokenKind::Newline,
            TokenKind::Indent,
            TokenKind::Identifier("c".to_string()),
            TokenKind::Newline,
            TokenKind::Dedent,
            TokenKind::Dedent,
            TokenKind::Identifier("d".to_string()),
            TokenKind::Eof,
        ]
    );
}

// === Comment Tests ===

#[test]
fn test_line_comment() {
    assert_eq!(
        tokenize("x # comment\ny"),
        vec![
            TokenKind::Identifier("x".to_string()),
            TokenKind::Newline,
            TokenKind::Identifier("y".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_block_comment() {
    assert_eq!(
        tokenize("x /* comment */ y"),
        vec![
            TokenKind::Identifier("x".to_string()),
            TokenKind::Identifier("y".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_block_comment_multiline() {
    assert_eq!(
        tokenize("x /* multi\nline\ncomment */ y"),
        vec![
            TokenKind::Identifier("x".to_string()),
            TokenKind::Identifier("y".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_block_comment_nested() {
    assert_eq!(
        tokenize("x /* outer /* inner */ outer */ y"),
        vec![
            TokenKind::Identifier("x".to_string()),
            TokenKind::Identifier("y".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_block_comment_at_line_start() {
    assert_eq!(
        tokenize("/* comment */\nx"),
        vec![
            TokenKind::Identifier("x".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_doc_block_comment() {
    assert_eq!(
        tokenize("/** This is a doc comment */\nx"),
        vec![
            TokenKind::DocComment("This is a doc comment".to_string()),
            TokenKind::Newline,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_doc_block_comment_multiline() {
    assert_eq!(
        tokenize("/**\n * Line 1\n * Line 2\n */\nx"),
        vec![
            TokenKind::DocComment("Line 1\nLine 2".to_string()),
            TokenKind::Newline,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_doc_line_comment() {
    assert_eq!(
        tokenize("## This is a doc comment\nx"),
        vec![
            TokenKind::DocComment("This is a doc comment".to_string()),
            TokenKind::Newline,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Eof,
        ]
    );
}

// === Module System Keywords Tests ===

#[test]
fn test_module_keywords() {
    assert_eq!(tokenize("use"), vec![TokenKind::Use, TokenKind::Eof]);
    assert_eq!(tokenize("mod"), vec![TokenKind::Mod, TokenKind::Eof]);
    assert_eq!(tokenize("export"), vec![TokenKind::Export, TokenKind::Eof]);
    assert_eq!(tokenize("common"), vec![TokenKind::Common, TokenKind::Eof]);
    assert_eq!(tokenize("auto"), vec![TokenKind::Auto, TokenKind::Eof]);
    assert_eq!(tokenize("crate"), vec![TokenKind::Crate, TokenKind::Eof]);
}

#[test]
fn test_use_statement_tokens() {
    assert_eq!(
        tokenize("use crate.core.Option"),
        vec![
            TokenKind::Use,
            TokenKind::Crate,
            TokenKind::Dot,
            TokenKind::Identifier("core".to_string()),
            TokenKind::Dot,
            TokenKind::Identifier("Option".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_mod_declaration_tokens() {
    assert_eq!(
        tokenize("pub mod router"),
        vec![
            TokenKind::Pub,
            TokenKind::Mod,
            TokenKind::Identifier("router".to_string()),
            TokenKind::Eof,
        ]
    );
}

// === Function Definition Test ===

#[test]
fn test_function_definition() {
    let source = "fn add(a: i64, b: i64) -> i64:\n    return a + b";
    let tokens = tokenize(source);
    assert_eq!(
        tokens,
        vec![
            TokenKind::Fn,
            TokenKind::Identifier("add".to_string()),
            TokenKind::LParen,
            TokenKind::Identifier("a".to_string()),
            TokenKind::Colon,
            TokenKind::Identifier("i64".to_string()),
            TokenKind::Comma,
            TokenKind::Identifier("b".to_string()),
            TokenKind::Colon,
            TokenKind::Identifier("i64".to_string()),
            TokenKind::RParen,
            TokenKind::Arrow,
            TokenKind::Identifier("i64".to_string()),
            TokenKind::Colon,
            TokenKind::Newline,
            TokenKind::Indent,
            TokenKind::Return,
            TokenKind::Identifier("a".to_string()),
            TokenKind::Plus,
            TokenKind::Identifier("b".to_string()),
            TokenKind::Dedent, // DEDENT at EOF for remaining indentation
            TokenKind::Eof,
        ]
    );
}

// === String Unit Suffix Tests ===

#[test]
fn test_raw_string_unit_suffix() {
    // Raw string with unit suffix: 'value'_suffix
    assert_eq!(
        tokenize(r#"'127.0.0.1'_ip"#),
        vec![
            TokenKind::TypedRawString("127.0.0.1".to_string(), "ip".to_string()),
            TokenKind::Eof
        ]
    );

    assert_eq!(
        tokenize(r#"'/path/to/file'_file"#),
        vec![
            TokenKind::TypedRawString("/path/to/file".to_string(), "file".to_string()),
            TokenKind::Eof
        ]
    );

    // Raw string without suffix
    assert_eq!(
        tokenize(r#"'127.0.0.1'"#),
        vec![TokenKind::RawString("127.0.0.1".to_string()), TokenKind::Eof]
    );
}

#[test]
fn test_double_quoted_string_unit_suffix() {
    // Double-quoted string without interpolation can have unit suffix
    assert_eq!(
        tokenize(r#""127.0.0.1"_ip"#),
        vec![
            TokenKind::TypedString("127.0.0.1".to_string(), "ip".to_string()),
            TokenKind::Eof
        ]
    );

    assert_eq!(
        tokenize(r#""https://example.com"_http"#),
        vec![
            TokenKind::TypedString("https://example.com".to_string(), "http".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_fstring_no_suffix_with_interpolation() {
    use crate::token::FStringToken;
    // F-strings with interpolation should NOT produce TypedString
    // (suffixes not allowed on interpolated strings)
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
fn test_numeric_unit_suffix_for_ip() {
    // Numeric IP address: 0x7F000001_ip (127.0.0.1)
    assert_eq!(
        tokenize("0x7F000001_ip"),
        vec![
            TokenKind::TypedInteger(0x7F000001, NumericSuffix::Unit("ip".to_string())),
            TokenKind::Eof
        ]
    );

    // Decimal form
    assert_eq!(
        tokenize("2130706433_ip"),
        vec![
            TokenKind::TypedInteger(2130706433, NumericSuffix::Unit("ip".to_string())),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_port_unit_suffix() {
    assert_eq!(
        tokenize("8080_port"),
        vec![
            TokenKind::TypedInteger(8080, NumericSuffix::Unit("port".to_string())),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_file_path_unit_suffix() {
    // Windows-style path with drive letter
    assert_eq!(
        tokenize(r#"'C:/Users/data.txt'_file"#),
        vec![
            TokenKind::TypedRawString("C:/Users/data.txt".to_string(), "file".to_string()),
            TokenKind::Eof
        ]
    );

    // Unix-style path
    assert_eq!(
        tokenize(r#"'/etc/config.json'_file"#),
        vec![
            TokenKind::TypedRawString("/etc/config.json".to_string(), "file".to_string()),
            TokenKind::Eof
        ]
    );
}
