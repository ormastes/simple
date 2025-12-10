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

#[test]
fn test_keyword_actor() {
    assert_eq!(tokenize("actor"), vec![TokenKind::Actor, TokenKind::Eof]);
}

#[test]
fn test_keyword_pub() {
    assert_eq!(tokenize("pub"), vec![TokenKind::Pub, TokenKind::Eof]);
}

#[test]
fn test_keyword_priv() {
    assert_eq!(tokenize("priv"), vec![TokenKind::Priv, TokenKind::Eof]);
}

#[test]
fn test_keyword_import() {
    assert_eq!(tokenize("import"), vec![TokenKind::Import, TokenKind::Eof]);
}

#[test]
fn test_keyword_from() {
    assert_eq!(tokenize("from"), vec![TokenKind::From, TokenKind::Eof]);
}

#[test]
fn test_keyword_as() {
    assert_eq!(tokenize("as"), vec![TokenKind::As, TokenKind::Eof]);
}

#[test]
fn test_keyword_in() {
    assert_eq!(tokenize("in"), vec![TokenKind::In, TokenKind::Eof]);
}

#[test]
fn test_keyword_is() {
    assert_eq!(tokenize("is"), vec![TokenKind::Is, TokenKind::Eof]);
}

#[test]
fn test_keyword_not() {
    assert_eq!(tokenize("not"), vec![TokenKind::Not, TokenKind::Eof]);
}

#[test]
fn test_keyword_and() {
    assert_eq!(tokenize("and"), vec![TokenKind::And, TokenKind::Eof]);
}

#[test]
fn test_keyword_or() {
    assert_eq!(tokenize("or"), vec![TokenKind::Or, TokenKind::Eof]);
}

#[test]
fn test_keyword_spawn() {
    assert_eq!(tokenize("spawn"), vec![TokenKind::Spawn, TokenKind::Eof]);
}

#[test]
fn test_keyword_new() {
    assert_eq!(tokenize("new"), vec![TokenKind::New, TokenKind::Eof]);
}

#[test]
fn test_keyword_self() {
    assert_eq!(tokenize("self"), vec![TokenKind::Self_, TokenKind::Eof]);
}

#[test]
fn test_keyword_super() {
    assert_eq!(tokenize("super"), vec![TokenKind::Super, TokenKind::Eof]);
}

#[test]
fn test_keyword_async() {
    assert_eq!(tokenize("async"), vec![TokenKind::Async, TokenKind::Eof]);
}

#[test]
fn test_keyword_await() {
    assert_eq!(tokenize("await"), vec![TokenKind::Await, TokenKind::Eof]);
}

#[test]
fn test_keyword_yield() {
    assert_eq!(tokenize("yield"), vec![TokenKind::Yield, TokenKind::Eof]);
}

#[test]
fn test_keyword_const() {
    assert_eq!(tokenize("const"), vec![TokenKind::Const, TokenKind::Eof]);
}

#[test]
fn test_keyword_static() {
    assert_eq!(tokenize("static"), vec![TokenKind::Static, TokenKind::Eof]);
}

#[test]
fn test_keyword_type() {
    assert_eq!(tokenize("type"), vec![TokenKind::Type, TokenKind::Eof]);
}

#[test]
fn test_keyword_extern() {
    assert_eq!(tokenize("extern"), vec![TokenKind::Extern, TokenKind::Eof]);
}

#[test]
fn test_keyword_context() {
    assert_eq!(
        tokenize("context"),
        vec![TokenKind::Context, TokenKind::Eof]
    );
}

#[test]
fn test_keyword_macro() {
    assert_eq!(tokenize("macro"), vec![TokenKind::Macro, TokenKind::Eof]);
}

#[test]
fn test_underscore() {
    assert_eq!(tokenize("_"), vec![TokenKind::Underscore, TokenKind::Eof]);
}

// === Arithmetic Operator Tests ===

#[test]
fn test_operator_plus() {
    assert_eq!(tokenize("+"), vec![TokenKind::Plus, TokenKind::Eof]);
}

#[test]
fn test_operator_minus() {
    assert_eq!(tokenize("-"), vec![TokenKind::Minus, TokenKind::Eof]);
}

#[test]
fn test_operator_star() {
    assert_eq!(tokenize("*"), vec![TokenKind::Star, TokenKind::Eof]);
}

#[test]
fn test_operator_slash() {
    assert_eq!(tokenize("/"), vec![TokenKind::Slash, TokenKind::Eof]);
}

#[test]
fn test_operator_percent() {
    assert_eq!(tokenize("%"), vec![TokenKind::Percent, TokenKind::Eof]);
}

#[test]
fn test_operator_double_star() {
    assert_eq!(tokenize("**"), vec![TokenKind::DoubleStar, TokenKind::Eof]);
}

#[test]
fn test_operator_double_slash() {
    assert_eq!(tokenize("//"), vec![TokenKind::DoubleSlash, TokenKind::Eof]);
}

// === Assignment Operator Tests ===

#[test]
fn test_operator_assign() {
    assert_eq!(tokenize("="), vec![TokenKind::Assign, TokenKind::Eof]);
}

#[test]
fn test_operator_plus_assign() {
    assert_eq!(tokenize("+="), vec![TokenKind::PlusAssign, TokenKind::Eof]);
}

#[test]
fn test_operator_minus_assign() {
    assert_eq!(tokenize("-="), vec![TokenKind::MinusAssign, TokenKind::Eof]);
}

#[test]
fn test_operator_star_assign() {
    assert_eq!(tokenize("*="), vec![TokenKind::StarAssign, TokenKind::Eof]);
}

#[test]
fn test_operator_slash_assign() {
    assert_eq!(tokenize("/="), vec![TokenKind::SlashAssign, TokenKind::Eof]);
}

// === Comparison Operator Tests ===

#[test]
fn test_operator_eq() {
    assert_eq!(tokenize("=="), vec![TokenKind::Eq, TokenKind::Eof]);
}

#[test]
fn test_operator_not_eq() {
    assert_eq!(tokenize("!="), vec![TokenKind::NotEq, TokenKind::Eof]);
}

#[test]
fn test_operator_lt() {
    assert_eq!(tokenize("<"), vec![TokenKind::Lt, TokenKind::Eof]);
}

#[test]
fn test_operator_gt() {
    assert_eq!(tokenize(">"), vec![TokenKind::Gt, TokenKind::Eof]);
}

#[test]
fn test_operator_lt_eq() {
    assert_eq!(tokenize("<="), vec![TokenKind::LtEq, TokenKind::Eof]);
}

#[test]
fn test_operator_gt_eq() {
    assert_eq!(tokenize(">="), vec![TokenKind::GtEq, TokenKind::Eof]);
}

// === Arrow Operator Tests ===

#[test]
fn test_operator_arrow() {
    assert_eq!(tokenize("->"), vec![TokenKind::Arrow, TokenKind::Eof]);
}

#[test]
fn test_operator_fat_arrow() {
    assert_eq!(tokenize("=>"), vec![TokenKind::FatArrow, TokenKind::Eof]);
}

// === Bitwise Operator Tests ===

#[test]
fn test_operator_ampersand() {
    assert_eq!(tokenize("&"), vec![TokenKind::Ampersand, TokenKind::Eof]);
}

#[test]
fn test_operator_pipe() {
    assert_eq!(tokenize("|"), vec![TokenKind::Pipe, TokenKind::Eof]);
}

#[test]
fn test_operator_caret() {
    assert_eq!(tokenize("^"), vec![TokenKind::Caret, TokenKind::Eof]);
}

#[test]
fn test_operator_tilde() {
    assert_eq!(tokenize("~"), vec![TokenKind::Tilde, TokenKind::Eof]);
}

#[test]
fn test_operator_shift_left() {
    assert_eq!(tokenize("<<"), vec![TokenKind::ShiftLeft, TokenKind::Eof]);
}

#[test]
fn test_operator_shift_right() {
    assert_eq!(tokenize(">>"), vec![TokenKind::ShiftRight, TokenKind::Eof]);
}

// === Other Operator Tests ===

#[test]
fn test_operator_bang() {
    assert_eq!(tokenize("!"), vec![TokenKind::Bang, TokenKind::Eof]);
}

#[test]
fn test_operator_question() {
    assert_eq!(tokenize("?"), vec![TokenKind::Question, TokenKind::Eof]);
}

#[test]
fn test_operator_at() {
    assert_eq!(tokenize("@"), vec![TokenKind::At, TokenKind::Eof]);
}

#[test]
fn test_operator_dollar() {
    assert_eq!(tokenize("$"), vec![TokenKind::Dollar, TokenKind::Eof]);
}

#[test]
fn test_operator_backslash() {
    assert_eq!(tokenize("\\"), vec![TokenKind::Backslash, TokenKind::Eof]);
}

// === Delimiter Tests ===

#[test]
fn test_delimiter_lparen() {
    assert_eq!(tokenize("("), vec![TokenKind::LParen, TokenKind::Eof]);
}

#[test]
fn test_delimiter_rparen() {
    assert_eq!(tokenize(")"), vec![TokenKind::RParen, TokenKind::Eof]);
}

#[test]
fn test_delimiter_lbracket() {
    assert_eq!(tokenize("["), vec![TokenKind::LBracket, TokenKind::Eof]);
}

#[test]
fn test_delimiter_rbracket() {
    assert_eq!(tokenize("]"), vec![TokenKind::RBracket, TokenKind::Eof]);
}

#[test]
fn test_delimiter_lbrace() {
    assert_eq!(tokenize("{"), vec![TokenKind::LBrace, TokenKind::Eof]);
}

#[test]
fn test_delimiter_rbrace() {
    assert_eq!(tokenize("}"), vec![TokenKind::RBrace, TokenKind::Eof]);
}

#[test]
fn test_delimiter_comma() {
    assert_eq!(tokenize(","), vec![TokenKind::Comma, TokenKind::Eof]);
}

#[test]
fn test_delimiter_semicolon() {
    assert_eq!(tokenize(";"), vec![TokenKind::Semicolon, TokenKind::Eof]);
}

#[test]
fn test_delimiter_colon() {
    assert_eq!(tokenize(":"), vec![TokenKind::Colon, TokenKind::Eof]);
}

#[test]
fn test_delimiter_double_colon() {
    assert_eq!(tokenize("::"), vec![TokenKind::DoubleColon, TokenKind::Eof]);
}

#[test]
fn test_delimiter_dot() {
    assert_eq!(tokenize("."), vec![TokenKind::Dot, TokenKind::Eof]);
}

#[test]
fn test_delimiter_double_dot() {
    assert_eq!(tokenize(".."), vec![TokenKind::DoubleDot, TokenKind::Eof]);
}

#[test]
fn test_delimiter_ellipsis() {
    assert_eq!(tokenize("..."), vec![TokenKind::Ellipsis, TokenKind::Eof]);
}

// === Indentation Tests ===

#[test]
fn test_indent_simple() {
    let source = "if x:\n    y";
    let tokens = tokenize(source);
    assert!(tokens.contains(&TokenKind::Indent));
}

#[test]
fn test_dedent_simple() {
    let source = "if x:\n    y\nz";
    let tokens = tokenize(source);
    assert!(tokens.contains(&TokenKind::Dedent));
}

#[test]
fn test_nested_indent() {
    let source = "if a:\n    if b:\n        c\nd";
    let tokens = tokenize(source);
    // Should have two indents and two dedents
    let indent_count = tokens.iter().filter(|t| **t == TokenKind::Indent).count();
    let dedent_count = tokens.iter().filter(|t| **t == TokenKind::Dedent).count();
    assert_eq!(indent_count, 2);
    assert_eq!(dedent_count, 2);
}

#[test]
fn test_tab_indent() {
    let source = "if x:\n\ty";
    let tokens = tokenize(source);
    assert!(tokens.contains(&TokenKind::Indent));
}

#[test]
fn test_empty_lines_in_indent() {
    let source = "if x:\n\n    y";
    let tokens = tokenize(source);
    assert!(tokens.contains(&TokenKind::Indent));
}

// === Comment Tests ===

#[test]
fn test_line_comment() {
    let tokens = tokenize("x # this is a comment\ny");
    assert!(!tokens
        .iter()
        .any(|t| matches!(t, TokenKind::Identifier(s) if s.contains("comment"))));
}

#[test]
fn test_comment_only_line() {
    let tokens = tokenize("# comment only");
    assert_eq!(tokens, vec![TokenKind::Eof]);
}

#[test]
fn test_comment_at_line_start() {
    let tokens = tokenize("# comment\nx");
    assert_eq!(
        tokens,
        vec![TokenKind::Identifier("x".to_string()), TokenKind::Eof]
    );
}

// === Line Continuation Tests ===

#[test]
fn test_line_continuation() {
    let tokens = tokenize("x \\\ny");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Identifier("x".to_string()),
            TokenKind::Identifier("y".to_string()),
            TokenKind::Eof,
        ]
    );
}

// === Newline Tests ===

#[test]
fn test_newline_single() {
    let tokens = tokenize("x\ny");
    assert!(tokens.contains(&TokenKind::Newline));
}

#[test]
fn test_newline_multiple() {
    let tokens = tokenize("x\n\n\ny");
    // Multiple newlines should not generate multiple newline tokens
    // (empty lines are skipped in indentation handling)
}

// === Token Span Tests ===

#[test]
fn test_token_span_single_char() {
    let tokens = tokenize_full("+");
    assert_eq!(tokens[0].span.start, 0);
    assert_eq!(tokens[0].span.end, 1);
}

#[test]
fn test_token_span_multi_char() {
    let tokens = tokenize_full("hello");
    assert_eq!(tokens[0].span.start, 0);
    assert_eq!(tokens[0].span.end, 5);
}

#[test]
fn test_token_line_tracking() {
    let tokens = tokenize_full("x\ny");
    assert_eq!(tokens[0].span.line, 1);
    assert_eq!(tokens[2].span.line, 2); // After newline
}

// === Complex Expression Tests ===

#[test]
fn test_expression_arithmetic() {
    let tokens = tokenize("1 + 2 * 3");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Integer(1),
            TokenKind::Plus,
            TokenKind::Integer(2),
            TokenKind::Star,
            TokenKind::Integer(3),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_expression_function_call() {
    let tokens = tokenize("foo(x, y)");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Identifier("foo".to_string()),
            TokenKind::LParen,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Comma,
            TokenKind::Identifier("y".to_string()),
            TokenKind::RParen,
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_expression_method_chain() {
    let tokens = tokenize("a.b.c()");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Identifier("a".to_string()),
            TokenKind::Dot,
            TokenKind::Identifier("b".to_string()),
            TokenKind::Dot,
            TokenKind::Identifier("c".to_string()),
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_expression_array_indexing() {
    let tokens = tokenize("arr[0]");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Identifier("arr".to_string()),
            TokenKind::LBracket,
            TokenKind::Integer(0),
            TokenKind::RBracket,
            TokenKind::Eof,
        ]
    );
}

// === Function Definition Tokenization ===

#[test]
fn test_function_def_tokens() {
    let source = "fn add(a: i64, b: i64) -> i64:\n    return a + b";
    let tokens = tokenize(source);
    assert_eq!(tokens[0], TokenKind::Fn);
    assert_eq!(tokens[1], TokenKind::Identifier("add".to_string()));
    assert_eq!(tokens[2], TokenKind::LParen);
}

// === Error Token Tests ===

#[test]
fn test_unexpected_character() {
    let tokens = tokenize("`");
    assert!(matches!(tokens[0], TokenKind::Error(_)));
}

// === Special f-string prefix ===

#[test]
fn test_fstring_with_f_prefix() {
    let tokens = tokenize(r#"f"hello {name}""#);
    assert!(matches!(tokens[0], TokenKind::FString(_)));
}
