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
    assert_eq!(tokenize("~="), vec![TokenKind::TildeAssign, TokenKind::Eof]);
}

#[test]
fn test_arrow_operators() {
    assert_eq!(tokenize("->"), vec![TokenKind::Arrow, TokenKind::Eof]);
    assert_eq!(tokenize("=>"), vec![TokenKind::FatArrow, TokenKind::Eof]);
    assert_eq!(
        tokenize("<-"),
        vec![TokenKind::ChannelArrow, TokenKind::Eof]
    );
}

#[test]
fn test_channel_arrow_disambiguation() {
    // <- is channel arrow (single token)
    assert_eq!(
        tokenize("<-"),
        vec![TokenKind::ChannelArrow, TokenKind::Eof]
    );

    // < - with space is two tokens
    assert_eq!(
        tokenize("< -"),
        vec![TokenKind::Lt, TokenKind::Minus, TokenKind::Eof]
    );

    // a<-b is tokenized as a, <-, b (channel send pattern)
    assert_eq!(
        tokenize("a<-b"),
        vec![
            TokenKind::Identifier {
                name: "a".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::ChannelArrow,
            TokenKind::Identifier {
                name: "b".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Eof
        ]
    );

    // a < -b is three tokens (comparison with negative)
    assert_eq!(
        tokenize("a < -b"),
        vec![
            TokenKind::Identifier {
                name: "a".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Lt,
            TokenKind::Minus,
            TokenKind::Identifier {
                name: "b".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Eof
        ]
    );
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
            TokenKind::Identifier { name: "x".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Star,
            TokenKind::LParen,
            TokenKind::Identifier { name: "y".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Plus,
            TokenKind::Identifier { name: "z".to_string(), pattern: NamePattern::Immutable },
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
            TokenKind::Identifier { name: "print".to_string(), pattern: NamePattern::Immutable },
            TokenKind::LParen,
            TokenKind::Identifier { name: "x".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Comma,
            TokenKind::Identifier { name: "y".to_string(), pattern: NamePattern::Immutable },
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
            TokenKind::Identifier { name: "x".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Colon,
            TokenKind::Newline,
            TokenKind::Indent,
            TokenKind::Identifier { name: "y".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Newline,
            TokenKind::Dedent,
            TokenKind::Identifier { name: "z".to_string(), pattern: NamePattern::Immutable },
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
            TokenKind::Identifier { name: "a".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Colon,
            TokenKind::Newline,
            TokenKind::Indent,
            TokenKind::If,
            TokenKind::Identifier { name: "b".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Colon,
            TokenKind::Newline,
            TokenKind::Indent,
            TokenKind::Identifier { name: "c".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Newline,
            TokenKind::Dedent,
            TokenKind::Dedent,
            TokenKind::Identifier { name: "d".to_string(), pattern: NamePattern::Immutable },
            TokenKind::Eof,
        ]
    );
}

