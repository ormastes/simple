
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
        tokenize("3.15"),
        vec![TokenKind::Float(3.15), TokenKind::Eof]
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
fn test_raw_double_string_literals() {
    // r"..." prefix creates raw double-quoted strings (no escapes, no interpolation)
    assert_eq!(
        tokenize(r#"r"hello""#),
        vec![TokenKind::RawString("hello".to_string()), TokenKind::Eof]
    );
    // Backslashes are literal in r"..." strings
    assert_eq!(
        tokenize(r#"r"hello\nworld""#),
        vec![
            TokenKind::RawString("hello\\nworld".to_string()),
            TokenKind::Eof
        ]
    );
    // Braces are literal in r"..." strings (no interpolation)
    assert_eq!(
        tokenize(r#"r"{name}""#),
        vec![TokenKind::RawString("{name}".to_string()), TokenKind::Eof]
    );
    // Escape sequences are not processed
    assert_eq!(
        tokenize(r#"r"tab\there""#),
        vec![
            TokenKind::RawString("tab\\there".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_raw_triple_string_literals() {
    // r"""...""" prefix creates raw triple-quoted strings
    assert_eq!(
        tokenize(r#"r"""hello""""#),
        vec![TokenKind::String("hello".to_string()), TokenKind::Eof]
    );
    // Multi-line raw triple-quoted strings
    assert_eq!(
        tokenize("r\"\"\"line1\nline2\"\"\""),
        vec![
            TokenKind::String("line1\nline2".to_string()),
            TokenKind::Eof
        ]
    );
    // Backslashes are literal in r"""...""" strings
    assert_eq!(
        tokenize(r#"r"""hello\nworld""""#),
        vec![
            TokenKind::String("hello\\nworld".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_triple_quoted_strings() {
    // Triple-quoted strings are raw by default (no interpolation)
    assert_eq!(
        tokenize(r#""""hello""""#),
        vec![TokenKind::String("hello".to_string()), TokenKind::Eof]
    );
    // Braces are literal in triple-quoted strings
    assert_eq!(
        tokenize(r#""""{name}""""#),
        vec![TokenKind::String("{name}".to_string()), TokenKind::Eof]
    );
    // Multi-line triple-quoted strings
    assert_eq!(
        tokenize("\"\"\"line1\nline2\"\"\""),
        vec![
            TokenKind::String("line1\nline2".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_triple_fstring_literals() {
    use crate::token::FStringToken;
    // Triple-quoted f-strings support interpolation and multi-line
    assert_eq!(
        tokenize(r#"f"""hello""""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("hello".to_string())]),
            TokenKind::Eof
        ]
    );
    // Interpolation in triple-quoted f-strings
    assert_eq!(
        tokenize(r#"f"""hello {name}""""#),
        vec![
            TokenKind::FString(vec![
                FStringToken::Literal("hello ".to_string()),
                FStringToken::Expr("name".to_string()),
            ]),
            TokenKind::Eof
        ]
    );
    // Multi-line triple-quoted f-strings
    assert_eq!(
        tokenize("f\"\"\"line1\nline2\"\"\""),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("line1\nline2".to_string())]),
            TokenKind::Eof
        ]
    );
    // Multi-line f-string with interpolation
    assert_eq!(
        tokenize("f\"\"\"Hello {name}!\nWelcome!\"\"\""),
        vec![
            TokenKind::FString(vec![
                FStringToken::Literal("Hello ".to_string()),
                FStringToken::Expr("name".to_string()),
                FStringToken::Literal("!\nWelcome!".to_string()),
            ]),
            TokenKind::Eof
        ]
    );
    // Double quotes inside triple f-string
    assert_eq!(
        tokenize(r#"f"""He said "hello""""#),
        vec![
            TokenKind::FString(vec![FStringToken::Literal("He said \"hello".to_string())]),
            TokenKind::Eof
        ]
    );
    // Escaped braces in triple f-string
    assert_eq!(
        tokenize(r#"f"""JSON: {{"key": {value}}}""""#),
        vec![
            TokenKind::FString(vec![
                FStringToken::Literal("JSON: {\"key\": ".to_string()),
                FStringToken::Expr("value".to_string()),
                FStringToken::Literal("}".to_string()),
            ]),
            TokenKind::Eof
        ]
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
        vec![
            TokenKind::Identifier {
                name: "foo".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Eof
        ]
    );
    assert_eq!(
        tokenize("_bar"),
        vec![
            TokenKind::Identifier {
                name: "_bar".to_string(),
                pattern: NamePattern::Private
            },
            TokenKind::Eof
        ]
    );
    assert_eq!(
        tokenize("baz123"),
        vec![
            TokenKind::Identifier {
                name: "baz123".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Eof
        ]
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
    assert_eq!(tokenize("go"), vec![TokenKind::Go, TokenKind::Eof]);
}

#[test]
fn test_suspension_keywords() {
    // Suspension control flow keywords (async-by-default #45)
    assert_eq!(tokenize("if~"), vec![TokenKind::IfSuspend, TokenKind::Eof]);
    assert_eq!(tokenize("while~"), vec![TokenKind::WhileSuspend, TokenKind::Eof]);
    assert_eq!(tokenize("for~"), vec![TokenKind::ForSuspend, TokenKind::Eof]);

    // Verify that regular keywords without ~ are still parsed correctly
    assert_eq!(tokenize("if"), vec![TokenKind::If, TokenKind::Eof]);
    assert_eq!(tokenize("while"), vec![TokenKind::While, TokenKind::Eof]);
    assert_eq!(tokenize("for"), vec![TokenKind::For, TokenKind::Eof]);

    // Verify that ~ alone is still a tilde operator
    assert_eq!(tokenize("~"), vec![TokenKind::Tilde, TokenKind::Eof]);
}


// === Contextual Keyword Tests ===

#[test]
fn test_contextual_keyword_skip_as_keyword() {
    // Branch 1: skip as keyword (NOT followed by '(')
    // Standalone skip statement
    assert_eq!(tokenize("skip"), vec![TokenKind::Skip, TokenKind::Eof]);

    // skip followed by newline
    assert_eq!(
        tokenize("skip\n"),
        vec![TokenKind::Skip, TokenKind::Newline, TokenKind::Eof]
    );

    // skip followed by other tokens
    assert_eq!(
        tokenize("skip;"),
        vec![TokenKind::Skip, TokenKind::Semicolon, TokenKind::Eof]
    );

    // skip in expression context
    assert_eq!(
        tokenize("x = skip"),
        vec![
            TokenKind::Identifier {
                name: "x".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Assign,
            TokenKind::Skip,
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_contextual_keyword_skip_as_identifier() {
    // Branch 2: skip as identifier (followed by '(')
    // Function call: skip(...)
    assert_eq!(
        tokenize("skip(5)"),
        vec![
            TokenKind::Identifier {
                name: "skip".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::Integer(5),
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );

    // Method call: obj.skip(...)
    assert_eq!(
        tokenize("obj.skip(10)"),
        vec![
            TokenKind::Identifier {
                name: "obj".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Dot,
            TokenKind::Identifier {
                name: "skip".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::Integer(10),
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );

    // Function definition: fn skip(...)
    assert_eq!(
        tokenize("fn skip(n)"),
        vec![
            TokenKind::Fn,
            TokenKind::Identifier {
                name: "skip".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::Identifier {
                name: "n".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_contextual_keyword_static_as_keyword() {
    // Branch 1: static as keyword (NOT followed by '(')
    // Static method declaration: static fn ...
    assert_eq!(
        tokenize("static fn"),
        vec![TokenKind::Static, TokenKind::Fn, TokenKind::Eof]
    );

    // Standalone static
    assert_eq!(tokenize("static"), vec![TokenKind::Static, TokenKind::Eof]);

    // Static followed by identifier
    assert_eq!(
        tokenize("static x"),
        vec![
            TokenKind::Static,
            TokenKind::Identifier {
                name: "x".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_contextual_keyword_static_as_identifier() {
    // Branch 2: static as identifier (followed by '(')
    // Function call: static(...)
    assert_eq!(
        tokenize("static()"),
        vec![
            TokenKind::Identifier {
                name: "static".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );

    // Method call: obj.static(...)
    assert_eq!(
        tokenize("obj.static(42)"),
        vec![
            TokenKind::Identifier {
                name: "obj".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Dot,
            TokenKind::Identifier {
                name: "static".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::Integer(42),
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_contextual_keyword_default_as_keyword() {
    // Branch 1: default as keyword (NOT followed by '(')
    // Match default case: default ->
    assert_eq!(
        tokenize("default ->"),
        vec![TokenKind::Default, TokenKind::Arrow, TokenKind::Eof]
    );

    // Standalone default
    assert_eq!(tokenize("default"), vec![TokenKind::Default, TokenKind::Eof]);

    // default followed by colon
    assert_eq!(
        tokenize("default:"),
        vec![TokenKind::Default, TokenKind::Colon, TokenKind::Eof]
    );
}

#[test]
fn test_contextual_keyword_default_as_identifier() {
    // Branch 2: default as identifier (followed by '(')
    // Function call: default(...)
    assert_eq!(
        tokenize("default()"),
        vec![
            TokenKind::Identifier {
                name: "default".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );

    // Method call with arguments
    assert_eq!(
        tokenize("config.default(100)"),
        vec![
            TokenKind::Identifier {
                name: "config".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Dot,
            TokenKind::Identifier {
                name: "default".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::Integer(100),
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_contextual_keywords_edge_cases() {
    // Test keywords with various whitespace and combinations

    // skip with multiple spaces before (
    assert_eq!(
        tokenize("skip (5)"),
        vec![
            TokenKind::Skip,
            TokenKind::LParen,
            TokenKind::Integer(5),
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );

    // Keywords as part of longer identifiers (should not trigger contextual logic)
    assert_eq!(
        tokenize("skip_all"),
        vec![
            TokenKind::Identifier {
                name: "skip_all".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Eof
        ]
    );

    assert_eq!(
        tokenize("static_var"),
        vec![
            TokenKind::Identifier {
                name: "static_var".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Eof
        ]
    );

    assert_eq!(
        tokenize("default_value"),
        vec![
            TokenKind::Identifier {
                name: "default_value".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_contextual_keywords_in_complex_expressions() {
    // Test contextual keywords in realistic code patterns

    // skip() in method chain
    assert_eq!(
        tokenize("items.skip(2).take(5)"),
        vec![
            TokenKind::Identifier {
                name: "items".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::Dot,
            TokenKind::Identifier {
                name: "skip".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::Integer(2),
            TokenKind::RParen,
            TokenKind::Dot,
            TokenKind::Identifier {
                name: "take".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::Integer(5),
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );

    // static method call on class
    assert_eq!(
        tokenize("MyClass.static()"),
        vec![
            TokenKind::Identifier {
                name: "MyClass".to_string(),
                pattern: NamePattern::TypeName,
            },
            TokenKind::Dot,
            TokenKind::Identifier {
                name: "static".to_string(),
                pattern: NamePattern::Immutable,
            },
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::Eof
        ]
    );
}
