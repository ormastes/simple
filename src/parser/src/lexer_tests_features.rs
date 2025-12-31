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
        vec![
            TokenKind::RawString("127.0.0.1".to_string()),
            TokenKind::Eof
        ]
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

// === AOP & Unified Predicates Tests (#1000-1050) ===

#[test]
fn test_aop_keywords() {
    assert_eq!(
        tokenize("on bind forbid allow mock"),
        vec![
            TokenKind::On,
            TokenKind::Bind,
            TokenKind::Forbid,
            TokenKind::Allow,
            TokenKind::Mock,
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_pointcut_simple() {
    assert_eq!(
        tokenize("pc{ type(Foo) }"),
        vec![
            TokenKind::Pointcut(" type(Foo) ".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_pointcut_with_operators() {
    assert_eq!(
        tokenize("pc{ type(Foo) & attr(inject) }"),
        vec![
            TokenKind::Pointcut(" type(Foo) & attr(inject) ".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_pointcut_with_negation() {
    assert_eq!(
        tokenize("pc{ !attr(test) }"),
        vec![
            TokenKind::Pointcut(" !attr(test) ".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_pointcut_nested_braces() {
    // Test that nested braces are handled correctly
    assert_eq!(
        tokenize("pc{ execution({ foo }) }"),
        vec![
            TokenKind::Pointcut(" execution({ foo }) ".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_pointcut_unclosed() {
    // Test unclosed pointcut
    let result = tokenize("pc{ type(Foo)");
    assert!(matches!(
        result[0],
        TokenKind::Error(ref msg) if msg.contains("Unclosed pointcut")
    ));
}

#[test]
fn test_aop_advice_statement() {
    assert_eq!(
        tokenize("on pc{ execution(* foo(..)) } use LogInterceptor"),
        vec![
            TokenKind::On,
            TokenKind::Pointcut(" execution(* foo(..)) ".to_string()),
            TokenKind::Use,
            TokenKind::Identifier("LogInterceptor".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_di_binding_statement() {
    assert_eq!(
        tokenize("bind on pc{ type(UserService) } -> MockUserService"),
        vec![
            TokenKind::Bind,
            TokenKind::On,
            TokenKind::Pointcut(" type(UserService) ".to_string()),
            TokenKind::Arrow,
            TokenKind::Identifier("MockUserService".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_architecture_rule_forbid() {
    assert_eq!(
        tokenize("forbid pc{ import(domain.**, infrastructure.**) }"),
        vec![
            TokenKind::Forbid,
            TokenKind::Pointcut(" import(domain.**, infrastructure.**) ".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_architecture_rule_allow() {
    assert_eq!(
        tokenize("allow pc{ use(utils.**) }"),
        vec![
            TokenKind::Allow,
            TokenKind::Pointcut(" use(utils.**) ".to_string()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn test_mock_declaration() {
    assert_eq!(
        tokenize("mock MockUser implements UserTrait"),
        vec![
            TokenKind::Mock,
            TokenKind::Identifier("MockUser".to_string()),
            TokenKind::Identifier("implements".to_string()),
            TokenKind::Identifier("UserTrait".to_string()),
            TokenKind::Eof
        ]
    );
}
