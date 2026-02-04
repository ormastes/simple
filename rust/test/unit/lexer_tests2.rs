#![allow(unused_imports, unused_variables)]
//! Lexer unit tests - Part 2

use simple_parser::lexer::Lexer;

use simple_parser::token::{FStringToken, NamePattern, Span, Token, TokenKind};

fn tokenize(source: &str) -> Vec<TokenKind> {
    let mut lexer = Lexer::new(source);
    lexer.tokenize().into_iter().map(|t| t.kind).collect()
}

fn tokenize_full(source: &str) -> Vec<Token> {
    let mut lexer = Lexer::new(source);
    lexer.tokenize()
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
    assert_eq!(tokenize("context"), vec![TokenKind::Context, TokenKind::Eof]);
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
    assert_eq!(tokenize("//"), vec![TokenKind::Parallel, TokenKind::Eof]);
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
fn test_operator_caret_is_error() {
    let tokens = tokenize("^");
    assert!(matches!(&tokens[0], TokenKind::Error(msg) if msg.contains("not allowed outside math blocks")));
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
        .any(|t| matches!(t, TokenKind::Identifier { name, .. } if name.contains("comment"))));
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
        vec![
            TokenKind::Identifier {
                name: "x".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Eof
        ]
    );
}

// === Line Continuation Tests ===

#[test]
fn test_line_continuation() {
    let tokens = tokenize("x \\\ny");
    assert_eq!(
        tokens,
        vec![
            TokenKind::Identifier {
                name: "x".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Identifier {
                name: "y".to_string(),
                pattern: NamePattern::Immutable
            },
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
            TokenKind::Identifier {
                name: "foo".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::LParen,
            TokenKind::Identifier {
                name: "x".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Comma,
            TokenKind::Identifier {
                name: "y".to_string(),
                pattern: NamePattern::Immutable
            },
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
            TokenKind::Identifier {
                name: "a".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Dot,
            TokenKind::Identifier {
                name: "b".to_string(),
                pattern: NamePattern::Immutable
            },
            TokenKind::Dot,
            TokenKind::Identifier {
                name: "c".to_string(),
                pattern: NamePattern::Immutable
            },
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
            TokenKind::Identifier {
                name: "arr".to_string(),
                pattern: NamePattern::Immutable
            },
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
    assert_eq!(
        tokens[1],
        TokenKind::Identifier {
            name: "add".to_string(),
            pattern: NamePattern::Immutable
        }
    );
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
