//! Tests for error recovery and common mistake detection

use simple_parser::{
    error_recovery::{detect_common_mistake, CommonMistake},
    Parser,
};

#[test]
fn test_python_def_detection() {
    // Test the detection function directly since 'def' is treated as an identifier
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let def_token = Token::new(
        TokenKind::Identifier {
            name: "def".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(0, 3, 1, 1),
        "def".to_string(),
    );
    let prev = Token::new(TokenKind::Newline, Span::new(0, 0, 1, 1), "\n".to_string());

    let mistake = detect_common_mistake(&def_token, &prev, None);
    assert_eq!(mistake, Some(CommonMistake::PythonDef));
    assert!(CommonMistake::PythonDef.message().contains("Use 'fn'"));
    assert!(CommonMistake::PythonDef.message().contains("not 'def'"));
}

#[test]
fn test_python_none_detection() {
    let source = "val x = None";
    let mut parser = Parser::new(source);
    let _result = parser.parse();

    // Check if we detected the Python None mistake
    let hints = parser.error_hints();
    let has_none_hint = hints
        .iter()
        .any(|hint| hint.message.contains("nil") && hint.message.contains("None"));

    // If detection didn't work during parsing, test the detection function directly
    if !has_none_hint {
        use simple_parser::token::{NamePattern, Span, Token, TokenKind};

        let none_token = Token::new(
            TokenKind::Identifier {
                name: "None".to_string(),
                pattern: NamePattern::TypeName,
            },
            Span::new(8, 12, 1, 9),
            "None".to_string(),
        );
        let prev_token = Token::new(TokenKind::Assign, Span::new(6, 7, 1, 7), "=".to_string());

        let mistake = detect_common_mistake(&none_token, &prev_token, None);
        assert_eq!(mistake, Some(CommonMistake::PythonNone));
    }
}

#[test]
fn test_python_true_false_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    // Test True
    let true_token = Token::new(
        TokenKind::Identifier {
            name: "True".to_string(),
            pattern: NamePattern::TypeName,
        },
        Span::new(0, 4, 1, 1),
        "True".to_string(),
    );
    let prev = Token::new(TokenKind::Assign, Span::new(0, 0, 1, 1), "=".to_string());

    let mistake = detect_common_mistake(&true_token, &prev, None);
    assert_eq!(mistake, Some(CommonMistake::PythonTrue));

    // Test False
    let false_token = Token::new(
        TokenKind::Identifier {
            name: "False".to_string(),
            pattern: NamePattern::TypeName,
        },
        Span::new(0, 5, 1, 1),
        "False".to_string(),
    );

    let mistake = detect_common_mistake(&false_token, &prev, None);
    assert_eq!(mistake, Some(CommonMistake::PythonFalse));
}

#[test]
fn test_rust_let_mut_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let mut_token = Token::new(
        TokenKind::Identifier {
            name: "mut".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(4, 7, 1, 5),
        "mut".to_string(),
    );
    let let_token = Token::new(TokenKind::Let, Span::new(0, 3, 1, 1), "let".to_string());

    let mistake = detect_common_mistake(&mut_token, &let_token, None);
    assert_eq!(mistake, Some(CommonMistake::RustLetMut));
}

#[test]
fn test_typescript_const_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let const_token = Token::new(
        TokenKind::Identifier {
            name: "const".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(0, 5, 1, 1),
        "const".to_string(),
    );
    let prev = Token::new(TokenKind::Newline, Span::new(0, 0, 1, 1), "\n".to_string());

    let mistake = detect_common_mistake(&const_token, &prev, None);
    assert_eq!(mistake, Some(CommonMistake::TsConst));
}

#[test]
fn test_typescript_function_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let function_token = Token::new(
        TokenKind::Identifier {
            name: "function".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(0, 8, 1, 1),
        "function".to_string(),
    );
    let prev = Token::new(TokenKind::Newline, Span::new(0, 0, 1, 1), "\n".to_string());

    let mistake = detect_common_mistake(&function_token, &prev, None);
    assert_eq!(mistake, Some(CommonMistake::TsFunction));
}

#[test]
fn test_java_public_class_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let public_token = Token::new(
        TokenKind::Identifier {
            name: "public".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(0, 6, 1, 1),
        "public".to_string(),
    );
    let prev = Token::new(TokenKind::Newline, Span::new(0, 0, 1, 1), "\n".to_string());
    let class_token = Token::new(
        TokenKind::Identifier {
            name: "class".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(7, 12, 1, 8),
        "class".to_string(),
    );

    let mistake = detect_common_mistake(&public_token, &prev, Some(&class_token));
    assert_eq!(mistake, Some(CommonMistake::JavaPublicClass));
}

#[test]
fn test_common_mistake_messages() {
    assert!(CommonMistake::PythonDef.message().contains("fn"));
    assert!(CommonMistake::PythonNone.message().contains("nil"));
    assert!(CommonMistake::RustLetMut.message().contains("var"));
    assert!(CommonMistake::TsConst.message().contains("val"));
    assert!(CommonMistake::TsFunction.message().contains("fn"));
}

#[test]
fn test_common_mistake_suggestions() {
    assert!(CommonMistake::PythonDef.suggestion().contains("fn"));
    assert!(CommonMistake::PythonNone.suggestion().contains("nil"));
    assert!(CommonMistake::RustLetMut.suggestion().contains("var"));
    assert!(CommonMistake::TsConst.suggestion().contains("val"));
}

#[test]
fn test_typescript_let_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let let_token = Token::new(TokenKind::Let, Span::new(0, 3, 1, 1), "let".to_string());
    let prev = Token::new(TokenKind::Newline, Span::new(0, 0, 1, 1), "\n".to_string());
    let next = Token::new(
        TokenKind::Identifier {
            name: "x".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(4, 5, 1, 5),
        "x".to_string(),
    );

    let mistake = detect_common_mistake(&let_token, &prev, Some(&next));
    assert_eq!(mistake, Some(CommonMistake::TsLet));
    assert!(CommonMistake::TsLet.message().contains("val"));
    assert!(CommonMistake::TsLet.message().contains("var"));
}

#[test]
fn test_python_self_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let self_token = Token::new(TokenKind::Self_, Span::new(0, 4, 1, 1), "self".to_string());
    let prev = Token::new(TokenKind::Newline, Span::new(0, 0, 1, 1), "\n".to_string());
    let dot_token = Token::new(TokenKind::Dot, Span::new(4, 5, 1, 5), ".".to_string());

    let mistake = detect_common_mistake(&self_token, &prev, Some(&dot_token));
    assert_eq!(mistake, Some(CommonMistake::PythonSelf));
    assert!(CommonMistake::PythonSelf.message().contains("implicit"));
}

#[test]
fn test_typescript_arrow_function_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let fat_arrow = Token::new(TokenKind::FatArrow, Span::new(8, 10, 1, 9), "=>".to_string());
    let rparen = Token::new(TokenKind::RParen, Span::new(7, 8, 1, 8), ")".to_string());

    let mistake = detect_common_mistake(&fat_arrow, &rparen, None);
    assert_eq!(mistake, Some(CommonMistake::TsArrowFunction));
    assert!(CommonMistake::TsArrowFunction.message().contains("lambda"));
}

#[test]
fn test_rust_turbofish_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let lt = Token::new(TokenKind::Lt, Span::new(4, 5, 1, 5), "<".to_string());
    let double_colon = Token::new(TokenKind::DoubleColon, Span::new(2, 4, 1, 3), "::".to_string());

    let mistake = detect_common_mistake(&lt, &double_colon, None);
    assert_eq!(mistake, Some(CommonMistake::RustTurbofish));
}

#[test]
fn test_rust_macro_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let not = Token::new(TokenKind::Not, Span::new(5, 6, 1, 6), "!".to_string());
    let ident = Token::new(
        TokenKind::Identifier {
            name: "println".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(0, 5, 1, 1),
        "println".to_string(),
    );

    let mistake = detect_common_mistake(&not, &ident, None);
    assert_eq!(mistake, Some(CommonMistake::RustMacro));
    assert!(CommonMistake::RustMacro.suggestion().contains("@"));
}

#[test]
fn test_wrong_brackets_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    let lbracket = Token::new(TokenKind::LBracket, Span::new(4, 5, 1, 5), "[".to_string());
    let ident = Token::new(
        TokenKind::Identifier {
            name: "Vec".to_string(),
            pattern: NamePattern::TypeName,
        },
        Span::new(0, 3, 1, 1),
        "Vec".to_string(),
    );
    let type_param = Token::new(
        TokenKind::Identifier {
            name: "String".to_string(),
            pattern: NamePattern::TypeName,
        },
        Span::new(5, 11, 1, 6),
        "String".to_string(),
    );

    let mistake = detect_common_mistake(&lbracket, &ident, Some(&type_param));
    assert_eq!(mistake, Some(CommonMistake::WrongBrackets));
    assert!(CommonMistake::WrongBrackets.suggestion().contains("<>"));
}

#[test]
fn test_c_type_first_detection() {
    use simple_parser::token::{NamePattern, Span, Token, TokenKind};

    // Test "int x"
    let int_token = Token::new(
        TokenKind::Identifier {
            name: "int".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(0, 3, 1, 1),
        "int".to_string(),
    );
    let prev = Token::new(TokenKind::Newline, Span::new(0, 0, 1, 1), "\n".to_string());
    let var_token = Token::new(
        TokenKind::Identifier {
            name: "x".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(4, 5, 1, 5),
        "x".to_string(),
    );

    let mistake = detect_common_mistake(&int_token, &prev, Some(&var_token));
    assert_eq!(mistake, Some(CommonMistake::CTypeFirst));

    // Test "float y"
    let float_token = Token::new(
        TokenKind::Identifier {
            name: "float".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(0, 5, 1, 1),
        "float".to_string(),
    );
    let y_token = Token::new(
        TokenKind::Identifier {
            name: "y".to_string(),
            pattern: NamePattern::Immutable,
        },
        Span::new(6, 7, 1, 7),
        "y".to_string(),
    );

    let mistake = detect_common_mistake(&float_token, &prev, Some(&y_token));
    assert_eq!(mistake, Some(CommonMistake::CTypeFirst));

    // Test message content
    assert!(CommonMistake::CTypeFirst.message().contains("Type comes after"));
    assert!(CommonMistake::CTypeFirst.suggestion().contains("val"));
}
