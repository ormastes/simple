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
        vec![TokenKind::Identifier("x".to_string()), TokenKind::Eof,]
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

#[test]
fn test_triple_slash_doc_comment() {
    // /// is a doc comment (like in Rust)
    assert_eq!(
        tokenize("/// This is a doc comment\nx"),
        vec![
            TokenKind::DocComment("This is a doc comment".to_string()),
            TokenKind::Newline,
            TokenKind::Identifier("x".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_double_slash_still_floor_div() {
    // // is still floor division, not a comment
    assert_eq!(
        tokenize("10 // 3"),
        vec![
            TokenKind::Integer(10),
            TokenKind::DoubleSlash,
            TokenKind::Integer(3),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_triple_slash_multiline_doc_block() {
    // ///.../// is a multi-line doc block
    // First, let's just test what tokens are produced
    let tokens = tokenize("///\nHello\n///\nx");
    eprintln!("Tokens: {:#?}", tokens);
    assert_eq!(
        tokens,
        vec![
            TokenKind::DocComment("Hello".to_string()),
            TokenKind::Identifier("x".to_string()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn test_triple_slash_multiline_with_import() {
    // ///.../// before import should work
    assert_eq!(
        tokenize("///\nModule docs\n///\nimport foo"),
        vec![
            TokenKind::DocComment("Module docs".to_string()),
            TokenKind::Import,
            TokenKind::Identifier("foo".to_string()),
            TokenKind::Eof,
        ]
    );
}

