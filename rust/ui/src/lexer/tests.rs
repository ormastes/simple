use super::*;

fn tokenize(source: &str) -> Vec<SuiTokenKind> {
    let mut lexer = SuiLexer::new(source);
    lexer.tokenize().into_iter().map(|t| t.kind).collect()
}

#[test]
fn test_text_only() {
    let tokens = tokenize("Hello World");
    assert_eq!(
        tokens,
        vec![SuiTokenKind::Text("Hello World".to_string()), SuiTokenKind::Eof,]
    );
}

#[test]
fn test_output_block() {
    let tokens = tokenize("{{ name }}");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::OutputOpen,
            SuiTokenKind::Identifier("name".to_string()),
            SuiTokenKind::OutputClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_directive_block() {
    let tokens = tokenize("{@ component Counter @}");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::DirectiveOpen,
            SuiTokenKind::Component,
            SuiTokenKind::Identifier("Counter".to_string()),
            SuiTokenKind::DirectiveClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_control_if() {
    let tokens = tokenize("{% if x > 0: %}yes{% end %}");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::ControlOpen,
            SuiTokenKind::If,
            SuiTokenKind::Identifier("x".to_string()),
            SuiTokenKind::Gt,
            SuiTokenKind::Integer(0),
            SuiTokenKind::Colon,
            SuiTokenKind::ControlClose,
            SuiTokenKind::Text("yes".to_string()),
            SuiTokenKind::ControlOpen,
            SuiTokenKind::End,
            SuiTokenKind::ControlClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_html_tag() {
    let tokens = tokenize("<div class=\"foo\">");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::TagOpen,
            SuiTokenKind::Identifier("div".to_string()),
            SuiTokenKind::Identifier("class".to_string()),
            SuiTokenKind::Assign,
            SuiTokenKind::String("foo".to_string()),
            SuiTokenKind::TagClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_self_closing_tag() {
    let tokens = tokenize("<input />");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::TagOpen,
            SuiTokenKind::Identifier("input".to_string()),
            SuiTokenKind::TagSelfClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_closing_tag() {
    let tokens = tokenize("</div>");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::TagEndOpen,
            SuiTokenKind::Identifier("div".to_string()),
            SuiTokenKind::TagClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_server_block() {
    let tokens = tokenize("{- count = 0 -}");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::ServerOpen,
            SuiTokenKind::Identifier("count".to_string()),
            SuiTokenKind::Assign,
            SuiTokenKind::Integer(0),
            SuiTokenKind::ServerClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_client_block() {
    let tokens = tokenize("{+ on_click(handler) +}");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::ClientOpen,
            SuiTokenKind::Identifier("on_click".to_string()),
            SuiTokenKind::LParen,
            SuiTokenKind::Identifier("handler".to_string()),
            SuiTokenKind::RParen,
            SuiTokenKind::ClientClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_declaration_block() {
    let tokens = tokenize("{$ let count: i32 $}");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::DeclOpen,
            SuiTokenKind::Let,
            SuiTokenKind::Identifier("count".to_string()),
            SuiTokenKind::Colon,
            SuiTokenKind::Identifier("i32".to_string()),
            SuiTokenKind::DeclClose,
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_comment_block() {
    let tokens = tokenize("{# This is a comment #}");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::CommentOpen,
            SuiTokenKind::Comment(" This is a comment ".to_string()),
            SuiTokenKind::Eof,
        ]
    );
}

#[test]
fn test_mixed_content() {
    let tokens = tokenize("<div>Hello {{ name }}</div>");
    assert_eq!(
        tokens,
        vec![
            SuiTokenKind::TagOpen,
            SuiTokenKind::Identifier("div".to_string()),
            SuiTokenKind::TagClose,
            SuiTokenKind::Text("Hello ".to_string()),
            SuiTokenKind::OutputOpen,
            SuiTokenKind::Identifier("name".to_string()),
            SuiTokenKind::OutputClose,
            SuiTokenKind::TagEndOpen,
            SuiTokenKind::Identifier("div".to_string()),
            SuiTokenKind::TagClose,
            SuiTokenKind::Eof,
        ]
    );
}
