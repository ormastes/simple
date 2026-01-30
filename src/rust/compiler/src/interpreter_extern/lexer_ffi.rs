// TODO: Re-enable once RuntimeValue FFI API is properly defined
// use simple_runtime::RuntimeValue;
use simple_parser::{Lexer, TokenKind, NamePattern, Token};
// use std::collections::HashMap;

/// Token representation for FFI
#[derive(Debug, Clone)]
pub struct TokenInfo {
    pub kind: String,
    pub text: String,
    pub name: Option<String>,
    pub pattern: Option<String>,
    pub value: Option<i64>,
}

impl TokenInfo {
    fn from_token(token: Token) -> Self {
        let text = token.lexeme;
        match token.kind {
            TokenKind::Identifier { name, pattern } => {
                let pattern_str = match pattern {
                    NamePattern::Constant => "Constant",
                    NamePattern::TypeName => "TypeName",
                    NamePattern::Immutable => "Immutable",
                    NamePattern::Mutable => "Mutable",
                    NamePattern::Private => "Private",
                };
                TokenInfo {
                    kind: "Identifier".to_string(),
                    text,
                    name: Some(name),
                    pattern: Some(pattern_str.to_string()),
                    value: None,
                }
            }
            TokenKind::Integer(n) => TokenInfo {
                kind: "Integer".to_string(),
                text,
                name: None,
                pattern: None,
                value: Some(n),
            },
            TokenKind::Float(f) => TokenInfo {
                kind: "Float".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Bool(b) => TokenInfo {
                kind: "Bool".to_string(),
                text,
                name: None,
                pattern: None,
                value: Some(if b { 1 } else { 0 }),
            },
            // Keywords
            TokenKind::Skip => TokenInfo {
                kind: "Skip".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Static => TokenInfo {
                kind: "Static".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Default => TokenInfo {
                kind: "Default".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Fn => TokenInfo {
                kind: "Fn".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            // Delimiters
            TokenKind::LParen => TokenInfo {
                kind: "LParen".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::RParen => TokenInfo {
                kind: "RParen".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::LBrace => TokenInfo {
                kind: "LBrace".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::RBrace => TokenInfo {
                kind: "RBrace".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::LBracket => TokenInfo {
                kind: "LBracket".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::RBracket => TokenInfo {
                kind: "RBracket".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            // Operators
            TokenKind::Dot => TokenInfo {
                kind: "Dot".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Arrow => TokenInfo {
                kind: "Arrow".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Colon => TokenInfo {
                kind: "Colon".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Semicolon => TokenInfo {
                kind: "Semicolon".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Newline => TokenInfo {
                kind: "Newline".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Eof => TokenInfo {
                kind: "Eof".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            // For any other tokens, use debug representation
            _ => TokenInfo {
                kind: format!("{:?}", token.kind),
                text,
                name: None,
                pattern: None,
                value: None,
            }
        }
    }
}

/// Tokenize source code and return list of tokens
pub fn tokenize_source(source: &str) -> Vec<TokenInfo> {
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();

    tokens.into_iter().map(TokenInfo::from_token).collect()
}

// TODO: Implement FFI function once RuntimeValue API for heap objects is ready
// Currently commented out because RuntimeValue doesn't have String/Array/Dict constructors
// Need to use heap allocation API from simple_runtime
/*
pub fn simple_lexer_tokenize(args: &[RuntimeValue]) -> RuntimeValue {
    // Implementation pending: need heap object allocation API
    RuntimeValue::NIL
}
*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize_simple_expression() {
        let tokens = tokenize_source("skip(5)");
        assert_eq!(tokens.len(), 5); // Identifier, LParen, Integer, RParen, Eof
        assert_eq!(tokens[0].kind, "Identifier");
        assert_eq!(tokens[0].name, Some("skip".to_string()));
    }

    #[test]
    fn test_contextual_keyword_skip() {
        let tokens = tokenize_source("skip");
        assert_eq!(tokens[0].kind, "Skip");

        let tokens = tokenize_source("skip(5)");
        assert_eq!(tokens[0].kind, "Identifier");
        assert_eq!(tokens[0].name, Some("skip".to_string()));
    }
}
