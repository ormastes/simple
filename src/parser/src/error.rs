use crate::token::Span;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Syntax error at {line}:{column}: {message}")]
    SyntaxError {
        message: String,
        line: usize,
        column: usize,
    },

    #[error("Unexpected token: expected {expected}, found {found}")]
    UnexpectedToken {
        expected: String,
        found: String,
        span: Span,
    },

    #[error("Unexpected end of file")]
    UnexpectedEof,

    #[error("Invalid integer literal: {0}")]
    InvalidInteger(String),

    #[error("Invalid float literal: {0}")]
    InvalidFloat(String),

    #[error("Invalid escape sequence: {0}")]
    InvalidEscape(String),

    #[error("Unclosed string literal")]
    UnclosedString,

    #[error("Invalid indentation")]
    InvalidIndentation { line: usize },
}

impl ParseError {
    pub fn syntax_error(message: impl Into<String>, line: usize, column: usize) -> Self {
        Self::SyntaxError {
            message: message.into(),
            line,
            column,
        }
    }

    pub fn unexpected_token(
        expected: impl Into<String>,
        found: impl Into<String>,
        span: Span,
    ) -> Self {
        Self::UnexpectedToken {
            expected: expected.into(),
            found: found.into(),
            span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_syntax_error() {
        let err = ParseError::syntax_error("test error", 1, 5);
        assert!(err.to_string().contains("1:5"));
        assert!(err.to_string().contains("test error"));
    }
}
