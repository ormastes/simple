//! SDN error types with span information for diagnostics.

use thiserror::Error;

/// Source location in SDN document.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Span {
    pub fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
        }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line,
            column: self.column,
        }
    }
}

impl Default for Span {
    fn default() -> Self {
        Self::new(0, 0, 1, 1)
    }
}

/// SDN parse and document errors.
#[derive(Error, Debug, Clone)]
pub enum SdnError {
    #[error("Syntax error at {line}:{column}: {message}")]
    SyntaxError {
        message: String,
        line: usize,
        column: usize,
        span: Option<Span>,
    },

    #[error("Unexpected token: expected {expected}, found {found}")]
    UnexpectedToken {
        expected: String,
        found: String,
        span: Span,
    },

    #[error("Unexpected end of file")]
    UnexpectedEof { span: Option<Span> },

    #[error("Invalid number literal: {0}")]
    InvalidNumber(String),

    #[error("Unclosed string literal")]
    UnclosedString { span: Option<Span> },

    #[error("Invalid indentation")]
    InvalidIndentation { line: usize },

    #[error("Invalid escape sequence: {0}")]
    InvalidEscape(String),

    #[error("Path not found: {path}")]
    PathNotFound { path: String },

    #[error("Type mismatch: expected {expected}, found {found}")]
    TypeMismatch { expected: String, found: String },

    #[error("Invalid table row: expected {expected} columns, found {found}")]
    InvalidTableRow { expected: usize, found: usize },

    #[error("I/O error: {0}")]
    IoError(String),

    #[error("Security error: {message}")]
    SecurityError { message: String, span: Option<Span> },

    #[error("Parse error: {message}")]
    ParseError { message: String, span: Option<Span> },
}

impl SdnError {
    pub fn syntax_error(message: impl Into<String>, line: usize, column: usize) -> Self {
        Self::SyntaxError {
            message: message.into(),
            line,
            column,
            span: None,
        }
    }

    pub fn syntax_error_with_span(message: impl Into<String>, span: Span) -> Self {
        Self::SyntaxError {
            message: message.into(),
            line: span.line,
            column: span.column,
            span: Some(span),
        }
    }

    pub fn unexpected_token(expected: impl Into<String>, found: impl Into<String>, span: Span) -> Self {
        Self::UnexpectedToken {
            expected: expected.into(),
            found: found.into(),
            span,
        }
    }

    pub fn security_error(message: impl Into<String>, span: Span) -> Self {
        Self::SecurityError {
            message: message.into(),
            span: Some(span),
        }
    }

    pub fn is_security_error(&self) -> bool {
        matches!(self, SdnError::SecurityError { .. })
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            SdnError::SyntaxError { span, .. } => *span,
            SdnError::UnexpectedToken { span, .. } => Some(*span),
            SdnError::UnclosedString { span } => *span,
            SdnError::UnexpectedEof { span } => *span,
            SdnError::SecurityError { span, .. } => *span,
            SdnError::ParseError { span, .. } => *span,
            _ => None,
        }
    }
}

impl From<std::io::Error> for SdnError {
    fn from(err: std::io::Error) -> Self {
        SdnError::IoError(err.to_string())
    }
}

pub type Result<T> = std::result::Result<T, SdnError>;
