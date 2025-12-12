use crate::diagnostic::Diagnostic;
use crate::token::Span;
use thiserror::Error;

/// Parse error with span information for diagnostics.
#[derive(Error, Debug, Clone)]
pub enum ParseError {
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
    UnexpectedEof,

    #[error("Invalid integer literal: {0}")]
    InvalidInteger(String),

    #[error("Invalid float literal: {0}")]
    InvalidFloat(String),

    #[error("Invalid escape sequence: {0}")]
    InvalidEscape(String),

    #[error("Unclosed string literal")]
    UnclosedString { span: Option<Span> },

    #[error("Invalid indentation")]
    InvalidIndentation { line: usize },

    #[error("Unterminated block comment")]
    UnterminatedBlockComment { span: Option<Span> },

    #[error("Missing expected token: {expected}")]
    MissingToken {
        expected: String,
        span: Span,
    },

    #[error("Invalid pattern")]
    InvalidPattern { span: Span, message: String },

    #[error("Invalid type")]
    InvalidType { span: Span, message: String },
}

impl ParseError {
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

    pub fn missing_token(expected: impl Into<String>, span: Span) -> Self {
        Self::MissingToken {
            expected: expected.into(),
            span,
        }
    }

    /// Get the span associated with this error, if any.
    pub fn span(&self) -> Option<Span> {
        match self {
            ParseError::SyntaxError { span, .. } => *span,
            ParseError::UnexpectedToken { span, .. } => Some(*span),
            ParseError::MissingToken { span, .. } => Some(*span),
            ParseError::InvalidPattern { span, .. } => Some(*span),
            ParseError::InvalidType { span, .. } => Some(*span),
            ParseError::UnclosedString { span } => *span,
            ParseError::UnterminatedBlockComment { span } => *span,
            _ => None,
        }
    }

    /// Convert this error to a diagnostic with source context.
    pub fn to_diagnostic(&self) -> Diagnostic {
        match self {
            ParseError::SyntaxError { message, line, column, span } => {
                let mut diag = Diagnostic::error(message.clone())
                    .with_code("E0001");
                if let Some(s) = span {
                    diag = diag.with_label(*s, "syntax error here");
                } else {
                    diag = diag.with_label(
                        Span::new(0, 1, *line, *column),
                        "syntax error here"
                    );
                }
                diag
            }
            ParseError::UnexpectedToken { expected, found, span } => {
                Diagnostic::error(format!("unexpected token: expected {}, found {}", expected, found))
                    .with_code("E0002")
                    .with_label(*span, format!("expected {} here", expected))
                    .with_help(format!("try adding `{}` before this token", expected))
            }
            ParseError::UnexpectedEof => {
                Diagnostic::error("unexpected end of file")
                    .with_code("E0003")
                    .with_note("the file ended unexpectedly")
                    .with_help("check for unclosed brackets or missing statements")
            }
            ParseError::InvalidInteger(s) => {
                Diagnostic::error(format!("invalid integer literal: {}", s))
                    .with_code("E0004")
                    .with_help("integer literals must be valid decimal, hex (0x), octal (0o), or binary (0b) numbers")
            }
            ParseError::InvalidFloat(s) => {
                Diagnostic::error(format!("invalid float literal: {}", s))
                    .with_code("E0005")
                    .with_help("float literals must be valid decimal numbers with optional exponent")
            }
            ParseError::InvalidEscape(s) => {
                Diagnostic::error(format!("invalid escape sequence: {}", s))
                    .with_code("E0006")
                    .with_help("valid escape sequences are: \\n, \\r, \\t, \\\\, \\\", \\'")
            }
            ParseError::UnclosedString { span } => {
                let mut diag = Diagnostic::error("unclosed string literal")
                    .with_code("E0007")
                    .with_help("string literals must be closed with a matching quote");
                if let Some(s) = span {
                    diag = diag.with_label(*s, "string started here but never closed");
                }
                diag
            }
            ParseError::InvalidIndentation { line } => {
                Diagnostic::error("invalid indentation")
                    .with_code("E0008")
                    .with_label(Span::new(0, 1, *line, 1), "invalid indentation here")
                    .with_help("use consistent indentation (spaces or tabs, but not mixed)")
            }
            ParseError::UnterminatedBlockComment { span } => {
                let mut diag = Diagnostic::error("unterminated block comment")
                    .with_code("E0009")
                    .with_help("block comments must be closed with */");
                if let Some(s) = span {
                    diag = diag.with_label(*s, "block comment started here but never closed");
                }
                diag
            }
            ParseError::MissingToken { expected, span } => {
                Diagnostic::error(format!("missing expected token: {}", expected))
                    .with_code("E0010")
                    .with_label(*span, format!("expected {} here", expected))
            }
            ParseError::InvalidPattern { span, message } => {
                Diagnostic::error(format!("invalid pattern: {}", message))
                    .with_code("E0011")
                    .with_label(*span, "invalid pattern here")
            }
            ParseError::InvalidType { span, message } => {
                Diagnostic::error(format!("invalid type: {}", message))
                    .with_code("E0012")
                    .with_label(*span, "invalid type here")
            }
        }
    }

    /// Format this error with source context.
    pub fn format_with_source(&self, source: &str, use_color: bool) -> String {
        self.to_diagnostic().format(source, use_color)
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

    #[test]
    fn test_error_to_diagnostic() {
        let source = "fn main():\n    let x = + 42";
        let err = ParseError::UnexpectedToken {
            expected: "expression".to_string(),
            found: "+".to_string(),
            span: Span::new(20, 21, 2, 13),
        };

        let output = err.format_with_source(source, false);
        assert!(output.contains("error[E0002]"));
        assert!(output.contains("unexpected token"));
        assert!(output.contains("let x = + 42"));
        assert!(output.contains("^"));
    }

    #[test]
    fn test_missing_token_diagnostic() {
        let source = "fn main()\n    return 0";
        let err = ParseError::MissingToken {
            expected: ":".to_string(),
            span: Span::new(9, 10, 1, 10),
        };

        let output = err.format_with_source(source, false);
        assert!(output.contains("error[E0010]"));
        assert!(output.contains("missing expected token"));
    }
}
