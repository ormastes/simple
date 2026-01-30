use crate::diagnostic::{Diagnostic, DiagnosticParserExt};
use crate::token::Span;
use thiserror::Error;

/// Context information for parse errors
#[derive(Debug, Clone)]
pub struct ParseContext {
    pub file: String,
    pub function: String,
    pub line: u32,
    pub column: u32,
    pub parser_state: Option<String>,
}

impl ParseContext {
    pub fn new(file: &str, function: &str, line: u32, column: u32) -> Self {
        Self {
            file: file.to_string(),
            function: function.to_string(),
            line,
            column,
            parser_state: None,
        }
    }

    pub fn with_state(mut self, state: String) -> Self {
        self.parser_state = Some(state);
        self
    }
}

/// Macro to capture parse context at call site
#[macro_export]
macro_rules! parse_context {
    () => {
        $crate::error::ParseContext::new(file!(), concat!(module_path!(), "::", line!()), line!(), column!())
    };
    ($state:expr) => {
        $crate::error::ParseContext::new(file!(), concat!(module_path!(), "::", line!()), line!(), column!())
            .with_state($state.to_string())
    };
}

/// Parse error with span information for diagnostics.
#[derive(Error, Debug, Clone)]
pub enum ParseError {
    #[error("Syntax error at {line}:{column}: {message}")]
    SyntaxError {
        message: String,
        line: usize,
        column: usize,
        span: Option<Span>,
        context: Option<ParseContext>,
    },

    #[error("Unexpected token: expected {expected}, found {found}")]
    UnexpectedToken {
        expected: String,
        found: String,
        span: Span,
        context: Option<ParseContext>,
    },

    #[error("Unexpected end of file")]
    UnexpectedEof { context: Option<ParseContext> },

    #[error("Invalid integer literal: {0}")]
    InvalidInteger(String, Option<ParseContext>),

    #[error("Invalid float literal: {0}")]
    InvalidFloat(String, Option<ParseContext>),

    #[error("Invalid escape sequence: {0}")]
    InvalidEscape(String, Option<ParseContext>),

    #[error("Unclosed string literal")]
    UnclosedString {
        span: Option<Span>,
        context: Option<ParseContext>,
    },

    #[error("Invalid indentation")]
    InvalidIndentation { line: usize, context: Option<ParseContext> },

    #[error("Unterminated block comment")]
    UnterminatedBlockComment {
        span: Option<Span>,
        context: Option<ParseContext>,
    },

    #[error("Missing expected token: {expected}")]
    MissingToken {
        expected: String,
        span: Span,
        context: Option<ParseContext>,
    },

    #[error("Invalid pattern")]
    InvalidPattern {
        span: Span,
        message: String,
        context: Option<ParseContext>,
    },

    #[error("Invalid type")]
    InvalidType {
        span: Span,
        message: String,
        context: Option<ParseContext>,
    },

    #[error("{context}: {message}")]
    ContextualSyntaxError {
        /// Context where error occurred (e.g., "dict literal", "function arguments", "struct initialization")
        context: String,
        /// Error message
        message: String,
        /// Span of the error
        span: Span,
        /// Optional suggestion for fixing
        suggestion: Option<String>,
        /// Optional help text
        help: Option<String>,
        /// Parser context (for debugging)
        parse_context: Option<ParseContext>,
    },
}

impl ParseError {
    pub fn syntax_error(message: impl Into<String>, line: usize, column: usize) -> Self {
        Self::SyntaxError {
            message: message.into(),
            line,
            column,
            span: None,
            context: None,
        }
    }

    pub fn syntax_error_with_span(message: impl Into<String>, span: Span) -> Self {
        Self::SyntaxError {
            message: message.into(),
            line: span.line,
            column: span.column,
            span: Some(span),
            context: None,
        }
    }

    pub fn syntax_error_with_context(message: impl Into<String>, span: Span, context: ParseContext) -> Self {
        Self::SyntaxError {
            message: message.into(),
            line: span.line,
            column: span.column,
            span: Some(span),
            context: Some(context),
        }
    }

    pub fn unexpected_token(expected: impl Into<String>, found: impl Into<String>, span: Span) -> Self {
        Self::UnexpectedToken {
            expected: expected.into(),
            found: found.into(),
            span,
            context: None,
        }
    }

    pub fn unexpected_token_with_context(
        expected: impl Into<String>,
        found: impl Into<String>,
        span: Span,
        context: ParseContext,
    ) -> Self {
        Self::UnexpectedToken {
            expected: expected.into(),
            found: found.into(),
            span,
            context: Some(context),
        }
    }

    pub fn missing_token(expected: impl Into<String>, span: Span) -> Self {
        Self::MissingToken {
            expected: expected.into(),
            span,
            context: None,
        }
    }

    pub fn missing_token_with_context(expected: impl Into<String>, span: Span, context: ParseContext) -> Self {
        Self::MissingToken {
            expected: expected.into(),
            span,
            context: Some(context),
        }
    }

    pub fn contextual_error(
        context: impl Into<String>,
        message: impl Into<String>,
        span: Span,
    ) -> Self {
        Self::ContextualSyntaxError {
            context: context.into(),
            message: message.into(),
            span,
            suggestion: None,
            help: None,
            parse_context: None,
        }
    }

    pub fn contextual_error_with_suggestion(
        context: impl Into<String>,
        message: impl Into<String>,
        span: Span,
        suggestion: impl Into<String>,
    ) -> Self {
        Self::ContextualSyntaxError {
            context: context.into(),
            message: message.into(),
            span,
            suggestion: Some(suggestion.into()),
            help: None,
            parse_context: None,
        }
    }

    pub fn contextual_error_with_help(
        context: impl Into<String>,
        message: impl Into<String>,
        span: Span,
        suggestion: Option<String>,
        help: impl Into<String>,
    ) -> Self {
        Self::ContextualSyntaxError {
            context: context.into(),
            message: message.into(),
            span,
            suggestion,
            help: Some(help.into()),
            parse_context: None,
        }
    }

    /// Add context to an existing error
    pub fn with_context(self, context: ParseContext) -> Self {
        match self {
            Self::SyntaxError {
                message,
                line,
                column,
                span,
                context: _,
            } => Self::SyntaxError {
                message,
                line,
                column,
                span,
                context: Some(context),
            },
            Self::UnexpectedToken {
                expected,
                found,
                span,
                context: _,
            } => Self::UnexpectedToken {
                expected,
                found,
                span,
                context: Some(context),
            },
            Self::UnexpectedEof { context: _ } => Self::UnexpectedEof { context: Some(context) },
            Self::InvalidInteger(s, _) => Self::InvalidInteger(s, Some(context)),
            Self::InvalidFloat(s, _) => Self::InvalidFloat(s, Some(context)),
            Self::InvalidEscape(s, _) => Self::InvalidEscape(s, Some(context)),
            Self::UnclosedString { span, context: _ } => Self::UnclosedString {
                span,
                context: Some(context),
            },
            Self::InvalidIndentation { line, context: _ } => Self::InvalidIndentation {
                line,
                context: Some(context),
            },
            Self::UnterminatedBlockComment { span, context: _ } => Self::UnterminatedBlockComment {
                span,
                context: Some(context),
            },
            Self::MissingToken {
                expected,
                span,
                context: _,
            } => Self::MissingToken {
                expected,
                span,
                context: Some(context),
            },
            Self::InvalidPattern {
                span,
                message,
                context: _,
            } => Self::InvalidPattern {
                span,
                message,
                context: Some(context),
            },
            Self::InvalidType {
                span,
                message,
                context: _,
            } => Self::InvalidType {
                span,
                message,
                context: Some(context),
            },
            Self::ContextualSyntaxError {
                context: ctx,
                message,
                span,
                suggestion,
                help,
                parse_context: _,
            } => Self::ContextualSyntaxError {
                context: ctx,
                message,
                span,
                suggestion,
                help,
                parse_context: Some(context),
            },
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
            ParseError::UnclosedString { span, .. } => *span,
            ParseError::UnterminatedBlockComment { span, .. } => *span,
            ParseError::ContextualSyntaxError { span, .. } => Some(*span),
            _ => None,
        }
    }

    /// Get the context associated with this error, if any.
    pub fn context(&self) -> Option<&ParseContext> {
        match self {
            ParseError::SyntaxError { context, .. } => context.as_ref(),
            ParseError::UnexpectedToken { context, .. } => context.as_ref(),
            ParseError::UnexpectedEof { context } => context.as_ref(),
            ParseError::InvalidInteger(_, context) => context.as_ref(),
            ParseError::InvalidFloat(_, context) => context.as_ref(),
            ParseError::InvalidEscape(_, context) => context.as_ref(),
            ParseError::UnclosedString { context, .. } => context.as_ref(),
            ParseError::InvalidIndentation { context, .. } => context.as_ref(),
            ParseError::UnterminatedBlockComment { context, .. } => context.as_ref(),
            ParseError::MissingToken { context, .. } => context.as_ref(),
            ParseError::InvalidPattern { context, .. } => context.as_ref(),
            ParseError::InvalidType { context, .. } => context.as_ref(),
            ParseError::ContextualSyntaxError { parse_context, .. } => parse_context.as_ref(),
        }
    }

    /// Convert this error to a diagnostic with source context.
    pub fn to_diagnostic(&self) -> Diagnostic {
        let add_context = |mut diag: Diagnostic, ctx: Option<&ParseContext>| {
            if let Some(context) = ctx {
                diag = diag.with_note(format!(
                    "Parser location: {}:{}:{} in {}",
                    context.file, context.line, context.column, context.function
                ));
                if let Some(state) = &context.parser_state {
                    diag = diag.with_note(format!("Parser state: {}", state));
                }
            }
            diag
        };

        match self {
            ParseError::SyntaxError {
                message,
                line,
                column,
                span,
                context,
            } => {
                let mut diag = Diagnostic::error(message.clone()).with_code("E0001");
                if let Some(s) = span {
                    diag = diag.with_parser_label(*s, "syntax error here");
                } else {
                    diag = diag.with_parser_label(Span::new(0, 1, *line, *column), "syntax error here");
                }
                add_context(diag, context.as_ref())
            }
            ParseError::UnexpectedToken {
                expected,
                found,
                span,
                context,
            } => {
                let diag = Diagnostic::error(format!("unexpected token: expected {}, found {}", expected, found))
                    .with_code("E0002")
                    .with_parser_label(*span, format!("expected {} here", expected))
                    .with_help(format!("try adding `{}` before this token", expected));
                add_context(diag, context.as_ref())
            }
            ParseError::UnexpectedEof { context } => {
                let diag = Diagnostic::error("unexpected end of file")
                    .with_code("E0003")
                    .with_note("the file ended unexpectedly")
                    .with_help("check for unclosed brackets or missing statements");
                add_context(diag, context.as_ref())
            }
            ParseError::InvalidInteger(s, context) => {
                let diag = Diagnostic::error(format!("invalid integer literal: {}", s))
                    .with_code("E0004")
                    .with_help("integer literals must be valid decimal, hex (0x), octal (0o), or binary (0b) numbers");
                add_context(diag, context.as_ref())
            }
            ParseError::InvalidFloat(s, context) => {
                let diag = Diagnostic::error(format!("invalid float literal: {}", s))
                    .with_code("E0005")
                    .with_help("float literals must be valid decimal numbers with optional exponent");
                add_context(diag, context.as_ref())
            }
            ParseError::InvalidEscape(s, context) => {
                let diag = Diagnostic::error(format!("invalid escape sequence: {}", s))
                    .with_code("E0006")
                    .with_help("valid escape sequences are: \\n, \\r, \\t, \\\\, \\\", \\'");
                add_context(diag, context.as_ref())
            }
            ParseError::UnclosedString { span, context } => {
                let mut diag = Diagnostic::error("unclosed string literal")
                    .with_code("E0007")
                    .with_help("string literals must be closed with a matching quote");
                if let Some(s) = span {
                    diag = diag.with_parser_label(*s, "string started here but never closed");
                }
                add_context(diag, context.as_ref())
            }
            ParseError::InvalidIndentation { line, context } => {
                let diag = Diagnostic::error("invalid indentation")
                    .with_code("E0008")
                    .with_parser_label(Span::new(0, 1, *line, 1), "invalid indentation here")
                    .with_help("use consistent indentation (spaces or tabs, but not mixed)");
                add_context(diag, context.as_ref())
            }
            ParseError::UnterminatedBlockComment { span, context } => {
                let mut diag = Diagnostic::error("unterminated block comment")
                    .with_code("E0009")
                    .with_help("block comments must be closed with */");
                if let Some(s) = span {
                    diag = diag.with_parser_label(*s, "block comment started here but never closed");
                }
                add_context(diag, context.as_ref())
            }
            ParseError::MissingToken {
                expected,
                span,
                context,
            } => {
                let diag = Diagnostic::error(format!("missing expected token: {}", expected))
                    .with_code("E0010")
                    .with_parser_label(*span, format!("expected {} here", expected));
                add_context(diag, context.as_ref())
            }
            ParseError::InvalidPattern { span, message, context } => {
                let diag = Diagnostic::error(format!("invalid pattern: {}", message))
                    .with_code("E0011")
                    .with_parser_label(*span, "invalid pattern here");
                add_context(diag, context.as_ref())
            }
            ParseError::InvalidType { span, message, context } => {
                let diag = Diagnostic::error(format!("invalid type: {}", message))
                    .with_code("E0012")
                    .with_parser_label(*span, "invalid type here");
                add_context(diag, context.as_ref())
            }
            ParseError::ContextualSyntaxError {
                context: ctx,
                message,
                span,
                suggestion,
                help,
                parse_context,
            } => {
                let mut diag = Diagnostic::error(format!("{}: {}", ctx, message))
                    .with_code("E0013")
                    .with_parser_label(*span, message.clone());

                if let Some(ref sugg) = suggestion {
                    diag = diag.with_note(format!("Suggestion: {}", sugg));
                }
                if let Some(ref h) = help {
                    diag = diag.with_help(h.clone());
                }
                add_context(diag, parse_context.as_ref())
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
            context: None,
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
            context: None,
        };

        let output = err.format_with_source(source, false);
        assert!(output.contains("error[E0010]"));
        assert!(output.contains("missing expected token"));
    }
}
