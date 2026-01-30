//! Conversion helpers for parser diagnostics to i18n diagnostics
//!
//! This module provides utilities to convert minimal parser diagnostics
//! (from `simple-common`) to full-featured i18n diagnostics (from `simple-diagnostics`).

use simple_common::Diagnostic as ParserDiagnostic;
use simple_diagnostics::{
    Diagnostic as I18nDiagnostic, Span as I18nSpan,
    i18n::{ctx1, ctx2, ContextBuilder},
};

/// Convert a parser diagnostic to an i18n-aware diagnostic
///
/// This function takes a minimal diagnostic from the parser and converts it
/// to a full-featured diagnostic with localized messages.
///
/// # Examples
///
/// ```
/// use simple_common::{Diagnostic, Severity, Span, Label};
/// use simple_driver::diagnostics_conversion::convert_parser_diagnostic;
///
/// // Create a parser diagnostic
/// let span = Span::new(10, 15, 1, 10);
/// let diag = Diagnostic {
///     severity: Severity::Error,
///     code: Some("E0002".to_string()),
///     message: "unexpected token: expected identifier, found +".to_string(),
///     labels: vec![Label::primary(span, "unexpected token")],
///     notes: vec![],
///     help: vec![],
///     file: None,
/// };
///
/// // Convert to i18n diagnostic
/// let i18n_diag = convert_parser_diagnostic(diag);
/// assert_eq!(i18n_diag.code, Some("E0002".to_string()));
/// ```
pub fn convert_parser_diagnostic(diag: ParserDiagnostic) -> I18nDiagnostic {
    // Get primary span from first label (parser diagnostics put span in labels)
    let span = diag
        .labels
        .first()
        .map(|l| I18nSpan::new(l.span.start, l.span.end, l.span.line, l.span.column));

    // Match on error code to provide i18n messages
    match diag.code.as_deref() {
        Some("E0002") => {
            // Unexpected token - extract expected/found from message
            // Message format: "unexpected token: expected X, found Y"
            let (expected, found) = extract_expected_found(&diag.message);

            let ctx = ctx2("expected", expected, "found", found);
            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0002", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0003") => {
            // Unexpected EOF
            let ctx = ContextBuilder::new().build();
            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0003", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0004") => {
            // Invalid integer literal
            let literal = extract_literal(&diag.message);
            let ctx = ctx1("literal", literal);

            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0004", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0005") => {
            // Invalid float literal
            let literal = extract_literal(&diag.message);
            let ctx = ctx1("literal", literal);

            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0005", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0006") => {
            // Invalid escape sequence
            let sequence = extract_sequence(&diag.message);
            let ctx = ctx1("sequence", sequence);

            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0006", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0007") => {
            // Unclosed string literal
            let ctx = ContextBuilder::new().build();
            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0007", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0008") => {
            // Invalid indentation
            let ctx = ContextBuilder::new().build();
            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0008", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0009") => {
            // Unterminated block comment
            let ctx = ContextBuilder::new().build();
            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0009", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0010") => {
            // Missing expected token
            let expected = extract_expected(&diag.message);
            let ctx = ctx1("expected", expected);

            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0010", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0011") => {
            // Invalid pattern
            let message = extract_message_detail(&diag.message);
            let ctx = ctx1("message", message);

            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0011", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some("E0012") => {
            // Invalid type
            let message = extract_message_detail(&diag.message);
            let ctx = ctx1("message", message);

            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0012", &ctx);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            i18n_diag
        }

        Some(code) => {
            // Generic message for unknown codes - use the generic E0001
            let ctx = ctx1("message", diag.message.as_str());
            let mut i18n_diag = I18nDiagnostic::error_i18n("parser", "E0001", &ctx).with_code(code);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            // Add labels, notes, and help from original diagnostic
            for label in &diag.labels[1..] {
                // Skip first label (already used as primary span)
                let label_span = I18nSpan::new(label.span.start, label.span.end, label.span.line, label.span.column);
                i18n_diag = i18n_diag.with_label(label_span, &label.message);
            }

            for note in &diag.notes {
                i18n_diag = i18n_diag.with_note(note);
            }

            for help_msg in &diag.help {
                i18n_diag = i18n_diag.with_help(help_msg);
            }

            i18n_diag
        }

        None => {
            // No error code - create a basic error with the message
            let mut i18n_diag = I18nDiagnostic::error(&diag.message);

            if let Some(s) = span {
                i18n_diag = i18n_diag.with_span(s);
            }

            // Add labels, notes, and help from original diagnostic
            for label in &diag.labels[1..] {
                // Skip first label (already used as primary span)
                let label_span = I18nSpan::new(label.span.start, label.span.end, label.span.line, label.span.column);
                i18n_diag = i18n_diag.with_label(label_span, &label.message);
            }

            for note in &diag.notes {
                i18n_diag = i18n_diag.with_note(note);
            }

            for help_msg in &diag.help {
                i18n_diag = i18n_diag.with_help(help_msg);
            }

            i18n_diag
        }
    }
}

/// Extract expected and found tokens from error message
///
/// Message format: "unexpected token: expected X, found Y"
fn extract_expected_found(message: &str) -> (&str, &str) {
    // Message format: "unexpected token: expected X, found Y"
    // Split by ", " to get: ["unexpected token: expected X", "found Y"]
    let parts: Vec<&str> = message.split(", ").collect();

    // Extract expected from first part: "unexpected token: expected X" -> "X"
    let expected = if let Some(first_part) = parts.first() {
        if let Some((_, after)) = first_part.split_once(": expected ") {
            after
        } else {
            "token"
        }
    } else {
        "token"
    };

    // Extract found from second part: "found Y" -> "Y"
    let found = if let Some(second_part) = parts.get(1) {
        if let Some((_, after)) = second_part.split_once("found ") {
            after
        } else {
            "token"
        }
    } else {
        "token"
    };

    (expected, found)
}

/// Extract expected token from error message
///
/// Message format: "missing expected token: X"
fn extract_expected(message: &str) -> &str {
    message.split(": ").nth(1).unwrap_or("token")
}

/// Extract literal from error message
///
/// Message format: "invalid integer literal: X" or "invalid float literal: X"
fn extract_literal(message: &str) -> &str {
    message.split(": ").nth(1).unwrap_or("<literal>")
}

/// Extract escape sequence from error message
///
/// Message format: "invalid escape sequence: X"
fn extract_sequence(message: &str) -> &str {
    message.split(": ").nth(1).unwrap_or("\\?")
}

/// Extract message detail from error message
///
/// Message format: "invalid pattern: X" or "invalid type: X"
fn extract_message_detail(message: &str) -> &str {
    message.split(": ").nth(1).unwrap_or("<detail>")
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_common::{Diagnostic, Label, Severity, Span};

    #[test]
    fn test_convert_unexpected_token() {
        let parser_diag = Diagnostic {
            severity: Severity::Error,
            code: Some("E0002".to_string()),
            message: "unexpected token: expected identifier, found number".to_string(),
            labels: vec![Label::primary(Span::new(10, 15, 2, 5), "unexpected token")],
            notes: vec![],
            help: vec![],
            file: None,
            easy_fix: None,
        };

        let i18n_diag = convert_parser_diagnostic(parser_diag);

        assert_eq!(i18n_diag.code, Some("E0002".to_string()));
        assert!(i18n_diag.span.is_some());
    }

    #[test]
    fn test_convert_unexpected_eof() {
        let parser_diag = Diagnostic {
            severity: Severity::Error,
            code: Some("E0003".to_string()),
            message: "unexpected end of file".to_string(),
            labels: vec![Label::primary(Span::new(100, 100, 10, 1), "end of file")],
            notes: vec![],
            help: vec![],
            file: None,
            easy_fix: None,
        };

        let i18n_diag = convert_parser_diagnostic(parser_diag);

        assert_eq!(i18n_diag.code, Some("E0003".to_string()));
    }

    #[test]
    fn test_extract_expected_found() {
        let (expected, found) = extract_expected_found("unexpected token: expected identifier, found number");
        assert_eq!(expected, "identifier");
        assert_eq!(found, "number");
    }

    #[test]
    fn test_extract_literal() {
        let literal = extract_literal("invalid integer literal: 123abc");
        assert_eq!(literal, "123abc");
    }
}
