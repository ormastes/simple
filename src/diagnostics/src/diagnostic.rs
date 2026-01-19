//! Core diagnostic type with i18n support

use crate::{Severity, Span};
use serde::{Deserialize, Serialize};
use simple_i18n::{I18n, MessageContext};

/// A labeled span within a diagnostic
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

impl Label {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
        }
    }
}

/// A diagnostic message (error, warning, note, etc.)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: Option<String>,
    pub message: String,
    pub span: Option<Span>,
    pub labels: Vec<Label>,
    pub notes: Vec<String>,
    pub help: Option<String>,
}

impl Diagnostic {
    /// Create a new diagnostic with the given severity and message
    pub fn new(severity: Severity, message: impl Into<String>) -> Self {
        Self {
            severity,
            code: None,
            message: message.into(),
            span: None,
            labels: Vec::new(),
            notes: Vec::new(),
            help: None,
        }
    }

    /// Create an error diagnostic
    pub fn error(message: impl Into<String>) -> Self {
        Self::new(Severity::Error, message)
    }

    /// Create a warning diagnostic
    pub fn warning(message: impl Into<String>) -> Self {
        Self::new(Severity::Warning, message)
    }

    /// Create a note diagnostic
    pub fn note(message: impl Into<String>) -> Self {
        Self::new(Severity::Note, message)
    }

    /// Create a help diagnostic
    pub fn help(message: impl Into<String>) -> Self {
        Self::new(Severity::Help, message)
    }

    /// Create an info diagnostic
    pub fn info(message: impl Into<String>) -> Self {
        Self::new(Severity::Info, message)
    }

    /// Create a diagnostic from an i18n message ID
    ///
    /// This looks up the message in the i18n catalog and interpolates it with the context.
    /// Falls back to English if the translation is not available.
    pub fn from_i18n(
        severity: Severity,
        domain: &str,
        id: &str,
        ctx: &MessageContext,
    ) -> Self {
        let i18n = I18n::global();
        let msg = i18n.get_message_safe(domain, id, ctx);

        let mut diag = Self::new(severity, &msg.message).with_code(id);

        // Add label if provided in the message
        if let Some(label_text) = msg.label {
            // Note: span will be added later via with_label() or with_span()
            // For now, we store the label text and it will be attached when span is known
            diag.help = Some(label_text);
        }

        // Add help text
        if let Some(help_text) = msg.help {
            diag = diag.with_help(&help_text);
        }

        // Add notes
        if let Some(note_text) = msg.note {
            diag = diag.with_note(&note_text);
        }

        diag
    }

    /// Create an error diagnostic from i18n
    pub fn error_i18n(domain: &str, id: &str, ctx: &MessageContext) -> Self {
        Self::from_i18n(Severity::Error, domain, id, ctx)
    }

    /// Create a warning diagnostic from i18n
    pub fn warning_i18n(domain: &str, id: &str, ctx: &MessageContext) -> Self {
        Self::from_i18n(Severity::Warning, domain, id, ctx)
    }

    /// Create a note diagnostic from i18n
    pub fn note_i18n(domain: &str, id: &str, ctx: &MessageContext) -> Self {
        Self::from_i18n(Severity::Note, domain, id, ctx)
    }

    /// Set the error code (e.g., "E0001")
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    /// Set the primary span
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Add a labeled span
    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label::new(span, message));
        self
    }

    /// Add a labeled span from i18n
    ///
    /// This looks up the label message in the i18n catalog and interpolates it.
    pub fn with_label_i18n(
        mut self,
        span: Span,
        domain: &str,
        label_key: &str,
        ctx: &MessageContext,
    ) -> Self {
        let i18n = I18n::global();
        let label_msg = i18n.get_message_safe(domain, label_key, ctx);
        self.labels.push(Label::new(span, label_msg.message));
        self
    }

    /// Add a note
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Set the help message
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    /// Format this diagnostic as colored text for terminal output
    pub fn format(&self, source: &str, use_color: bool) -> String {
        use crate::formatters::TextFormatter;

        let formatter = if use_color {
            TextFormatter::new()
        } else {
            TextFormatter::without_color()
        };

        formatter.format(self, source)
    }

    /// Format this diagnostic as JSON
    pub fn format_json(&self) -> String {
        use crate::formatters::JsonFormatter;

        let formatter = JsonFormatter::new();
        formatter.format(self)
    }

    /// Format this diagnostic as Simple language syntax
    pub fn format_simple(&self) -> String {
        use crate::formatters::SimpleFormatter;

        let formatter = SimpleFormatter::new();
        formatter.format(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_diagnostic_basic() {
        let diag = Diagnostic::error("unexpected token")
            .with_code("E0001")
            .with_span(Span::new(0, 5, 1, 1));

        assert_eq!(diag.severity, Severity::Error);
        assert_eq!(diag.code, Some("E0001".to_string()));
        assert_eq!(diag.message, "unexpected token");
        assert!(diag.span.is_some());
    }

    #[test]
    fn test_diagnostic_with_label() {
        let span = Span::new(10, 15, 2, 5);
        let diag = Diagnostic::error("type mismatch")
            .with_label(span, "expected i32, found bool");

        assert_eq!(diag.labels.len(), 1);
        assert_eq!(diag.labels[0].span, span);
        assert_eq!(diag.labels[0].message, "expected i32, found bool");
    }

    #[test]
    fn test_diagnostic_with_note_and_help() {
        let diag = Diagnostic::warning("unused variable")
            .with_note("variable `x` is never used")
            .with_help("consider prefixing with an underscore: `_x`");

        assert_eq!(diag.notes.len(), 1);
        assert_eq!(diag.notes[0], "variable `x` is never used");
        assert_eq!(diag.help, Some("consider prefixing with an underscore: `_x`".to_string()));
    }

    #[test]
    fn test_diagnostic_i18n_fallback() {
        // Without setting locale, should fall back to English bootstrap messages
        let mut ctx = MessageContext::new();
        ctx.insert("expected", "identifier");
        ctx.insert("found", "number");

        let diag = Diagnostic::error_i18n("parser", "E0002", &ctx);

        // Should have created a diagnostic even if message not in catalog (fallback)
        assert_eq!(diag.severity, Severity::Error);
        assert_eq!(diag.code, Some("E0002".to_string()));
        assert!(!diag.message.is_empty());
    }

    #[test]
    fn test_diagnostic_serialization() {
        let diag = Diagnostic::error("test error")
            .with_code("E0001")
            .with_span(Span::new(0, 5, 1, 1))
            .with_label(Span::new(0, 5, 1, 1), "here")
            .with_note("note text")
            .with_help("help text");

        // Should serialize to JSON successfully
        let json = serde_json::to_value(&diag).unwrap();
        assert!(json.is_object());

        // Should deserialize back
        let deserialized: Diagnostic = serde_json::from_value(json).unwrap();
        assert_eq!(deserialized, diag);
    }
}
