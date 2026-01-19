//! Simple language formatter for diagnostic output
//!
//! Provides diagnostic output in Simple language syntax for specs and tests.

use crate::{Diagnostic, Severity};

/// Simple language formatter for spec-compatible output
pub struct SimpleFormatter {
    /// Whether to use Simple language syntax or plain text
    simple_syntax: bool,
}

impl SimpleFormatter {
    /// Create a new Simple formatter
    pub fn new() -> Self {
        Self {
            simple_syntax: true,
        }
    }

    /// Format a diagnostic in Simple language syntax
    pub fn format(&self, diagnostic: &Diagnostic) -> String {
        if self.simple_syntax {
            self.format_as_simple_syntax(diagnostic)
        } else {
            self.format_as_plain_text(diagnostic)
        }
    }

    fn format_as_simple_syntax(&self, diagnostic: &Diagnostic) -> String {
        let mut output = String::new();

        // Create a Diagnostic struct initialization in Simple syntax
        output.push_str("Diagnostic(\n");

        // Severity
        let severity_variant = match diagnostic.severity {
            Severity::Error => "Error",
            Severity::Warning => "Warning",
            Severity::Note => "Note",
            Severity::Help => "Help",
            Severity::Info => "Info",
        };
        output.push_str(&format!("  severity: Severity.{},\n", severity_variant));

        // Code
        if let Some(code) = &diagnostic.code {
            output.push_str(&format!("  code: \"{}\",\n", code));
        }

        // Message
        output.push_str(&format!("  message: \"{}\",\n", escape_string(&diagnostic.message)));

        // Span
        if let Some(span) = diagnostic.span {
            output.push_str(&format!(
                "  span: Span(start: {}, end: {}, line: {}, column: {}),\n",
                span.start, span.end, span.line, span.column
            ));
        }

        // Labels
        if !diagnostic.labels.is_empty() {
            output.push_str("  labels: [\n");
            for label in &diagnostic.labels {
                output.push_str(&format!(
                    "    Label(span: Span(start: {}, end: {}, line: {}, column: {}), message: \"{}\"),\n",
                    label.span.start,
                    label.span.end,
                    label.span.line,
                    label.span.column,
                    escape_string(&label.message)
                ));
            }
            output.push_str("  ],\n");
        }

        // Notes
        if !diagnostic.notes.is_empty() {
            output.push_str("  notes: [\n");
            for note in &diagnostic.notes {
                output.push_str(&format!("    \"{}\",\n", escape_string(note)));
            }
            output.push_str("  ],\n");
        }

        // Help
        if let Some(help) = &diagnostic.help {
            output.push_str(&format!("  help: \"{}\",\n", escape_string(help)));
        }

        output.push_str(")");

        output
    }

    fn format_as_plain_text(&self, diagnostic: &Diagnostic) -> String {
        let mut output = String::new();

        // Header: severity[code]: message
        let severity_str = diagnostic.severity.display_name();

        if let Some(code) = &diagnostic.code {
            output.push_str(&format!("{}[{}]: {}", severity_str, code, diagnostic.message));
        } else {
            output.push_str(&format!("{}: {}", severity_str, diagnostic.message));
        }

        // Span info
        if let Some(span) = diagnostic.span {
            output.push_str(&format!(
                " (at line {}, column {})",
                span.line, span.column
            ));
        }

        // Labels
        for label in &diagnostic.labels {
            output.push_str(&format!(
                "\n  - {} (line {}, column {})",
                label.message, label.span.line, label.span.column
            ));
        }

        // Notes
        for note in &diagnostic.notes {
            output.push_str(&format!("\n  note: {}", note));
        }

        // Help
        if let Some(help) = &diagnostic.help {
            output.push_str(&format!("\n  help: {}", help));
        }

        output
    }
}

impl Default for SimpleFormatter {
    fn default() -> Self {
        Self::new()
    }
}

impl super::DiagnosticFormatter for SimpleFormatter {
    fn format_diagnostic(&self, diagnostic: &Diagnostic, _source: &str) -> String {
        self.format(diagnostic)
    }
}

/// Escape special characters in strings for Simple syntax
fn escape_string(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Diagnostic, Span};

    #[test]
    fn test_format_basic_error() {
        let diag = Diagnostic::error("unexpected token")
            .with_code("E0001")
            .with_span(Span::new(0, 5, 1, 1));

        let formatter = SimpleFormatter::new();
        let output = formatter.format(&diag);

        assert!(output.contains("Diagnostic("));
        assert!(output.contains("severity: Severity.Error"));
        assert!(output.contains("code: \"E0001\""));
        assert!(output.contains("message: \"unexpected token\""));
    }

    #[test]
    fn test_format_with_label() {
        let span = Span::new(10, 15, 2, 5);
        let diag = Diagnostic::error("type mismatch")
            .with_span(span)
            .with_label(span, "expected i32");

        let formatter = SimpleFormatter::new();
        let output = formatter.format(&diag);

        assert!(output.contains("labels: ["));
        assert!(output.contains("Label("));
        assert!(output.contains("expected i32"));
    }

    #[test]
    fn test_format_with_notes_and_help() {
        let diag = Diagnostic::warning("unused variable")
            .with_note("variable `x` is never used")
            .with_help("consider prefixing with underscore");

        let formatter = SimpleFormatter::new();
        let output = formatter.format(&diag);

        assert!(output.contains("notes: ["));
        assert!(output.contains("variable `x` is never used"));
        assert!(output.contains("help: \"consider prefixing with underscore\""));
    }

    #[test]
    fn test_escape_string() {
        assert_eq!(escape_string("hello"), "hello");
        assert_eq!(escape_string("hello\nworld"), "hello\\nworld");
        assert_eq!(escape_string("say \"hello\""), "say \\\"hello\\\"");
        assert_eq!(escape_string("path\\to\\file"), "path\\\\to\\\\file");
    }
}
