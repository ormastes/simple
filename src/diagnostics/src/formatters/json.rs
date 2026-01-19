//! JSON formatter for machine-readable diagnostic output
//!
//! Provides structured JSON output for tools, IDEs, and LLM integration.

use crate::Diagnostic;
use serde_json::json;

/// JSON formatter for structured diagnostic output
pub struct JsonFormatter {
    pretty: bool,
}

impl JsonFormatter {
    /// Create a new JSON formatter (compact output)
    pub fn new() -> Self {
        Self { pretty: false }
    }

    /// Create a formatter with pretty-printed JSON
    pub fn pretty() -> Self {
        Self { pretty: true }
    }

    /// Format a single diagnostic as JSON
    pub fn format(&self, diagnostic: &Diagnostic) -> String {
        let value = self.diagnostic_to_json(diagnostic);

        if self.pretty {
            serde_json::to_string_pretty(&value).unwrap_or_else(|_| "{}".to_string())
        } else {
            serde_json::to_string(&value).unwrap_or_else(|_| "{}".to_string())
        }
    }

    /// Format multiple diagnostics as JSON array
    pub fn format_multiple(&self, diagnostics: &[Diagnostic]) -> String {
        let values: Vec<_> = diagnostics
            .iter()
            .map(|d| self.diagnostic_to_json(d))
            .collect();

        if self.pretty {
            serde_json::to_string_pretty(&values).unwrap_or_else(|_| "[]".to_string())
        } else {
            serde_json::to_string(&values).unwrap_or_else(|_| "[]".to_string())
        }
    }

    fn diagnostic_to_json(&self, diagnostic: &Diagnostic) -> serde_json::Value {
        let mut obj = json!({
            "severity": diagnostic.severity.name(),
            "message": diagnostic.message,
        });

        if let Some(code) = &diagnostic.code {
            obj["code"] = json!(code);
        }

        if let Some(span) = diagnostic.span {
            obj["span"] = json!({
                "start": span.start,
                "end": span.end,
                "line": span.line,
                "column": span.column,
            });
        }

        if !diagnostic.labels.is_empty() {
            obj["labels"] = json!(diagnostic.labels.iter().map(|label| {
                json!({
                    "span": {
                        "start": label.span.start,
                        "end": label.span.end,
                        "line": label.span.line,
                        "column": label.span.column,
                    },
                    "message": label.message,
                })
            }).collect::<Vec<_>>());
        }

        if !diagnostic.notes.is_empty() {
            obj["notes"] = json!(diagnostic.notes);
        }

        if let Some(help) = &diagnostic.help {
            obj["help"] = json!(help);
        }

        obj
    }
}

impl Default for JsonFormatter {
    fn default() -> Self {
        Self::new()
    }
}

impl super::DiagnosticFormatter for JsonFormatter {
    fn format_diagnostic(&self, diagnostic: &Diagnostic, _source: &str) -> String {
        self.format(diagnostic)
    }

    fn format_diagnostics(&self, diagnostics: &[Diagnostic], _source: &str) -> String {
        self.format_multiple(diagnostics)
    }
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

        let formatter = JsonFormatter::new();
        let output = formatter.format(&diag);

        let parsed: serde_json::Value = serde_json::from_str(&output).unwrap();
        assert_eq!(parsed["severity"], "error");
        assert_eq!(parsed["code"], "E0001");
        assert_eq!(parsed["message"], "unexpected token");
        assert_eq!(parsed["span"]["line"], 1);
    }

    #[test]
    fn test_format_with_labels() {
        let span = Span::new(10, 15, 2, 5);
        let diag = Diagnostic::error("type mismatch")
            .with_code("E0002")
            .with_span(span)
            .with_label(span, "expected i32");

        let formatter = JsonFormatter::new();
        let output = formatter.format(&diag);

        let parsed: serde_json::Value = serde_json::from_str(&output).unwrap();
        assert!(parsed["labels"].is_array());
        assert_eq!(parsed["labels"][0]["message"], "expected i32");
    }

    #[test]
    fn test_format_with_help_and_notes() {
        let diag = Diagnostic::warning("unused variable")
            .with_note("variable `x` is never used")
            .with_help("consider prefixing with underscore");

        let formatter = JsonFormatter::new();
        let output = formatter.format(&diag);

        let parsed: serde_json::Value = serde_json::from_str(&output).unwrap();
        assert!(parsed["notes"].is_array());
        assert_eq!(parsed["notes"][0], "variable `x` is never used");
        assert_eq!(parsed["help"], "consider prefixing with underscore");
    }

    #[test]
    fn test_format_multiple() {
        let diag1 = Diagnostic::error("error 1").with_code("E0001");
        let diag2 = Diagnostic::warning("warning 1").with_code("W0001");

        let formatter = JsonFormatter::new();
        let output = formatter.format_multiple(&[diag1, diag2]);

        let parsed: serde_json::Value = serde_json::from_str(&output).unwrap();
        assert!(parsed.is_array());
        assert_eq!(parsed.as_array().unwrap().len(), 2);
        assert_eq!(parsed[0]["severity"], "error");
        assert_eq!(parsed[1]["severity"], "warning");
    }

    #[test]
    fn test_pretty_formatting() {
        let diag = Diagnostic::error("test").with_code("E0001");

        let formatter = JsonFormatter::pretty();
        let output = formatter.format(&diag);

        // Pretty-printed JSON should contain newlines
        assert!(output.contains('\n'));
    }
}
