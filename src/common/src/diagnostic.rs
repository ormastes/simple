//! Rust-style diagnostic messages for the Simple language.
//!
//! This module provides rich error messages with:
//! - Source code context with line numbers
//! - Colored output (error=red, warning=yellow, note=blue, help=green)
//! - Underlines pointing to the exact error location
//! - Support for notes, hints, and help messages
//!
//! Example output:
//! ```text
//! error[E0001]: unexpected token
//!   --> src/main.spl:5:10
//!    |
//!  5 |     let x = + 42
//!    |             ^ expected expression, found `+`
//!    |
//!    = help: expressions cannot start with an operator
//! ```

use std::fmt;

/// Source location span (line, column, offset)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Span {
    /// Create a new span
    pub fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
        }
    }

    /// Create a zero-length span at the given position
    pub fn at(pos: usize, line: usize, column: usize) -> Self {
        Self {
            start: pos,
            end: pos,
            line,
            column,
        }
    }

    /// Combine two spans into one covering both
    pub fn to(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line.min(other.line),
            column: self.column,
        }
    }
}

/// Severity level of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    /// Fatal error that prevents compilation
    Error,
    /// Warning that doesn't prevent compilation
    Warning,
    /// Informational note
    Note,
    /// Helpful suggestion
    Help,
}

impl Severity {
    /// Get the display name for this severity.
    pub fn name(&self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
            Severity::Help => "help",
        }
    }

    /// Get the ANSI color code for this severity.
    pub fn color(&self) -> &'static str {
        match self {
            Severity::Error => "\x1b[1;31m",   // Bold red
            Severity::Warning => "\x1b[1;33m", // Bold yellow
            Severity::Note => "\x1b[1;36m",    // Bold cyan
            Severity::Help => "\x1b[1;32m",    // Bold green
        }
    }
}

/// A label attached to a span in the source code.
#[derive(Debug, Clone)]
pub struct Label {
    /// The span this label points to
    pub span: Span,
    /// The message for this label
    pub message: String,
    /// Whether this is the primary label (shown with ^^^)
    pub primary: bool,
}

impl Label {
    /// Create a new primary label.
    pub fn primary(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
            primary: true,
        }
    }

    /// Create a new secondary label.
    pub fn secondary(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
            primary: false,
        }
    }
}

/// A diagnostic message with source context.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// The severity of this diagnostic
    pub severity: Severity,
    /// Error code (e.g., "E0001")
    pub code: Option<String>,
    /// The main message
    pub message: String,
    /// Labels pointing to source locations
    pub labels: Vec<Label>,
    /// Additional notes
    pub notes: Vec<String>,
    /// Help suggestions
    pub help: Vec<String>,
    /// The file path (optional)
    pub file: Option<String>,
}

impl Diagnostic {
    /// Create a new diagnostic with the given severity and message.
    pub fn new(severity: Severity, message: impl Into<String>) -> Self {
        Self {
            severity,
            code: None,
            message: message.into(),
            labels: Vec::new(),
            notes: Vec::new(),
            help: Vec::new(),
            file: None,
        }
    }

    /// Create a new error diagnostic.
    pub fn error(message: impl Into<String>) -> Self {
        Self::new(Severity::Error, message)
    }

    /// Create a new warning diagnostic.
    pub fn warning(message: impl Into<String>) -> Self {
        Self::new(Severity::Warning, message)
    }

    /// Set the error code.
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    /// Set the file path.
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    /// Add a primary label.
    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label::primary(span, message));
        self
    }

    /// Add a secondary label.
    pub fn with_secondary_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label::secondary(span, message));
        self
    }

    /// Add a note.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Add a help suggestion.
    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help.push(help.into());
        self
    }

    /// Format this diagnostic with source code context.
    pub fn format(&self, source: &str, use_color: bool) -> String {
        let mut output = String::new();

        // Color codes
        let reset = if use_color { "\x1b[0m" } else { "" };
        let bold = if use_color { "\x1b[1m" } else { "" };
        let blue = if use_color { "\x1b[1;34m" } else { "" };
        let severity_color = if use_color { self.severity.color() } else { "" };

        // Header: error[E0001]: message
        output.push_str(&format!(
            "{}{}{}{}: {}{}",
            severity_color,
            self.severity.name(),
            self.code
                .as_ref()
                .map(|c| format!("[{}]", c))
                .unwrap_or_default(),
            reset,
            bold,
            self.message
        ));
        output.push_str(reset);
        output.push('\n');

        // Source location and context for each label
        let lines: Vec<&str> = source.lines().collect();

        for label in &self.labels {
            // Location: --> file:line:column
            let file = self.file.as_deref().unwrap_or("<source>");
            output.push_str(&format!(
                "  {}-->{} {}:{}:{}\n",
                blue, reset, file, label.span.line, label.span.column
            ));

            // Show source line with line number
            if label.span.line > 0 && label.span.line <= lines.len() {
                let line_num = label.span.line;
                let line_str = lines[line_num - 1];
                let line_num_width = format!("{}", line_num).len().max(2);

                // Empty line with just the bar
                output.push_str(&format!(
                    "  {:>width$} {}|{}\n",
                    "",
                    blue,
                    reset,
                    width = line_num_width
                ));

                // The source line
                output.push_str(&format!(
                    "  {}{:>width$}{} {}|{} {}\n",
                    blue,
                    line_num,
                    reset,
                    blue,
                    reset,
                    line_str,
                    width = line_num_width
                ));

                // The underline with message
                let underline_char = if label.primary { '^' } else { '-' };
                let underline_color = if label.primary { severity_color } else { blue };

                // Calculate underline position and length
                let col = label.span.column.saturating_sub(1);
                let len = (label.span.end - label.span.start).max(1);

                let spaces = " ".repeat(col);
                let underline = underline_char
                    .to_string()
                    .repeat(len.min(line_str.len().saturating_sub(col)));

                output.push_str(&format!(
                    "  {:>width$} {}|{} {}{}{} {}\n",
                    "",
                    blue,
                    reset,
                    spaces,
                    underline_color,
                    underline,
                    label.message,
                    width = line_num_width
                ));
                output.push_str(reset);
            }
        }

        // Notes
        for note in &self.notes {
            let note_color = if use_color {
                Severity::Note.color()
            } else {
                ""
            };
            output.push_str(&format!("  {}= note:{} {}\n", note_color, reset, note));
        }

        // Help
        for help in &self.help {
            let help_color = if use_color {
                Severity::Help.color()
            } else {
                ""
            };
            output.push_str(&format!("  {}= help:{} {}\n", help_color, reset, help));
        }

        output
    }

    /// Format this diagnostic without color (for testing).
    pub fn format_plain(&self, source: &str) -> String {
        self.format(source, false)
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Simple display without source context
        write!(f, "{}", self.message)
    }
}

/// A registry of source files for multi-file error tracking.
///
/// Use this to store source code from multiple files so that
/// diagnostics can show context from any file.
#[derive(Debug, Default, Clone)]
pub struct SourceRegistry {
    files: std::collections::HashMap<String, String>,
}

impl SourceRegistry {
    /// Create a new empty source registry.
    pub fn new() -> Self {
        Self {
            files: std::collections::HashMap::new(),
        }
    }

    /// Add a source file to the registry.
    pub fn add(&mut self, path: impl Into<String>, source: impl Into<String>) {
        self.files.insert(path.into(), source.into());
    }

    /// Get the source code for a file path.
    pub fn get(&self, path: &str) -> Option<&str> {
        self.files.get(path).map(|s| s.as_str())
    }

    /// Check if a file is in the registry.
    pub fn contains(&self, path: &str) -> bool {
        self.files.contains_key(path)
    }

    /// Get all file paths in the registry.
    pub fn files(&self) -> impl Iterator<Item = &str> {
        self.files.keys().map(|s| s.as_str())
    }

    /// Get the number of files in the registry.
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }
}

/// A collection of diagnostics.
#[derive(Debug, Default)]
pub struct Diagnostics {
    items: Vec<Diagnostic>,
}

impl Diagnostics {
    /// Create a new empty diagnostics collection.
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    /// Add a diagnostic.
    pub fn push(&mut self, diag: Diagnostic) {
        self.items.push(diag);
    }

    /// Add an error.
    pub fn error(&mut self, message: impl Into<String>) -> &mut Diagnostic {
        self.items.push(Diagnostic::error(message));
        self.items.last_mut().unwrap()
    }

    /// Add a warning.
    pub fn warning(&mut self, message: impl Into<String>) -> &mut Diagnostic {
        self.items.push(Diagnostic::warning(message));
        self.items.last_mut().unwrap()
    }

    /// Check if there are any errors.
    pub fn has_errors(&self) -> bool {
        self.items.iter().any(|d| d.severity == Severity::Error)
    }

    /// Get the number of errors.
    pub fn error_count(&self) -> usize {
        self.items
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count()
    }

    /// Get the number of warnings.
    pub fn warning_count(&self) -> usize {
        self.items
            .iter()
            .filter(|d| d.severity == Severity::Warning)
            .count()
    }

    /// Format all diagnostics.
    pub fn format(&self, source: &str, use_color: bool) -> String {
        let mut output = String::new();
        for diag in &self.items {
            output.push_str(&diag.format(source, use_color));
            output.push('\n');
        }

        self.append_summary(&mut output, use_color);
        output
    }

    /// Append error/warning summary
    fn append_summary(&self, output: &mut String, use_color: bool) {
        let errors = self.error_count();
        let warnings = self.warning_count();
        if errors == 0 && warnings == 0 {
            return;
        }

        if use_color {
            if errors > 0 {
                output.push_str(&format!(
                    "\x1b[1;31merror\x1b[0m: aborting due to {} previous error{}\n",
                    errors,
                    if errors == 1 { "" } else { "s" }
                ));
            }
            if warnings > 0 {
                output.push_str(&format!(
                    "\x1b[1;33mwarning\x1b[0m: {} warning{} emitted\n",
                    warnings,
                    if warnings == 1 { "" } else { "s" }
                ));
            }
        } else {
            if errors > 0 {
                output.push_str(&format!(
                    "error: aborting due to {} previous error{}\n",
                    errors,
                    if errors == 1 { "" } else { "s" }
                ));
            }
            if warnings > 0 {
                output.push_str(&format!(
                    "warning: {} warning{} emitted\n",
                    warnings,
                    if warnings == 1 { "" } else { "s" }
                ));
            }
        }
    }

    /// Format all diagnostics with source from multiple files.
    ///
    /// Each diagnostic can have a `file` field that specifies which file it belongs to.
    /// The source registry provides the source code for each file.
    pub fn format_multi_file(&self, sources: &SourceRegistry, use_color: bool) -> String {
        let mut output = String::new();

        for diag in &self.items {
            // Get the source for this diagnostic's file
            let source = diag
                .file
                .as_ref()
                .and_then(|f| sources.get(f))
                .unwrap_or("");

            output.push_str(&diag.format(source, use_color));
            output.push('\n');
        }

        self.append_summary(&mut output, use_color);
        output
    }

    /// Group diagnostics by file.
    ///
    /// Returns a map from file path to diagnostics for that file.
    /// Diagnostics without a file are grouped under an empty string key.
    pub fn by_file(&self) -> std::collections::HashMap<String, Vec<&Diagnostic>> {
        let mut grouped: std::collections::HashMap<String, Vec<&Diagnostic>> =
            std::collections::HashMap::new();

        for diag in &self.items {
            let file = diag.file.as_deref().unwrap_or("").to_string();
            grouped.entry(file).or_default().push(diag);
        }

        grouped
    }

    /// Get diagnostics for a specific file.
    pub fn for_file(&self, path: &str) -> Vec<&Diagnostic> {
        self.items
            .iter()
            .filter(|d| d.file.as_deref() == Some(path))
            .collect()
    }

    /// Iterate over diagnostics.
    pub fn iter(&self) -> impl Iterator<Item = &Diagnostic> {
        self.items.iter()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Get the number of diagnostics.
    pub fn len(&self) -> usize {
        self.items.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_format() {
        let source = "fn main():\n    let x = + 42\n    return x";
        let diag = Diagnostic::error("unexpected token")
            .with_code("E0001")
            .with_label(Span::new(20, 21, 2, 13), "expected expression, found `+`")
            .with_help("expressions cannot start with an operator");

        let output = diag.format_plain(source);
        assert!(output.contains("error[E0001]: unexpected token"));
        assert!(output.contains("let x = + 42"));
        assert!(output.contains("^"));
        assert!(output.contains("expected expression"));
        assert!(output.contains("help:"));
    }

    #[test]
    fn test_warning_format() {
        let source = "fn main():\n    let unused = 42\n    return 0";
        let diag = Diagnostic::warning("unused variable")
            .with_code("W0001")
            .with_label(Span::new(19, 25, 2, 9), "variable `unused` is never used")
            .with_note("prefix with `_` to silence this warning");

        let output = diag.format_plain(source);
        assert!(output.contains("warning[W0001]: unused variable"));
        assert!(output.contains("let unused = 42"));
        assert!(output.contains("note:"));
    }

    #[test]
    fn test_diagnostics_collection() {
        let mut diags = Diagnostics::new();
        diags.push(Diagnostic::error("first error"));
        diags.push(Diagnostic::warning("a warning"));
        diags.push(Diagnostic::error("second error"));

        assert_eq!(diags.error_count(), 2);
        assert_eq!(diags.warning_count(), 1);
        assert!(diags.has_errors());
    }

    #[test]
    fn test_source_registry() {
        let mut registry = SourceRegistry::new();
        registry.add("main.spl", "fn main():\n    return 0");
        registry.add("lib.spl", "fn helper():\n    return 42");

        assert_eq!(registry.len(), 2);
        assert!(registry.contains("main.spl"));
        assert!(registry.contains("lib.spl"));
        assert!(!registry.contains("other.spl"));

        assert_eq!(registry.get("main.spl"), Some("fn main():\n    return 0"));
        assert_eq!(registry.get("lib.spl"), Some("fn helper():\n    return 42"));
        assert_eq!(registry.get("other.spl"), None);
    }

    #[test]
    fn test_multi_file_diagnostics() {
        let mut registry = SourceRegistry::new();
        registry.add("main.spl", "fn main():\n    helper()");
        registry.add("lib.spl", "fn helper():\n    return x");

        let mut diags = Diagnostics::new();
        diags.push(
            Diagnostic::error("undefined variable: x")
                .with_file("lib.spl")
                .with_label(Span::new(22, 23, 2, 12), "not found in scope"),
        );
        diags.push(
            Diagnostic::warning("unused import")
                .with_file("main.spl")
                .with_label(Span::new(15, 21, 2, 5), "never used"),
        );

        // Test by_file grouping
        let by_file = diags.by_file();
        assert_eq!(by_file.len(), 2);
        assert_eq!(by_file.get("lib.spl").map(|v| v.len()), Some(1));
        assert_eq!(by_file.get("main.spl").map(|v| v.len()), Some(1));

        // Test for_file filtering
        let lib_diags = diags.for_file("lib.spl");
        assert_eq!(lib_diags.len(), 1);
        assert!(lib_diags[0].message.contains("undefined variable"));

        // Test multi-file formatting
        let output = diags.format_multi_file(&registry, false);
        assert!(output.contains("lib.spl"));
        assert!(output.contains("main.spl"));
        assert!(output.contains("undefined variable"));
        assert!(output.contains("unused import"));
    }
}
