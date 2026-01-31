//! Text formatter for terminal output
//!
//! Provides rich, colored diagnostic output similar to rustc.

use crate::{Diagnostic, Severity, Span};

const RESET: &str = "\x1b[0m";
const BOLD: &str = "\x1b[1m";

/// Text formatter for terminal output with color support
pub struct TextFormatter {
    use_color: bool,
}

impl TextFormatter {
    /// Create a new text formatter
    pub fn new() -> Self {
        Self { use_color: true }
    }

    /// Create a formatter without colors (for piping/redirected output)
    pub fn without_color() -> Self {
        Self { use_color: false }
    }

    /// Format a diagnostic with source code context
    pub fn format(&self, diagnostic: &Diagnostic, source: &str) -> String {
        let mut output = String::new();

        // Header: severity[code]: message
        self.format_header(diagnostic, &mut output);

        // Source code snippet with labels
        if let Some(span) = diagnostic.span {
            output.push('\n');
            self.format_source_snippet(span, source, diagnostic, &mut output);
        }

        // Labels for additional spans
        for label in &diagnostic.labels {
            if Some(label.span) != diagnostic.span {
                output.push('\n');
                self.format_label_snippet(label.span, source, &label.message, diagnostic.severity, &mut output);
            }
        }

        // Notes
        for note in &diagnostic.notes {
            output.push('\n');
            self.format_note(note, &mut output);
        }

        // Help
        if let Some(help) = &diagnostic.help {
            output.push('\n');
            self.format_help(help, &mut output);
        }

        output
    }

    fn format_header(&self, diagnostic: &Diagnostic, output: &mut String) {
        let severity_str = diagnostic.severity.display_name();
        let color = if self.use_color {
            diagnostic.severity.color()
        } else {
            ""
        };
        let reset = if self.use_color { RESET } else { "" };
        let bold = if self.use_color { BOLD } else { "" };

        if let Some(code) = &diagnostic.code {
            output.push_str(&format!(
                "{}{bold}{}[{}]{reset}: {}",
                color, severity_str, code, diagnostic.message
            ));
        } else {
            output.push_str(&format!(
                "{}{bold}{}{reset}: {}",
                color, severity_str, diagnostic.message
            ));
        }
    }

    fn format_source_snippet(&self, span: Span, source: &str, diagnostic: &Diagnostic, output: &mut String) {
        let lines: Vec<&str> = source.lines().collect();

        // Get the line (1-indexed)
        if span.line == 0 || span.line > lines.len() {
            return;
        }

        let line_idx = span.line - 1;
        let line_text = lines[line_idx];

        // Line number width for alignment
        let line_num_width = span.line.to_string().len().max(2);

        let blue = if self.use_color { "\x1b[34m" } else { "" };
        let reset = if self.use_color { RESET } else { "" };
        let bold = if self.use_color { BOLD } else { "" };

        // Location line: "  --> file.rs:line:column"
        output.push_str(&format!(
            "{:>width$} {blue}{bold}-->{reset} <source>:{}:{}\n",
            "",
            span.line,
            span.column,
            width = line_num_width
        ));

        // Empty line
        output.push_str(&format!("{:>width$} {blue}|{reset}\n", "", width = line_num_width));

        // Source line with line number
        output.push_str(&format!(
            "{blue}{:>width$} |{reset} {}\n",
            span.line,
            line_text,
            width = line_num_width
        ));

        // Underline/caret line
        let color = if self.use_color {
            diagnostic.severity.color()
        } else {
            ""
        };

        // Calculate underline position and length
        let start_col = span.column.saturating_sub(1);
        let underline_len = span.len().max(1);

        let spaces = " ".repeat(start_col);
        let carets = "^".repeat(underline_len);

        output.push_str(&format!(
            "{:>width$} {blue}|{reset} {}{color}{bold}{}{reset}",
            "",
            spaces,
            carets,
            width = line_num_width
        ));

        // Primary label (if any match the main span)
        if let Some(label) = diagnostic.labels.iter().find(|l| l.span == span) {
            output.push_str(&format!(" {}{bold}{}{reset}", color, label.message));
        }

        output.push('\n');
    }

    fn format_label_snippet(&self, span: Span, source: &str, label_msg: &str, severity: Severity, output: &mut String) {
        let lines: Vec<&str> = source.lines().collect();

        if span.line == 0 || span.line > lines.len() {
            return;
        }

        let line_idx = span.line - 1;
        let line_text = lines[line_idx];

        let line_num_width = span.line.to_string().len().max(2);

        let blue = if self.use_color { "\x1b[34m" } else { "" };
        let reset = if self.use_color { RESET } else { "" };
        let bold = if self.use_color { BOLD } else { "" };
        let color = if self.use_color { severity.color() } else { "" };

        output.push_str(&format!("{:>width$} {blue}|{reset}\n", "", width = line_num_width));
        output.push_str(&format!(
            "{blue}{:>width$} |{reset} {}\n",
            span.line,
            line_text,
            width = line_num_width
        ));

        let start_col = span.column.saturating_sub(1);
        let underline_len = span.len().max(1);
        let spaces = " ".repeat(start_col);
        let carets = "^".repeat(underline_len);

        output.push_str(&format!(
            "{:>width$} {blue}|{reset} {}{color}{bold}{}{reset} {color}{bold}{}{reset}\n",
            "",
            spaces,
            carets,
            label_msg,
            width = line_num_width
        ));
    }

    fn format_note(&self, note: &str, output: &mut String) {
        let cyan = if self.use_color { "\x1b[36m" } else { "" };
        let reset = if self.use_color { RESET } else { "" };
        let bold = if self.use_color { BOLD } else { "" };

        output.push_str(&format!("{cyan}{bold}note{reset}: {}", note));
    }

    fn format_help(&self, help: &str, output: &mut String) {
        let green = if self.use_color { "\x1b[32m" } else { "" };
        let reset = if self.use_color { RESET } else { "" };
        let bold = if self.use_color { BOLD } else { "" };

        output.push_str(&format!("{green}{bold}help{reset}: {}", help));
    }
}

impl Default for TextFormatter {
    fn default() -> Self {
        Self::new()
    }
}

impl super::DiagnosticFormatter for TextFormatter {
    fn format_diagnostic(&self, diagnostic: &Diagnostic, source: &str) -> String {
        self.format(diagnostic, source)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Diagnostic, Span};

    #[test]
    fn test_format_basic_error() {
        let source = "fn main() {\n    let x = 42\n}\n";
        let span = Span::new(20, 22, 2, 13);

        let diag = Diagnostic::error("expected semicolon")
            .with_code("E0001")
            .with_span(span);

        let formatter = TextFormatter::without_color();
        let output = formatter.format(&diag, source);

        assert!(output.contains("error[E0001]"));
        assert!(output.contains("expected semicolon"));
        assert!(output.contains("let x = 42"));
    }

    #[test]
    fn test_format_with_label() {
        let source = "fn main() {\n    let x = 42\n}\n";
        let span = Span::new(20, 22, 2, 13);

        let diag = Diagnostic::error("expected semicolon")
            .with_code("E0001")
            .with_span(span)
            .with_label(span, "add `;` here");

        let formatter = TextFormatter::without_color();
        let output = formatter.format(&diag, source);

        assert!(output.contains("add `;` here"));
    }

    #[test]
    fn test_format_with_help_and_note() {
        let source = "fn main() {}\n";
        let span = Span::new(0, 2, 1, 1);

        let diag = Diagnostic::warning("unused function")
            .with_code("W0001")
            .with_span(span)
            .with_note("function `main` is never called")
            .with_help("consider removing this function");

        let formatter = TextFormatter::without_color();
        let output = formatter.format(&diag, source);

        assert!(output.contains("warning[W0001]"));
        assert!(output.contains("note:"));
        assert!(output.contains("help:"));
    }
}
