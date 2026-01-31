//! Lint diagnostic messages and formatting.

use super::types::{LintLevel, LintName};
use simple_common::diagnostic::EasyFix;
use simple_parser::token::Span;

/// A lint diagnostic message
#[derive(Debug, Clone)]
pub struct LintDiagnostic {
    pub lint: LintName,
    pub level: LintLevel,
    pub span: Span,
    pub message: String,
    pub suggestion: Option<String>,
    pub easy_fix: Option<EasyFix>,
}

impl LintDiagnostic {
    pub fn new(lint: LintName, level: LintLevel, span: Span, message: String) -> Self {
        Self {
            lint,
            level,
            span,
            message,
            suggestion: None,
            easy_fix: None,
        }
    }

    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.suggestion = Some(suggestion);
        self
    }

    pub fn with_easy_fix(mut self, easy_fix: EasyFix) -> Self {
        self.easy_fix = Some(easy_fix);
        self
    }

    /// Check if this is an error (deny level)
    pub fn is_error(&self) -> bool {
        self.level == LintLevel::Deny
    }

    /// Check if this is a warning
    pub fn is_warning(&self) -> bool {
        self.level == LintLevel::Warn
    }

    /// Format the diagnostic for display
    pub fn format(&self) -> String {
        let prefix = match self.level {
            LintLevel::Allow => return String::new(), // Don't display allowed lints
            LintLevel::Warn => "warning",
            LintLevel::Deny => "error",
        };

        let mut result = format!(
            "{}: {} [{}]\n  --> line {}, column {}\n",
            prefix,
            self.message,
            self.lint.as_str(),
            self.span.line,
            self.span.column
        );

        if let Some(ref suggestion) = self.suggestion {
            result.push_str(&format!("  = help: {}\n", suggestion));
        }

        result
    }

    /// Convert to common Diagnostic format for JSON export (#903)
    pub fn to_diagnostic(&self, file: Option<String>) -> simple_common::diagnostic::Diagnostic {
        use simple_common::diagnostic::{Diagnostic, Severity, Span as CommonSpan};

        let severity = match self.level {
            LintLevel::Allow => Severity::Note,
            LintLevel::Warn => Severity::Warning,
            LintLevel::Deny => Severity::Error,
        };

        let common_span = CommonSpan::new(self.span.start, self.span.end, self.span.line, self.span.column);

        let mut diag = Diagnostic::new(severity, self.message.clone())
            .with_code(format!("L:{}", self.lint.as_str()))
            .with_label(common_span, self.message.clone());

        if let Some(ref file_path) = file {
            diag = diag.with_file(file_path);
        }

        if let Some(ref suggestion) = self.suggestion {
            diag = diag.with_help(suggestion);
        }

        if let Some(ref easy_fix) = self.easy_fix {
            diag = diag.with_easy_fix(easy_fix.clone());
        }

        diag
    }
}
