//! Re-export diagnostics from simple_common with parser-specific Span compatibility.
//!
//! This module re-exports the diagnostic infrastructure from simple_common and provides
//! compatibility between parser::token::Span and common::diagnostic::Span.

pub use simple_common::diagnostic::{Diagnostic, Label, Severity};

use crate::token::Span as ParserSpan;
use simple_common::diagnostic::Span as CommonSpan;

/// Convert parser Span to common Span
impl From<ParserSpan> for CommonSpan {
    fn from(span: ParserSpan) -> Self {
        CommonSpan::new(span.start, span.end, span.line, span.column)
    }
}

/// Extension trait for Diagnostic to work with parser Spans
pub trait DiagnosticParserExt {
    /// Add a label with a parser span
    fn with_parser_label(self, span: ParserSpan, message: impl Into<String>) -> Self;

    /// Add a secondary label with a parser span
    fn with_parser_secondary_label(self, span: ParserSpan, message: impl Into<String>) -> Self;
}

impl DiagnosticParserExt for Diagnostic {
    fn with_parser_label(self, span: ParserSpan, message: impl Into<String>) -> Self {
        self.with_label(span.into(), message)
    }

    fn with_parser_secondary_label(self, span: ParserSpan, message: impl Into<String>) -> Self {
        self.with_secondary_label(span.into(), message)
    }
}
