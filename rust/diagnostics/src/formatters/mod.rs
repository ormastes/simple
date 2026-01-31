//! Diagnostic formatters
//!
//! This module provides different formatters for diagnostic output:
//! - `text`: Colored terminal output (like rustc)
//! - `json`: JSON format for tools and LLM integration
//! - `simple`: Simple language syntax for specs

pub mod json;
pub mod simple;
pub mod text;

pub use json::JsonFormatter;
pub use simple::SimpleFormatter;
pub use text::TextFormatter;

/// Common trait for diagnostic formatters
pub trait DiagnosticFormatter {
    /// Format a single diagnostic
    fn format_diagnostic(&self, diagnostic: &crate::Diagnostic, source: &str) -> String;

    /// Format multiple diagnostics
    fn format_diagnostics(&self, diagnostics: &[crate::Diagnostic], source: &str) -> String {
        diagnostics
            .iter()
            .map(|d| self.format_diagnostic(d, source))
            .collect::<Vec<_>>()
            .join("\n\n")
    }
}
