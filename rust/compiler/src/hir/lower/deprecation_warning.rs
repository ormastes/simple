//! Deprecation warning infrastructure
//!
//! This module provides types for collecting and reporting deprecation warnings
//! when deprecated functions, types, or methods are used.

use simple_parser::Span;

/// A deprecation warning for a deprecated item usage
#[derive(Debug, Clone)]
pub struct DeprecationWarning {
    /// Location where the deprecated item is used
    pub span: Span,
    /// Name of the deprecated item
    pub deprecated_name: String,
    /// Optional deprecation message from @deprecated("...")
    pub message: Option<String>,
    /// Suggested non-deprecated alternative
    pub suggestion: Option<String>,
    /// Kind of item: "function", "type", or "method"
    pub kind: &'static str,
}

impl DeprecationWarning {
    /// Create a new deprecation warning for a function
    pub fn function(span: Span, name: String, message: Option<String>, suggestion: Option<String>) -> Self {
        Self {
            span,
            deprecated_name: name,
            message,
            suggestion,
            kind: "function",
        }
    }

    /// Create a new deprecation warning for a type
    pub fn type_usage(span: Span, name: String, message: Option<String>, suggestion: Option<String>) -> Self {
        Self {
            span,
            deprecated_name: name,
            message,
            suggestion,
            kind: "type",
        }
    }

    /// Create a new deprecation warning for a method
    pub fn method(span: Span, name: String, message: Option<String>, suggestion: Option<String>) -> Self {
        Self {
            span,
            deprecated_name: name,
            message,
            suggestion,
            kind: "method",
        }
    }

    /// Format the warning as a human-readable string
    pub fn format(&self) -> String {
        let mut output = format!("warning: use of deprecated {} '{}'\n", self.kind, self.deprecated_name);

        output.push_str(&format!("  --> line {}:{}\n", self.span.line, self.span.column));

        if let Some(ref msg) = self.message {
            output.push_str(&format!("   = note: \"{}\"\n", msg));
        }

        if let Some(ref suggestion) = self.suggestion {
            output.push_str(&format!(
                "   = help: consider using '{}' which is a non-deprecated alternative\n",
                suggestion
            ));
        }

        output
    }
}

/// Collector for deprecation warnings
#[derive(Debug, Clone, Default)]
pub struct DeprecationWarningCollector {
    warnings: Vec<DeprecationWarning>,
}

impl DeprecationWarningCollector {
    /// Create a new empty collector
    pub fn new() -> Self {
        Self { warnings: Vec::new() }
    }

    /// Add a deprecation warning
    pub fn add(&mut self, warning: DeprecationWarning) {
        self.warnings.push(warning);
    }

    /// Add a function deprecation warning
    pub fn add_function(&mut self, span: Span, name: String, message: Option<String>, suggestion: Option<String>) {
        self.add(DeprecationWarning::function(span, name, message, suggestion));
    }

    /// Add a type deprecation warning
    pub fn add_type(&mut self, span: Span, name: String, message: Option<String>, suggestion: Option<String>) {
        self.add(DeprecationWarning::type_usage(span, name, message, suggestion));
    }

    /// Add a method deprecation warning
    pub fn add_method(&mut self, span: Span, name: String, message: Option<String>, suggestion: Option<String>) {
        self.add(DeprecationWarning::method(span, name, message, suggestion));
    }

    /// Check if there are any warnings
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    /// Get the number of warnings
    pub fn count(&self) -> usize {
        self.warnings.len()
    }

    /// Get all warnings
    pub fn warnings(&self) -> &[DeprecationWarning] {
        &self.warnings
    }

    /// Take ownership of the warnings
    pub fn take_warnings(&mut self) -> Vec<DeprecationWarning> {
        std::mem::take(&mut self.warnings)
    }

    /// Format all warnings as a human-readable string
    pub fn format_all(&self) -> String {
        self.warnings.iter().map(|w| w.format()).collect::<Vec<_>>().join("\n")
    }
}
