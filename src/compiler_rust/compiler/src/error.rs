//! Compiler error types with rich diagnostic support.
//!
//! This module provides error types that can be converted to rich diagnostics
//! with source context, labels, and suggestions.

use crate::value::Value;
use simple_parser::{Diagnostic, Severity, Span};
use thiserror::Error;

// ---- submodule files -------------------------------------------------------
// Each file defines exactly one pub mod that re-exports via `use crate::error::X`.
// External code using `use crate::error::codes::X` continues to work unchanged.

#[path = "error_codes.rs"]
mod _codes_file;
pub use _codes_file::codes;

#[path = "error_typo.rs"]
mod _typo_file;
pub use _typo_file::typo;

#[path = "error_factory/mod.rs"]
mod error_factory;
pub use error_factory::factory;

// ---------------------------------------------------------------------------

/// Error context for rich diagnostics.
#[derive(Debug, Clone)]
pub struct ErrorContext {
    /// Primary span where the error occurred
    pub span: Option<Span>,
    /// Secondary spans with labels (for related locations)
    pub secondary_spans: Vec<(Span, String)>,
    /// The source file path
    pub file: Option<String>,
    /// The source code (for formatting)
    pub source: Option<String>,
    /// Error code
    pub code: Option<String>,
    /// Additional notes
    pub notes: Vec<String>,
    /// Help suggestions
    pub help: Vec<String>,
}

impl Default for ErrorContext {
    fn default() -> Self {
        Self::new()
    }
}

impl ErrorContext {
    /// Create a new empty error context.
    pub fn new() -> Self {
        Self {
            span: None,
            secondary_spans: Vec::new(),
            file: None,
            source: None,
            code: None,
            notes: Vec::new(),
            help: Vec::new(),
        }
    }

    /// Set the primary span.
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Add a secondary span with a label.
    pub fn with_secondary(mut self, span: Span, label: impl Into<String>) -> Self {
        self.secondary_spans.push((span, label.into()));
        self
    }

    /// Set the file path.
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    /// Set the source code.
    pub fn with_source(mut self, source: impl Into<String>) -> Self {
        self.source = Some(source.into());
        self
    }

    /// Set the error code.
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
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
}

/// Compilation errors with optional rich context.
#[derive(Error, Debug)]
pub enum CompileError {
    #[error("io: {0}")]
    Io(String),
    #[error("parse: {0}")]
    Parse(String),
    #[error("semantic: {0}")]
    Semantic(String),
    #[error("codegen: {0}")]
    Codegen(String),
    /// Lint errors (when lint is set to deny level)
    #[error("lint: {0}")]
    Lint(String),
    /// Runtime error during interpretation
    #[error("runtime: {0}")]
    Runtime(String),
    /// Error from ? operator that should be propagated as a return value
    #[error("try: early return")]
    TryError(Value),
    /// Execution was interrupted by user (Ctrl-C)
    #[error("interrupted: execution stopped by user request")]
    InterruptedByUser,
    /// Ghost code verification error (VER-001)
    #[error("ghost: {0}")]
    GhostError(String),

    /// Execution limit exceeded (infinite loop protection)
    #[error("execution limit exceeded: {message}")]
    ExecutionLimitExceeded { limit: u64, message: String },

    /// Stack overflow (recursion depth exceeded)
    #[error("stack overflow: recursion depth {depth} exceeded limit {limit} in function '{function_name}'")]
    StackOverflow {
        depth: u64,
        limit: u64,
        function_name: String,
    },

    /// Execution timeout exceeded (wall-clock)
    #[error("timeout: execution exceeded {timeout_secs} second limit")]
    TimeoutExceeded { timeout_secs: u64 },

    // Rich variants with context (new API)
    #[error("io: {message}")]
    IoWithContext { message: String, context: ErrorContext },
    #[error("parse: {message}")]
    ParseWithContext { message: String, context: ErrorContext },
    #[error("semantic: {message}")]
    SemanticWithContext { message: String, context: ErrorContext },
    #[error("codegen: {message}")]
    CodegenWithContext { message: String, context: ErrorContext },
    #[error("lint: {message}")]
    LintWithContext { message: String, context: ErrorContext },
    #[error("runtime: {message}")]
    RuntimeWithContext { message: String, context: ErrorContext },
}

impl CompileError {
    /// Create an I/O error with just a message.
    pub fn io(message: impl Into<String>) -> Self {
        Self::Io(message.into())
    }

    /// Create a parse error with just a message.
    pub fn parse(message: impl Into<String>) -> Self {
        Self::Parse(message.into())
    }

    /// Create a semantic error with just a message.
    pub fn semantic(message: impl Into<String>) -> Self {
        Self::Semantic(message.into())
    }

    /// Create a codegen error with just a message.
    pub fn codegen(message: impl Into<String>) -> Self {
        Self::Codegen(message.into())
    }

    /// Create a lint error with just a message.
    pub fn lint(message: impl Into<String>) -> Self {
        Self::Lint(message.into())
    }

    /// Create a runtime error with just a message.
    pub fn runtime(message: impl Into<String>) -> Self {
        Self::Runtime(message.into())
    }

    /// Create a contract violation error with a message.
    /// Used when preconditions, postconditions, or invariants fail at runtime.
    pub fn contract_violation(message: impl Into<String>) -> Self {
        let ctx = ErrorContext::new()
            .with_code(codes::CONTRACT_PRECONDITION_FAILED)
            .with_help("ensure the contract condition is satisfied before function call");
        Self::RuntimeWithContext {
            message: message.into(),
            context: ctx,
        }
    }

    /// Create a semantic error with context.
    pub fn semantic_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::SemanticWithContext {
            message: message.into(),
            context,
        }
    }

    /// Create a runtime error with context.
    pub fn runtime_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::RuntimeWithContext {
            message: message.into(),
            context,
        }
    }

    /// Create a parse error with context.
    pub fn parse_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::ParseWithContext {
            message: message.into(),
            context,
        }
    }

    /// Create an I/O error with context.
    pub fn io_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::IoWithContext {
            message: message.into(),
            context,
        }
    }

    /// Create a codegen error with context.
    pub fn codegen_with_context(message: impl Into<String>, context: ErrorContext) -> Self {
        Self::CodegenWithContext {
            message: message.into(),
            context,
        }
    }

    /// Get the error context if available.
    pub fn context(&self) -> Option<&ErrorContext> {
        match self {
            Self::IoWithContext { context, .. } => Some(context),
            Self::ParseWithContext { context, .. } => Some(context),
            Self::SemanticWithContext { context, .. } => Some(context),
            Self::CodegenWithContext { context, .. } => Some(context),
            Self::LintWithContext { context, .. } => Some(context),
            Self::RuntimeWithContext { context, .. } => Some(context),
            _ => None,
        }
    }

    /// Get the error message.
    pub fn message(&self) -> &str {
        match self {
            Self::Io(msg) => msg,
            Self::Parse(msg) => msg,
            Self::Semantic(msg) => msg,
            Self::Codegen(msg) => msg,
            Self::Lint(msg) => msg,
            Self::Runtime(msg) => msg,
            Self::IoWithContext { message, .. } => message,
            Self::ParseWithContext { message, .. } => message,
            Self::SemanticWithContext { message, .. } => message,
            Self::CodegenWithContext { message, .. } => message,
            Self::LintWithContext { message, .. } => message,
            Self::RuntimeWithContext { message, .. } => message,
            Self::TryError(_) => "try: early return",
            Self::InterruptedByUser => "interrupted: execution stopped by user request",
            Self::GhostError(msg) => msg,
            Self::ExecutionLimitExceeded { message, .. } => message,
            Self::StackOverflow { function_name, .. } => function_name,
            Self::TimeoutExceeded { .. } => "timeout exceeded",
        }
    }

    /// Get the severity for this error type.
    fn severity(&self) -> Severity {
        match self {
            Self::Lint(_) | Self::LintWithContext { .. } => Severity::Warning,
            _ => Severity::Error,
        }
    }

    /// Convert this error to a rich diagnostic.
    pub fn to_diagnostic(&self) -> Diagnostic {
        let mut diag = if self.severity() == Severity::Warning {
            Diagnostic::warning(self.message())
        } else {
            Diagnostic::error(self.message())
        };

        if let Some(ctx) = self.context() {
            // Set error code
            if let Some(code) = &ctx.code {
                diag = diag.with_code(code.clone());
            }

            // Set file
            if let Some(file) = &ctx.file {
                diag = diag.with_file(file.clone());
            }

            // Add primary label
            if let Some(span) = &ctx.span {
                diag = diag.with_label((*span).into(), self.message());
            }

            // Add secondary labels
            for (span, label) in &ctx.secondary_spans {
                diag = diag.with_secondary_label((*span).into(), label.clone());
            }

            // Add notes
            for note in &ctx.notes {
                diag = diag.with_note(note.clone());
            }

            // Add help
            for help in &ctx.help {
                diag = diag.with_help(help.clone());
            }
        }

        diag
    }

    /// Format this error with source context.
    pub fn format_with_source(&self, source: &str, use_color: bool) -> String {
        self.to_diagnostic().format(source, use_color)
    }
}

// Backward compatibility: allow creating errors from strings
impl From<String> for CompileError {
    fn from(s: String) -> Self {
        Self::semantic(s)
    }
}

impl From<&str> for CompileError {
    fn from(s: &str) -> Self {
        Self::semantic(s)
    }
}

// SPIR-V error conversion (for Vulkan backend)
#[cfg(feature = "vulkan")]
impl From<rspirv::dr::Error> for CompileError {
    fn from(e: rspirv::dr::Error) -> Self {
        Self::Codegen(format!("SPIR-V error: {}", e))
    }
}

// Helper macro for creating errors with context at call site
#[macro_export]
macro_rules! semantic_error {
    ($msg:expr) => {
        $crate::error::CompileError::semantic($msg)
    };
    ($msg:expr, span = $span:expr) => {
        $crate::error::CompileError::semantic_with_context($msg, $crate::error::ErrorContext::new().with_span($span))
    };
    ($msg:expr, span = $span:expr, code = $code:expr) => {
        $crate::error::CompileError::semantic_with_context(
            $msg,
            $crate::error::ErrorContext::new().with_span($span).with_code($code),
        )
    };
}

#[macro_export]
macro_rules! runtime_error {
    ($msg:expr) => {
        $crate::error::CompileError::runtime($msg)
    };
    ($msg:expr, span = $span:expr) => {
        $crate::error::CompileError::runtime_with_context($msg, $crate::error::ErrorContext::new().with_span($span))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = CompileError::semantic("undefined variable: x");
        assert!(err.message().contains("undefined variable"));
    }

    #[test]
    fn test_error_with_context() {
        let ctx = ErrorContext::new()
            .with_span(Span::new(10, 15, 2, 5))
            .with_code(codes::UNDEFINED_VARIABLE)
            .with_help("did you mean 'y'?");

        let err = CompileError::semantic_with_context("undefined variable: x", ctx);
        let diag = err.to_diagnostic();

        assert!(diag.code.as_ref().is_some_and(|c| c == codes::UNDEFINED_VARIABLE));
        assert!(!diag.help.is_empty());
    }

    #[test]
    fn test_diagnostic_format() {
        let ctx = ErrorContext::new()
            .with_span(Span::new(10, 11, 2, 5))
            .with_code(codes::UNDEFINED_VARIABLE)
            .with_file("test.spl");

        let err = CompileError::semantic_with_context("undefined variable: x", ctx);
        let source = "fn main():\n    x + 1";
        let formatted = err.format_with_source(source, false);

        assert!(formatted.contains("error"));
        assert!(formatted.contains("E1001"));
        assert!(formatted.contains("test.spl"));
    }

    #[test]
    fn test_backward_compatibility() {
        // Old-style tuple variant creation should still work
        let err = CompileError::Semantic("test error".into());
        assert_eq!(err.message(), "test error");

        // Also test the From trait
        let err2: CompileError = "another error".into();
        assert_eq!(err2.message(), "another error");
    }
}
