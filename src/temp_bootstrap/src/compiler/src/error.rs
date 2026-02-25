//! Compiler error types with rich diagnostic support.
//!
//! This module provides error types that can be converted to rich diagnostics
//! with source context, labels, and suggestions.

use crate::value::Value;
use simple_parser::{Diagnostic, Severity, Span};
use thiserror::Error;

/// Error codes for compiler errors.
///
/// Format: E1xxx for semantic, E2xxx for codegen, E3xxx for runtime
pub mod codes {
    // Semantic errors (E10xx)
    pub const UNDEFINED_VARIABLE: &str = "E1001";
    pub const UNDEFINED_FUNCTION: &str = "E1002";
    pub const TYPE_MISMATCH: &str = "E1003";
    pub const INVALID_ASSIGNMENT: &str = "E1004";
    pub const INVALID_OPERATION: &str = "E1005";
    pub const INVALID_PATTERN: &str = "E1006";
    pub const MISSING_FIELD: &str = "E1007";
    pub const DUPLICATE_DEFINITION: &str = "E1008";
    pub const CIRCULAR_DEPENDENCY: &str = "E1009";
    pub const MODULE_NOT_FOUND: &str = "E1010";

    // Control flow errors (E11xx)
    pub const BREAK_OUTSIDE_LOOP: &str = "E1101";
    pub const CONTINUE_OUTSIDE_LOOP: &str = "E1102";
    pub const RETURN_OUTSIDE_FUNCTION: &str = "E1103";
    pub const YIELD_OUTSIDE_GENERATOR: &str = "E1104";
    pub const AWAIT_OUTSIDE_ASYNC: &str = "E1105";

    // Actor/concurrency errors (E12xx)
    pub const ACTOR_SEND_FAILED: &str = "E1201";
    pub const ACTOR_RECV_FAILED: &str = "E1202";
    pub const CHANNEL_CLOSED: &str = "E1203";
    pub const DEADLOCK_DETECTED: &str = "E1204";

    // Memory errors (E13xx)
    pub const NULL_POINTER: &str = "E1301";
    pub const DANGLING_POINTER: &str = "E1302";
    pub const BORROW_VIOLATION: &str = "E1303";
    pub const USE_AFTER_FREE: &str = "E1304";

    // Codegen errors (E20xx)
    pub const UNSUPPORTED_FEATURE: &str = "E2001";
    pub const FFI_ERROR: &str = "E2002";
    pub const LINKING_ERROR: &str = "E2003";

    // Runtime errors (E30xx)
    pub const DIVISION_BY_ZERO: &str = "E3001";
    pub const INDEX_OUT_OF_BOUNDS: &str = "E3002";
    pub const STACK_OVERFLOW: &str = "E3003";
    pub const ASSERTION_FAILED: &str = "E3004";
    pub const TIMEOUT: &str = "E3005";
}

/// Typo detection and suggestion utilities.
pub mod typo {
    /// Calculate the Levenshtein distance between two strings.
    ///
    /// This measures the minimum number of single-character edits
    /// (insertions, deletions, substitutions) required to change
    /// one string into the other.
    pub fn levenshtein_distance(a: &str, b: &str) -> usize {
        let a_chars: Vec<char> = a.chars().collect();
        let b_chars: Vec<char> = b.chars().collect();
        let a_len = a_chars.len();
        let b_len = b_chars.len();

        if a_len == 0 {
            return b_len;
        }
        if b_len == 0 {
            return a_len;
        }

        // Use two rows instead of full matrix for space efficiency
        let mut prev_row: Vec<usize> = (0..=b_len).collect();
        let mut curr_row: Vec<usize> = vec![0; b_len + 1];

        for (i, a_char) in a_chars.iter().enumerate() {
            curr_row[0] = i + 1;

            for (j, b_char) in b_chars.iter().enumerate() {
                let cost = if a_char == b_char { 0 } else { 1 };
                curr_row[j + 1] = (prev_row[j + 1] + 1) // deletion
                    .min(curr_row[j] + 1) // insertion
                    .min(prev_row[j] + cost); // substitution
            }

            std::mem::swap(&mut prev_row, &mut curr_row);
        }

        prev_row[b_len]
    }

    /// Find similar names from a list of candidates.
    ///
    /// Returns names that are within the given edit distance threshold.
    /// Results are sorted by similarity (closest first).
    pub fn find_similar<'a>(
        name: &str,
        candidates: impl IntoIterator<Item = &'a str>,
        max_distance: usize,
    ) -> Vec<&'a str> {
        let mut matches: Vec<(&str, usize)> = candidates
            .into_iter()
            .filter_map(|candidate| {
                // Skip if lengths differ too much
                let len_diff = (name.len() as isize - candidate.len() as isize).unsigned_abs();
                if len_diff > max_distance {
                    return None;
                }

                let distance = levenshtein_distance(name, candidate);
                if distance <= max_distance && distance > 0 {
                    Some((candidate, distance))
                } else {
                    None
                }
            })
            .collect();

        // Sort by distance (closest first), then alphabetically
        matches.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(b.0)));

        matches.into_iter().map(|(name, _)| name).collect()
    }

    /// Find the best matching name from a list of candidates.
    ///
    /// Uses dynamic threshold based on name length:
    /// - Short names (≤3 chars): max 1 edit
    /// - Medium names (4-6 chars): max 2 edits
    /// - Long names (>6 chars): max 3 edits
    pub fn suggest_name<'a>(
        name: &str,
        candidates: impl IntoIterator<Item = &'a str>,
    ) -> Option<&'a str> {
        let max_distance = match name.len() {
            0..=3 => 1,
            4..=6 => 2,
            _ => 3,
        };

        find_similar(name, candidates, max_distance)
            .into_iter()
            .next()
    }

    /// Format a suggestion message for a typo.
    ///
    /// Returns `Some("did you mean 'foo'?")` if a suggestion is found,
    /// or `None` if no good match exists.
    pub fn format_suggestion<'a>(
        name: &str,
        candidates: impl IntoIterator<Item = &'a str>,
    ) -> Option<String> {
        suggest_name(name, candidates).map(|suggestion| format!("did you mean '{}'?", suggestion))
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_levenshtein_distance() {
            assert_eq!(levenshtein_distance("", ""), 0);
            assert_eq!(levenshtein_distance("abc", "abc"), 0);
            assert_eq!(levenshtein_distance("abc", ""), 3);
            assert_eq!(levenshtein_distance("", "abc"), 3);
            assert_eq!(levenshtein_distance("abc", "abd"), 1);
            assert_eq!(levenshtein_distance("abc", "abcd"), 1);
            assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
        }

        #[test]
        fn test_find_similar() {
            let candidates = ["count", "counter", "amount", "account", "mouse"];

            let similar = find_similar("coutn", candidates.iter().copied(), 2);
            assert!(similar.contains(&"count"));

            let similar = find_similar("xyz", candidates.iter().copied(), 2);
            assert!(similar.is_empty());
        }

        #[test]
        fn test_suggest_name() {
            let candidates = ["println", "print", "printf", "sprint"];

            assert_eq!(
                suggest_name("pritn", candidates.iter().copied()),
                Some("print")
            );
            // "printl" has distance 1 to both "print" and "println", alphabetically "print" comes first
            assert_eq!(
                suggest_name("printl", candidates.iter().copied()),
                Some("print")
            );
            assert_eq!(
                suggest_name("printlnn", candidates.iter().copied()),
                Some("println")
            );
            assert_eq!(suggest_name("xyz", candidates.iter().copied()), None);
        }

        #[test]
        fn test_format_suggestion() {
            let candidates = ["foo", "bar", "baz"];

            assert_eq!(
                format_suggestion("fo", candidates.iter().copied()),
                Some("did you mean 'foo'?".to_string())
            );
            assert_eq!(format_suggestion("xyz", candidates.iter().copied()), None);
        }
    }
}

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

    // Rich variants with context (new API)
    #[error("io: {message}")]
    IoWithContext {
        message: String,
        context: ErrorContext,
    },
    #[error("parse: {message}")]
    ParseWithContext {
        message: String,
        context: ErrorContext,
    },
    #[error("semantic: {message}")]
    SemanticWithContext {
        message: String,
        context: ErrorContext,
    },
    #[error("codegen: {message}")]
    CodegenWithContext {
        message: String,
        context: ErrorContext,
    },
    #[error("lint: {message}")]
    LintWithContext {
        message: String,
        context: ErrorContext,
    },
    #[error("runtime: {message}")]
    RuntimeWithContext {
        message: String,
        context: ErrorContext,
    },
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
                diag = diag.with_label(*span, self.message());
            }

            // Add secondary labels
            for (span, label) in &ctx.secondary_spans {
                diag = diag.with_secondary_label(*span, label.clone());
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

// Helper macro for creating errors with context at call site
#[macro_export]
macro_rules! semantic_error {
    ($msg:expr) => {
        $crate::error::CompileError::semantic($msg)
    };
    ($msg:expr, span = $span:expr) => {
        $crate::error::CompileError::semantic_with_context(
            $msg,
            $crate::error::ErrorContext::new().with_span($span),
        )
    };
    ($msg:expr, span = $span:expr, code = $code:expr) => {
        $crate::error::CompileError::semantic_with_context(
            $msg,
            $crate::error::ErrorContext::new()
                .with_span($span)
                .with_code($code),
        )
    };
}

#[macro_export]
macro_rules! runtime_error {
    ($msg:expr) => {
        $crate::error::CompileError::runtime($msg)
    };
    ($msg:expr, span = $span:expr) => {
        $crate::error::CompileError::runtime_with_context(
            $msg,
            $crate::error::ErrorContext::new().with_span($span),
        )
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

        assert!(diag
            .code
            .as_ref()
            .is_some_and(|c| c == codes::UNDEFINED_VARIABLE));
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
