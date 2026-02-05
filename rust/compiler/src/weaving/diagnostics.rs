//! Diagnostic reporting for AOP weaving.

/// Diagnostic severity levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticLevel {
    /// Informational message
    Info,
    /// Warning that doesn't prevent weaving
    Warning,
    /// Error that prevents correct weaving
    Error,
}

/// Weaving diagnostic message.
#[derive(Debug, Clone)]
pub struct WeavingDiagnostic {
    /// Severity level
    pub level: DiagnosticLevel,
    /// Diagnostic message
    pub message: String,
    /// Optional location (function name, block, instruction)
    pub location: Option<String>,
    /// Related predicate text
    pub predicate: Option<String>,
}

impl WeavingDiagnostic {
    /// Create an info diagnostic.
    pub fn info(message: String) -> Self {
        Self {
            level: DiagnosticLevel::Info,
            message,
            location: None,
            predicate: None,
        }
    }

    /// Create a warning diagnostic.
    pub fn warning(message: String) -> Self {
        Self {
            level: DiagnosticLevel::Warning,
            message,
            location: None,
            predicate: None,
        }
    }

    /// Create an error diagnostic.
    pub fn error(message: String) -> Self {
        Self {
            level: DiagnosticLevel::Error,
            message,
            location: None,
            predicate: None,
        }
    }

    /// Add location information.
    pub fn with_location(mut self, location: String) -> Self {
        self.location = Some(location);
        self
    }

    /// Add predicate information.
    pub fn with_predicate(mut self, predicate: String) -> Self {
        self.predicate = Some(predicate);
        self
    }
}
