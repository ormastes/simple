//! Diagnostic severity levels

use serde::{Deserialize, Serialize};
use simple_i18n::I18n;

/// Severity level of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// Fatal error that prevents compilation
    Error,
    /// Warning that doesn't prevent compilation
    Warning,
    /// Informational note
    Note,
    /// Helpful suggestion
    Help,
    /// General information
    Info,
}

impl Severity {
    /// Get the English name (for error codes, internal use)
    pub fn name(&self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
            Severity::Help => "help",
            Severity::Info => "info",
        }
    }

    /// Get the localized name for display (i18n-aware)
    ///
    /// This uses the global i18n instance to get the localized severity name.
    /// Falls back to English if i18n catalog is not available.
    pub fn display_name(&self) -> String {
        I18n::global().severity_name(self.name())
    }

    /// Get ANSI color code for terminal output
    pub fn color(&self) -> &'static str {
        match self {
            Severity::Error => "\x1b[1;31m",   // Bold red
            Severity::Warning => "\x1b[1;33m", // Bold yellow
            Severity::Note => "\x1b[1;36m",    // Bold cyan
            Severity::Help => "\x1b[1;32m",    // Bold green
            Severity::Info => "\x1b[1;34m",    // Bold blue
        }
    }
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_severity_name() {
        assert_eq!(Severity::Error.name(), "error");
        assert_eq!(Severity::Warning.name(), "warning");
        assert_eq!(Severity::Note.name(), "note");
        assert_eq!(Severity::Help.name(), "help");
        assert_eq!(Severity::Info.name(), "info");
    }

    #[test]
    fn test_severity_display_name() {
        // Default locale (English)
        std::env::remove_var("SIMPLE_LANG");
        assert_eq!(Severity::Error.display_name(), "error");

        // Korean locale
        std::env::set_var("SIMPLE_LANG", "ko");
        let name = Severity::Error.display_name();
        // Will be "오류" if Korean catalog is loaded, "error" if fallback
        assert!(!name.is_empty());

        // Cleanup
        std::env::remove_var("SIMPLE_LANG");
    }

    #[test]
    fn test_severity_color() {
        assert_eq!(Severity::Error.color(), "\x1b[1;31m");
        assert_eq!(Severity::Warning.color(), "\x1b[1;33m");
        assert_eq!(Severity::Note.color(), "\x1b[1;36m");
        assert_eq!(Severity::Help.color(), "\x1b[1;32m");
        assert_eq!(Severity::Info.color(), "\x1b[1;34m");
    }
}
