//! Unified diagnostic system for Simple compiler
//!
//! This crate provides a unified diagnostic system with built-in i18n support.
//! It's used by all parts of the Simple compiler: parser, compiler, interpreter.
//!
//! # Examples
//!
//! ## Creating a simple diagnostic
//!
//! ```
//! use simple_diagnostics::{Diagnostic, Severity, Span};
//!
//! let span = Span::new(0, 5, 1, 1);
//! let diag = Diagnostic::error("unexpected token")
//!     .with_code("E0001")
//!     .with_span(span)
//!     .with_label(span, "expected identifier");
//! ```
//!
//! ## Creating an i18n diagnostic
//!
//! ```
//! use simple_diagnostics::{Diagnostic, i18n::ctx2};
//!
//! let ctx = ctx2("expected", "identifier", "found", "number");
//! let diag = Diagnostic::error_i18n("parser", "E0002", &ctx);
//! ```
//!
//! ## Using the context builder
//!
//! ```
//! use simple_diagnostics::{Diagnostic, i18n::ContextBuilder};
//!
//! let ctx = ContextBuilder::new()
//!     .with("expected", "i32")
//!     .with("found", "bool")
//!     .with("line", 42)
//!     .build();
//!
//! let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx);
//! ```

mod diagnostic;
pub mod formatters;
mod i18n_helpers;
mod severity;
mod span;

// Re-export public API
pub use diagnostic::{Diagnostic, Label};
pub use severity::Severity;
pub use span::Span;

// Re-export i18n helpers under "i18n" module
pub mod i18n {
    pub use crate::i18n_helpers::{ctx1, ctx2, ctx3, ContextBuilder, IntoContextValue};
}

// Re-export commonly used formatters
pub use formatters::{DiagnosticFormatter, JsonFormatter, SimpleFormatter, TextFormatter};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_public_api() {
        // Verify all public types are accessible
        let _span = Span::new(0, 5, 1, 1);
        let _severity = Severity::Error;
        let _diag = Diagnostic::error("test");

        // Verify i18n helpers are accessible
        let _ctx = i18n::ctx1("key", "value");
        let _builder = i18n::ContextBuilder::new();
    }
}
