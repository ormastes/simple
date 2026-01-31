//! Internationalization (i18n) support for the Simple compiler
//!
//! This crate provides a simple JSON-based message catalog system for
//! localizing compiler error messages and other user-facing text.
//!
//! # Example
//!
//! ```rust
//! use simple_i18n::{I18n, MessageContext};
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! // Get the global i18n instance
//! let i18n = I18n::global();
//!
//! // Create a message context with placeholder values
//! let mut ctx = MessageContext::new();
//! ctx.insert("expected", "identifier");
//! ctx.insert("found", "number");
//!
//! // Get a localized message
//! if let Some(message) = i18n.get_message("parser", "E0002", &ctx) {
//!     println!("{}: {}", message.title, message.message);
//! }
//! # Ok(())
//! # }
//! ```

pub mod bootstrap;
pub mod catalog;
pub mod error;
pub mod locale;
pub mod message;

#[cfg(feature = "simple-format")]
pub mod simple_catalog;

// Include compile-time generated catalog maps (created by build.rs)
// This file contains DEFAULT_SEVERITY and DEFAULT_PARSER_MESSAGES constants
include!(concat!(env!("OUT_DIR"), "/generated.rs"));

use bootstrap::get_bootstrap_message;
use catalog::{CatalogRegistry, SharedCatalogRegistry};
use locale::Locale;
use once_cell::sync::OnceCell;
use std::path::PathBuf;

/// Global i18n instance
static GLOBAL_I18N: OnceCell<I18n> = OnceCell::new();

/// Main i18n interface
#[derive(Clone)]
pub struct I18n {
    registry: SharedCatalogRegistry,
    locale: Locale,
}

impl I18n {
    /// Create a new i18n instance with the given locale and catalog directory
    pub fn new(locale: Locale, catalog_dir: PathBuf) -> Self {
        let registry = CatalogRegistry::new().with_catalog_dir(catalog_dir);
        let registry = SharedCatalogRegistry::new(registry);

        Self { registry, locale }
    }

    /// Get the global i18n instance
    ///
    /// The global instance is initialized lazily on first access with:
    /// - Locale detected from environment variables (SIMPLE_LANG or LANG)
    /// - Catalog directory at workspace root: `i18n/locales/`
    pub fn global() -> &'static I18n {
        GLOBAL_I18N.get_or_init(|| {
            let locale = Locale::from_env();
            let catalog_dir = Self::find_catalog_dir();
            Self::new(locale, catalog_dir)
        })
    }

    /// Initialize the global i18n instance with a specific locale
    ///
    /// This must be called before the first call to `global()`.
    /// Returns an error if the global instance has already been initialized.
    pub fn init_global(locale: Locale, catalog_dir: PathBuf) -> std::result::Result<(), String> {
        let i18n = Self::new(locale, catalog_dir);
        GLOBAL_I18N
            .set(i18n)
            .map_err(|_| "Global I18n instance already initialized".to_string())
    }

    /// Find the catalog directory in the workspace
    ///
    /// Searches for `i18n/locales/` starting from the current directory and
    /// walking up the directory tree until the workspace root is found.
    fn find_catalog_dir() -> PathBuf {
        // Start from current directory
        let mut current = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

        // Walk up the directory tree looking for i18n/locales/
        loop {
            let candidate = current.join("i18n/locales");
            if candidate.exists() && candidate.is_dir() {
                return candidate;
            }

            // Try Cargo.toml as a marker for workspace root
            if current.join("Cargo.toml").exists() {
                let candidate = current.join("i18n/locales");
                // Even if it doesn't exist, use this as the base
                return candidate;
            }

            // Move up one directory
            match current.parent() {
                Some(parent) => current = parent.to_path_buf(),
                None => {
                    // Reached root, use default
                    return PathBuf::from("i18n/locales");
                }
            }
        }
    }

    /// Get the current locale
    pub fn locale(&self) -> &Locale {
        &self.locale
    }

    /// Set the locale (creates a new instance)
    pub fn with_locale(mut self, locale: Locale) -> Self {
        self.locale = locale;
        self
    }

    /// Get a localized message and interpolate it with the given context
    ///
    /// Returns None if the message is not found in any catalog (including English fallback).
    pub fn get_message(&self, domain: &str, id: &str, ctx: &MessageContext) -> Option<InterpolatedMessage> {
        // Ensure the catalog is loaded (for the current locale and English fallback)
        let _ = self.registry.ensure_loaded(self.locale.language_code(), domain);
        if self.locale.language_code() != "en" {
            let _ = self.registry.ensure_loaded("en", domain);
        }

        // Get the message with fallback
        let message = self.registry.get_message(&self.locale, domain, id)?;

        // Interpolate and return
        Some(message.interpolate(ctx))
    }

    /// Get a localized message with bootstrap fallback
    ///
    /// This method never fails - it will fall back to bootstrap messages
    /// if catalogs can't be loaded. Use this for critical error reporting
    /// where we need to display something even if i18n is broken.
    pub fn get_message_safe(&self, domain: &str, id: &str, ctx: &MessageContext) -> InterpolatedMessage {
        // Try to get from catalog first
        if let Some(msg) = self.get_message(domain, id, ctx) {
            return msg;
        }

        // Fall back to bootstrap messages
        if let Some(msg) = get_bootstrap_message(id) {
            return msg;
        }

        // Last resort: generate a generic error message
        InterpolatedMessage {
            id: id.to_string(),
            title: "Error".to_string(),
            message: format!("Error {}", id),
            label: None,
            help: None,
            note: None,
        }
    }

    /// Get a localized severity name
    ///
    /// Maps severity levels to localized strings:
    /// - "error" -> "error" (en) or "오류" (ko)
    /// - "warning" -> "warning" (en) or "경고" (ko)
    /// - "info" -> "info" (en) or "정보" (ko)
    pub fn severity_name(&self, severity: &str) -> String {
        let ctx = MessageContext::new();
        if let Some(msg) = self.get_message("common", &format!("severity.{}", severity), &ctx) {
            msg.message
        } else {
            // Fallback to the input if not found
            severity.to_string()
        }
    }
}

// Re-export commonly used types
pub use error::{I18nError, Result as I18nResult};
pub use message::{InterpolatedMessage, LocalizedMessage, MessageContext};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_catalog_dir() {
        let catalog_dir = I18n::find_catalog_dir();
        // Should find or create a path (exact path depends on test environment)
        assert!(catalog_dir.to_str().unwrap().contains("i18n/locales"));
    }

    #[test]
    fn test_global_instance() {
        let i18n = I18n::global();
        assert!(i18n.locale().language_code() == "en" || i18n.locale().language_code() == "ko");
    }
}
