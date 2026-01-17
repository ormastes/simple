//! i18n (Internationalization) module for the Simple language
//!
//! This module provides:
//! - String extraction from source files
//! - Locale file generation
//! - Runtime locale loading and lookup

pub mod extractor;
pub mod locale;
pub mod registry;

pub use extractor::{ExtractionResult, I18nExtractor, I18nString};
pub use locale::{LocaleFile, LocaleGenerator};
pub use registry::{clear as clear_registry, get_locale, load_from_file, load_strings, lookup, lookup_or_placeholder, set_locale};
