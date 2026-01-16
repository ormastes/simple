//! i18n (Internationalization) module for the Simple language
//!
//! This module provides:
//! - String extraction from source files
//! - Locale file generation
//! - Runtime locale loading

pub mod extractor;
pub mod locale;

pub use extractor::{I18nString, I18nExtractor, ExtractionResult};
pub use locale::{LocaleFile, LocaleGenerator};
