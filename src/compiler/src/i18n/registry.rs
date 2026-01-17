//! Locale Registry for i18n Runtime Support
//!
//! This module provides a thread-local registry for locale strings that can be
//! queried at runtime by the interpreter to look up i18n strings.
//!
//! # Usage
//!
//! ```ignore
//! use simple_compiler::i18n::registry;
//!
//! // Load a locale file
//! registry::load_locale_file(Path::new("i18n/__init__.ko-KR.spl"));
//!
//! // Set active locale
//! registry::set_locale("ko-KR");
//!
//! // Lookup a string
//! let text = registry::lookup("Greeting_");
//! ```

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::Path;

use super::locale::load_locale_file;

/// Thread-local locale registry
thread_local! {
    /// Currently active locale (e.g., "ko-KR", "en-US")
    static CURRENT_LOCALE: RefCell<String> = RefCell::new("default".to_string());

    /// Loaded locale strings: locale -> (name -> text)
    static LOCALE_STRINGS: RefCell<HashMap<String, HashMap<String, String>>> =
        RefCell::new(HashMap::new());
}

/// Set the current active locale
///
/// This determines which locale's strings are returned by `lookup()`.
/// If the locale hasn't been loaded, lookups will fall back to "default".
pub fn set_locale(locale: &str) {
    CURRENT_LOCALE.with(|cell| {
        *cell.borrow_mut() = locale.to_string();
    });
}

/// Get the current active locale
pub fn get_locale() -> String {
    CURRENT_LOCALE.with(|cell| cell.borrow().clone())
}

/// Load strings from a locale file into the registry
///
/// The locale code is extracted from the file path:
/// - `__init__.spl` -> "default"
/// - `__init__.ko-KR.spl` -> "ko-KR"
///
/// Returns `Ok(locale_code)` on success.
pub fn load_from_file(path: &Path) -> std::io::Result<String> {
    let locale_file = load_locale_file(path)?;
    let locale_code = locale_file.locale.clone();

    LOCALE_STRINGS.with(|cell| {
        let mut registry = cell.borrow_mut();
        let locale_map = registry.entry(locale_code.clone()).or_insert_with(HashMap::new);

        for (name, text) in locale_file.strings {
            locale_map.insert(name, text);
        }
    });

    Ok(locale_code)
}

/// Load strings directly into the registry
///
/// This is useful for testing or when strings are provided programmatically.
pub fn load_strings(locale: &str, strings: HashMap<String, String>) {
    LOCALE_STRINGS.with(|cell| {
        let mut registry = cell.borrow_mut();
        let locale_map = registry.entry(locale.to_string()).or_insert_with(HashMap::new);
        locale_map.extend(strings);
    });
}

/// Look up an i18n string by name
///
/// Lookup order:
/// 1. Current locale
/// 2. "default" locale (fallback)
/// 3. Returns `None` if not found in either
pub fn lookup(name: &str) -> Option<String> {
    let current = get_locale();

    LOCALE_STRINGS.with(|cell| {
        let registry = cell.borrow();

        // Try current locale first
        if let Some(locale_strings) = registry.get(&current) {
            if let Some(text) = locale_strings.get(name) {
                return Some(text.clone());
            }
        }

        // Fall back to default locale
        if current != "default" {
            if let Some(default_strings) = registry.get("default") {
                if let Some(text) = default_strings.get(name) {
                    return Some(text.clone());
                }
            }
        }

        None
    })
}

/// Look up an i18n string, returning the name as placeholder if not found
///
/// This is useful for the interpreter to always return something meaningful.
pub fn lookup_or_placeholder(name: &str) -> String {
    lookup(name).unwrap_or_else(|| format!("[i18n:{}]", name))
}

/// Clear all loaded locales
///
/// Useful for testing or resetting state between runs.
pub fn clear() {
    CURRENT_LOCALE.with(|cell| {
        *cell.borrow_mut() = "default".to_string();
    });
    LOCALE_STRINGS.with(|cell| {
        cell.borrow_mut().clear();
    });
}

/// Check if a locale has been loaded
pub fn is_locale_loaded(locale: &str) -> bool {
    LOCALE_STRINGS.with(|cell| cell.borrow().contains_key(locale))
}

/// Get list of loaded locales
pub fn loaded_locales() -> Vec<String> {
    LOCALE_STRINGS.with(|cell| cell.borrow().keys().cloned().collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup() {
        clear();
    }

    #[test]
    fn test_load_and_lookup() {
        setup();

        let mut strings = HashMap::new();
        strings.insert("Greeting_".to_string(), "Hello!".to_string());
        strings.insert("Farewell_".to_string(), "Goodbye!".to_string());

        load_strings("default", strings);

        assert_eq!(lookup("Greeting_"), Some("Hello!".to_string()));
        assert_eq!(lookup("Farewell_"), Some("Goodbye!".to_string()));
        assert_eq!(lookup("NonExistent_"), None);
    }

    #[test]
    fn test_locale_fallback() {
        setup();

        // Load default locale
        let mut default_strings = HashMap::new();
        default_strings.insert("Greeting_".to_string(), "Hello!".to_string());
        default_strings.insert("DefaultOnly_".to_string(), "Default only".to_string());
        load_strings("default", default_strings);

        // Load Korean locale (partial translation)
        let mut ko_strings = HashMap::new();
        ko_strings.insert("Greeting_".to_string(), "안녕하세요!".to_string());
        load_strings("ko-KR", ko_strings);

        // Test with default locale
        set_locale("default");
        assert_eq!(lookup("Greeting_"), Some("Hello!".to_string()));

        // Switch to Korean
        set_locale("ko-KR");
        assert_eq!(lookup("Greeting_"), Some("안녕하세요!".to_string()));

        // Korean falls back to default for untranslated strings
        assert_eq!(lookup("DefaultOnly_"), Some("Default only".to_string()));
    }

    #[test]
    fn test_lookup_or_placeholder() {
        setup();

        let mut strings = HashMap::new();
        strings.insert("Exists_".to_string(), "I exist".to_string());
        load_strings("default", strings);

        assert_eq!(lookup_or_placeholder("Exists_"), "I exist");
        assert_eq!(lookup_or_placeholder("Missing_"), "[i18n:Missing_]");
    }

    #[test]
    fn test_loaded_locales() {
        setup();

        load_strings("default", HashMap::new());
        load_strings("en-US", HashMap::new());
        load_strings("ko-KR", HashMap::new());

        let locales = loaded_locales();
        assert!(locales.contains(&"default".to_string()));
        assert!(locales.contains(&"en-US".to_string()));
        assert!(locales.contains(&"ko-KR".to_string()));
    }
}
