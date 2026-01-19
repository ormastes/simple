use crate::error::Result;
#[cfg(feature = "simple-format")]
use crate::error::I18nError;
use crate::locale::Locale;
use crate::message::LocalizedMessage;
#[cfg(feature = "simple-format")]
use crate::simple_catalog::SimpleCatalogParser;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

/// A message catalog for a specific domain and locale
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessageCatalog {
    /// Catalog version
    pub version: String,

    /// Locale this catalog is for (e.g., "en", "ko")
    pub locale: String,

    /// Domain this catalog covers (e.g., "parser", "compiler")
    pub domain: String,

    /// Map of message ID to localized message
    pub messages: HashMap<String, LocalizedMessage>,
}

impl MessageCatalog {
    /// Get a message by ID
    pub fn get(&self, id: &str) -> Option<&LocalizedMessage> {
        self.messages.get(id)
    }

    /// Check if a message exists
    pub fn contains(&self, id: &str) -> bool {
        self.messages.contains_key(id)
    }
}

/// Registry of message catalogs for multiple locales and domains
#[derive(Debug, Default)]
pub struct CatalogRegistry {
    /// Catalogs indexed by (locale, domain)
    catalogs: HashMap<(String, String), MessageCatalog>,

    /// Base directory for catalog files
    catalog_dir: Option<PathBuf>,
}

impl CatalogRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the base directory for catalog files
    pub fn with_catalog_dir<P: AsRef<Path>>(mut self, dir: P) -> Self {
        self.catalog_dir = Some(dir.as_ref().to_path_buf());
        self
    }

    /// Register a catalog
    pub fn register(&mut self, catalog: MessageCatalog) {
        let key = (catalog.locale.clone(), catalog.domain.clone());
        self.catalogs.insert(key, catalog);
    }

    /// Get a catalog for a specific locale and domain
    pub fn get(&self, locale: &str, domain: &str) -> Option<&MessageCatalog> {
        self.catalogs.get(&(locale.to_string(), domain.to_string()))
    }

    /// Load a catalog from the catalog directory
    ///
    /// Supports locale suffix pattern:
    /// - Default locale (en): `{catalog_dir}/__init__.spl`, `{catalog_dir}/parser.spl`
    /// - Other locales: `{catalog_dir}/__init__.ko.spl`, `{catalog_dir}/parser.ko.spl`
    ///
    /// Implements automatic fallback: if locale-specific file doesn't exist, falls back to default.
    ///
    /// **Note**: This method requires the `simple-format` feature to be enabled.
    /// Without this feature, only compile-time bootstrap messages are available.
    #[cfg(feature = "simple-format")]
    pub fn load(&mut self, locale: &str, domain: &str) -> Result<()> {
        let catalog_dir = self
            .catalog_dir
            .as_ref()
            .ok_or_else(|| I18nError::CatalogDirectoryNotFound("not set".to_string()))?;

        // Determine filename with locale suffix pattern
        let filename = self.get_catalog_filename(locale, domain);
        let path = catalog_dir.join(&filename);

        // Try locale-specific file first
        if path.exists() {
            let catalog = SimpleCatalogParser::parse_catalog(&path, domain, locale)?;
            self.register(catalog);
            return Ok(());
        }

        // If locale-specific file doesn't exist and locale is not default, try fallback to default
        if locale != "en" {
            let default_filename = self.get_catalog_filename("en", domain);
            let default_path = catalog_dir.join(&default_filename);

            if default_path.exists() {
                // Load with requested locale but from default file (fallback)
                let catalog = SimpleCatalogParser::parse_catalog(&default_path, domain, locale)?;
                self.register(catalog);
                return Ok(());
            }
        }

        // Neither locale-specific nor default file exists
        Err(I18nError::CatalogLoadError {
            path: path.display().to_string(),
            source: std::io::Error::new(std::io::ErrorKind::NotFound, "catalog file not found"),
        })
    }

    /// Stub for load() when simple-format feature is disabled
    #[cfg(not(feature = "simple-format"))]
    pub fn load(&mut self, _locale: &str, _domain: &str) -> Result<()> {
        // Without the simple-format feature, catalog loading from .spl files is not supported.
        // This is fine for simple-diagnostics which uses compile-time bootstrap messages.
        Ok(())
    }

    /// Get the catalog filename for a given locale and domain
    ///
    /// Pattern: `<basename>.<locale>.spl`
    /// - Default locale (en): No suffix
    /// - Other locales: Locale suffix before .spl
    #[cfg(feature = "simple-format")]
    fn get_catalog_filename(&self, locale: &str, domain: &str) -> String {
        let basename = if domain == "common" {
            "__init__"
        } else {
            domain
        };

        if locale == "en" {
            format!("{}.spl", basename)
        } else {
            format!("{}.{}.spl", basename, locale)
        }
    }

    /// Get a message with fallback logic
    ///
    /// Implements locale resolution chain:
    /// 1. Try full locale with region (e.g., "ko_KR")
    /// 2. Try language only (e.g., "ko")
    /// 3. Fall back to English ("en")
    /// 4. Return None if not found in any
    pub fn get_message(&self, locale: &Locale, domain: &str, id: &str) -> Option<&LocalizedMessage> {
        // Build fallback chain
        let mut locales_to_try = Vec::new();

        // 1. Try full locale if region is present (e.g., "ko_KR")
        if locale.region.is_some() {
            locales_to_try.push(locale.to_string());
        }

        // 2. Try language only (e.g., "ko")
        if locale.language_code() != "en" {
            locales_to_try.push(locale.language_code().to_string());
        }

        // 3. Fall back to English
        locales_to_try.push("en".to_string());

        // Try each locale in the fallback chain
        for locale_str in locales_to_try {
            if let Some(catalog) = self.get(&locale_str, domain) {
                if let Some(message) = catalog.get(id) {
                    return Some(message);
                }
            }
        }

        None
    }

    /// Ensure a catalog is loaded (loads if not already present)
    pub fn ensure_loaded(&mut self, locale: &str, domain: &str) -> Result<()> {
        if self.get(locale, domain).is_none() {
            self.load(locale, domain)?;
        }
        Ok(())
    }
}

/// Thread-safe catalog registry
pub struct SharedCatalogRegistry {
    inner: Arc<RwLock<CatalogRegistry>>,
}

impl SharedCatalogRegistry {
    /// Create a new shared registry
    pub fn new(registry: CatalogRegistry) -> Self {
        Self {
            inner: Arc::new(RwLock::new(registry)),
        }
    }

    /// Get a message with fallback logic
    pub fn get_message(&self, locale: &Locale, domain: &str, id: &str) -> Option<LocalizedMessage> {
        let registry = self.inner.read().unwrap();
        registry.get_message(locale, domain, id).cloned()
    }

    /// Ensure a catalog is loaded
    pub fn ensure_loaded(&self, locale: &str, domain: &str) -> Result<()> {
        let mut registry = self.inner.write().unwrap();
        registry.ensure_loaded(locale, domain)
    }
}

impl Clone for SharedCatalogRegistry {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io::Write;
    use tempfile::TempDir;

    fn create_test_catalog(dir: &Path, locale: &str, domain: &str, messages: Vec<(&str, &str)>) {
        // Build Simple language catalog file content
        let mut content = String::from("val messages = {\n");

        for (id, message_text) in messages {
            content.push_str(&format!(
                "    \"{}\": {{\n        \"id\": \"{}\",\n        \"title\": \"{} Title\",\n        \"message\": \"{}\"\n    }},\n",
                id, id, id, message_text
            ));
        }

        content.push_str("}\n");

        // Use locale suffix pattern: <basename>.<locale>.spl
        let basename = if domain == "common" { "__init__" } else { domain };
        let filename = if locale == "en" {
            format!("{}.spl", basename)
        } else {
            format!("{}.{}.spl", basename, locale)
        };

        let path = dir.join(filename);
        let mut file = fs::File::create(path).unwrap();
        file.write_all(content.as_bytes()).unwrap();
    }

    #[test]
    fn test_registry_get_message() {
        let temp_dir = TempDir::new().unwrap();
        create_test_catalog(temp_dir.path(), "en", "parser", vec![("E0001", "English message")]);
        create_test_catalog(temp_dir.path(), "ko", "parser", vec![("E0001", "Korean message")]);

        let mut registry = CatalogRegistry::new().with_catalog_dir(temp_dir.path());
        registry.load("en", "parser").unwrap();
        registry.load("ko", "parser").unwrap();

        // Get Korean message
        let ko_locale = Locale::new("ko", None::<String>);
        let message = registry.get_message(&ko_locale, "parser", "E0001").unwrap();
        assert_eq!(message.message, "Korean message");

        // Get English message
        let en_locale = Locale::new("en", None::<String>);
        let message = registry.get_message(&en_locale, "parser", "E0001").unwrap();
        assert_eq!(message.message, "English message");
    }

    #[test]
    fn test_registry_fallback_to_english() {
        let temp_dir = TempDir::new().unwrap();
        create_test_catalog(temp_dir.path(), "en", "parser", vec![("E0001", "English message")]);

        let mut registry = CatalogRegistry::new().with_catalog_dir(temp_dir.path());
        registry.load("en", "parser").unwrap();

        // Request Korean, but only English exists - should fall back
        let ko_locale = Locale::new("ko", None::<String>);
        let message = registry.get_message(&ko_locale, "parser", "E0001").unwrap();
        assert_eq!(message.message, "English message");
    }

    #[test]
    fn test_locale_suffix_pattern() {
        let temp_dir = TempDir::new().unwrap();

        // Create English (default) and Korean catalogs using locale suffix pattern
        create_test_catalog(temp_dir.path(), "en", "parser", vec![("E0001", "English message")]);
        create_test_catalog(temp_dir.path(), "ko", "parser", vec![("E0001", "Korean message")]);

        // Verify files were created with correct names
        assert!(temp_dir.path().join("parser.spl").exists());
        assert!(temp_dir.path().join("parser.ko.spl").exists());

        let mut registry = CatalogRegistry::new().with_catalog_dir(temp_dir.path());

        // Load both catalogs
        registry.load("en", "parser").unwrap();
        registry.load("ko", "parser").unwrap();

        // Verify English catalog
        let en_locale = Locale::new("en", None::<String>);
        let message = registry.get_message(&en_locale, "parser", "E0001").unwrap();
        assert_eq!(message.message, "English message");

        // Verify Korean catalog
        let ko_locale = Locale::new("ko", None::<String>);
        let message = registry.get_message(&ko_locale, "parser", "E0001").unwrap();
        assert_eq!(message.message, "Korean message");
    }

    #[test]
    fn test_locale_suffix_common_domain() {
        let temp_dir = TempDir::new().unwrap();

        // Create common domain catalogs (severity names)
        let mut content_en = String::from("val severity = {\n");
        content_en.push_str("    \"error\": \"error\",\n");
        content_en.push_str("    \"warning\": \"warning\"\n");
        content_en.push_str("}\n");

        let mut content_ko = String::from("val severity = {\n");
        content_ko.push_str("    \"error\": \"오류\",\n");
        content_ko.push_str("    \"warning\": \"경고\"\n");
        content_ko.push_str("}\n");

        // Write files with locale suffix pattern
        fs::write(temp_dir.path().join("__init__.spl"), content_en).unwrap();
        fs::write(temp_dir.path().join("__init__.ko.spl"), content_ko).unwrap();

        let mut registry = CatalogRegistry::new().with_catalog_dir(temp_dir.path());

        // Load both catalogs
        registry.load("en", "common").unwrap();
        registry.load("ko", "common").unwrap();

        // Verify English severity
        let en_locale = Locale::new("en", None::<String>);
        let message = registry.get_message(&en_locale, "common", "error").unwrap();
        assert_eq!(message.title, "error");

        // Verify Korean severity
        let ko_locale = Locale::new("ko", None::<String>);
        let message = registry.get_message(&ko_locale, "common", "error").unwrap();
        assert_eq!(message.title, "오류");
    }

    #[test]
    fn test_load_fallback_when_locale_file_missing() {
        let temp_dir = TempDir::new().unwrap();

        // Only create English catalog
        create_test_catalog(temp_dir.path(), "en", "parser", vec![("E0001", "English message")]);

        let mut registry = CatalogRegistry::new().with_catalog_dir(temp_dir.path());

        // Try to load Korean, should fall back to English file
        registry.load("ko", "parser").unwrap();

        // Verify we got the catalog (from English fallback)
        let ko_locale = Locale::new("ko", None::<String>);
        let message = registry.get_message(&ko_locale, "parser", "E0001").unwrap();
        assert_eq!(message.message, "English message");
    }

    #[test]
    fn test_full_fallback_chain() {
        let temp_dir = TempDir::new().unwrap();

        // Create catalogs with different messages
        create_test_catalog(temp_dir.path(), "en", "parser", vec![
            ("E0001", "English E0001"),
            ("E0002", "English E0002"),
            ("E0003", "English E0003"),
        ]);
        create_test_catalog(temp_dir.path(), "ko", "parser", vec![
            ("E0001", "Korean E0001"),
            ("E0002", "Korean E0002"),
        ]);

        let mut registry = CatalogRegistry::new().with_catalog_dir(temp_dir.path());
        registry.load("en", "parser").unwrap();
        registry.load("ko", "parser").unwrap();

        // Test 1: ko_KR locale with region
        let ko_kr_locale = Locale::new("ko", Some("KR"));

        // E0001 exists in Korean - should get Korean version
        let msg = registry.get_message(&ko_kr_locale, "parser", "E0001").unwrap();
        assert_eq!(msg.message, "Korean E0001");

        // E0002 exists in Korean - should get Korean version
        let msg = registry.get_message(&ko_kr_locale, "parser", "E0002").unwrap();
        assert_eq!(msg.message, "Korean E0002");

        // E0003 only exists in English - should fall back to English
        let msg = registry.get_message(&ko_kr_locale, "parser", "E0003").unwrap();
        assert_eq!(msg.message, "English E0003");

        // Test 2: ko locale without region
        let ko_locale = Locale::new("ko", None::<String>);

        // E0001 exists in Korean
        let msg = registry.get_message(&ko_locale, "parser", "E0001").unwrap();
        assert_eq!(msg.message, "Korean E0001");

        // E0003 falls back to English
        let msg = registry.get_message(&ko_locale, "parser", "E0003").unwrap();
        assert_eq!(msg.message, "English E0003");
    }
}
