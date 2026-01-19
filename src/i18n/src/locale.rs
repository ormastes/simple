use crate::error::{I18nError, Result};

/// Represents a locale (e.g., "en", "ko", "en_US")
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Locale {
    /// Language code (e.g., "en", "ko")
    pub language: String,
    /// Optional region code (e.g., "US", "KR")
    pub region: Option<String>,
}

impl Locale {
    /// Create a new locale from language and optional region
    pub fn new(language: impl Into<String>, region: Option<impl Into<String>>) -> Self {
        Self {
            language: language.into(),
            region: region.map(|r| r.into()),
        }
    }

    /// Parse a locale string (e.g., "en", "ko", "en_US", "ko_KR")
    pub fn parse(s: &str) -> Result<Self> {
        let parts: Vec<&str> = s.split('_').collect();
        match parts.len() {
            1 => Ok(Self::new(parts[0], None::<String>)),
            2 => Ok(Self::new(parts[0], Some(parts[1]))),
            _ => Err(I18nError::InvalidLocale(s.to_string())),
        }
    }

    /// Get the language code (e.g., "en", "ko")
    pub fn language_code(&self) -> &str {
        &self.language
    }

    /// Get the full locale string (e.g., "en", "ko", "en_US")
    pub fn to_string(&self) -> String {
        if let Some(region) = &self.region {
            format!("{}_{}", self.language, region)
        } else {
            self.language.clone()
        }
    }

    /// Detect locale from environment variables
    ///
    /// Checks in order:
    /// 1. SIMPLE_LANG environment variable
    /// 2. LANG environment variable
    /// 3. Defaults to "en"
    pub fn from_env() -> Self {
        // Check SIMPLE_LANG first
        if let Ok(lang) = std::env::var("SIMPLE_LANG") {
            if let Ok(locale) = Self::parse(&lang) {
                return locale;
            }
        }

        // Check LANG environment variable
        if let Ok(lang) = std::env::var("LANG") {
            // LANG format is typically "en_US.UTF-8"
            let lang = lang.split('.').next().unwrap_or(&lang);
            if let Ok(locale) = Self::parse(lang) {
                return locale;
            }
        }

        // Default to English
        Self::new("en", None::<String>)
    }
}

impl Default for Locale {
    fn default() -> Self {
        Self::new("en", None::<String>)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_language_only() {
        let locale = Locale::parse("en").unwrap();
        assert_eq!(locale.language, "en");
        assert_eq!(locale.region, None);
    }

    #[test]
    fn test_parse_with_region() {
        let locale = Locale::parse("ko_KR").unwrap();
        assert_eq!(locale.language, "ko");
        assert_eq!(locale.region, Some("KR".to_string()));
    }

    #[test]
    fn test_to_string() {
        let locale1 = Locale::new("en", None::<String>);
        assert_eq!(locale1.to_string(), "en");

        let locale2 = Locale::new("ko", Some("KR"));
        assert_eq!(locale2.to_string(), "ko_KR");
    }

    #[test]
    fn test_from_env_default() {
        // When no env vars are set, should default to "en"
        std::env::remove_var("SIMPLE_LANG");
        std::env::remove_var("LANG");

        let locale = Locale::from_env();
        assert_eq!(locale.language, "en");
    }

    #[test]
    fn test_from_env_simple_lang() {
        std::env::set_var("SIMPLE_LANG", "ko");
        let locale = Locale::from_env();
        assert_eq!(locale.language, "ko");
        std::env::remove_var("SIMPLE_LANG");
    }
}
