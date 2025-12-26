use std::collections::HashMap;
use std::env;

/// A unified dictionary-like interface for configuration, environment variables, and arguments.
///
/// Provides a consistent way to access configuration from multiple sources:
/// - Direct key-value pairs
/// - Environment variables
/// - Command-line arguments (--key=value or --key value format)
#[derive(Debug, Clone, Default)]
pub struct ConfigEnv {
    data: HashMap<String, String>,
}

impl ConfigEnv {
    /// Create a new empty ConfigEnv.
    pub fn new() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    /// Create a ConfigEnv from command-line arguments.
    ///
    /// Supports formats:
    /// - `--key=value`
    /// - `--key value`
    /// - `-k value`
    /// - Positional args stored as `_0`, `_1`, etc.
    pub fn from_args(args: &[String]) -> Self {
        let mut config = Self::new();
        let mut positional_idx = 0;
        let mut iter = args.iter().peekable();

        while let Some(arg) = iter.next() {
            if arg.starts_with("--") {
                let key_value = &arg[2..];
                if let Some(eq_pos) = key_value.find('=') {
                    // --key=value format
                    let key = &key_value[..eq_pos];
                    let value = &key_value[eq_pos + 1..];
                    config.set(key, value);
                } else if let Some(next) = iter.peek() {
                    if !next.starts_with('-') {
                        // --key value format
                        config.set(key_value, iter.next().unwrap());
                    } else {
                        // --flag (boolean)
                        config.set(key_value, "true");
                    }
                } else {
                    // --flag at end
                    config.set(key_value, "true");
                }
            } else if arg.starts_with('-') && arg.len() == 2 {
                // -k value format
                let key = &arg[1..];
                if let Some(next) = iter.peek() {
                    if !next.starts_with('-') {
                        config.set(key, iter.next().unwrap());
                    } else {
                        config.set(key, "true");
                    }
                } else {
                    config.set(key, "true");
                }
            } else {
                // Positional argument
                config.set(&format!("_{}", positional_idx), arg);
                positional_idx += 1;
            }
        }

        config
    }

    /// Create a ConfigEnv from all environment variables.
    pub fn from_env() -> Self {
        let mut config = Self::new();
        for (key, value) in env::vars() {
            config.set(&key, &value);
        }
        config
    }

    /// Create a ConfigEnv from environment variables with a specific prefix.
    ///
    /// The prefix is stripped from the key names.
    /// Example: with prefix "SIMPLE_", env var "SIMPLE_DEBUG" becomes key "DEBUG".
    pub fn from_env_with_prefix(prefix: &str) -> Self {
        let mut config = Self::new();
        for (key, value) in env::vars() {
            if key.starts_with(prefix) {
                let stripped_key = &key[prefix.len()..];
                config.set(stripped_key, &value);
            }
        }
        config
    }

    /// Get a value by key.
    pub fn get(&self, key: &str) -> Option<&str> {
        self.data.get(key).map(|s| s.as_str())
    }

    /// Get a value by key, or return a default.
    pub fn get_or<'a>(&'a self, key: &str, default: &'a str) -> &'a str {
        self.data.get(key).map(|s| s.as_str()).unwrap_or(default)
    }

    /// Set a key-value pair.
    pub fn set(&mut self, key: &str, value: &str) {
        self.data.insert(key.to_string(), value.to_string());
    }

    /// Check if a key exists.
    pub fn contains(&self, key: &str) -> bool {
        self.data.contains_key(key)
    }

    /// Remove a key and return its value.
    pub fn remove(&mut self, key: &str) -> Option<String> {
        self.data.remove(key)
    }

    /// Get a value as an integer.
    pub fn get_int(&self, key: &str) -> Option<i64> {
        self.data.get(key).and_then(|s| s.parse().ok())
    }

    /// Get a value as an integer with a default.
    pub fn get_int_or(&self, key: &str, default: i64) -> i64 {
        self.get_int(key).unwrap_or(default)
    }

    /// Get a value as a boolean.
    ///
    /// Returns true for "true", "1", "yes", "on" (case-insensitive).
    /// Returns false for "false", "0", "no", "off" (case-insensitive).
    /// Returns None for other values or missing keys.
    pub fn get_bool(&self, key: &str) -> Option<bool> {
        self.data
            .get(key)
            .and_then(|s| match s.to_lowercase().as_str() {
                "true" | "1" | "yes" | "on" => Some(true),
                "false" | "0" | "no" | "off" => Some(false),
                _ => None,
            })
    }

    /// Get a value as a boolean with a default.
    pub fn get_bool_or(&self, key: &str, default: bool) -> bool {
        self.get_bool(key).unwrap_or(default)
    }

    /// Iterate over all keys.
    pub fn keys(&self) -> impl Iterator<Item = &str> {
        self.data.keys().map(|s| s.as_str())
    }

    /// Iterate over all key-value pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &str)> {
        self.data.iter().map(|(k, v)| (k.as_str(), v.as_str()))
    }

    /// Get the number of entries.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Merge another ConfigEnv into this one.
    ///
    /// Values from `other` override existing values.
    pub fn merge(&mut self, other: &ConfigEnv) {
        for (key, value) in &other.data {
            self.data.insert(key.clone(), value.clone());
        }
    }

    /// Add environment variables to this config.
    ///
    /// Environment values override existing config values.
    pub fn with_env(mut self) -> Self {
        for (key, value) in env::vars() {
            self.set(&key, &value);
        }
        self
    }

    /// Add environment variables with a prefix to this config.
    pub fn with_env_prefix(mut self, prefix: &str) -> Self {
        for (key, value) in env::vars() {
            if key.starts_with(prefix) {
                let stripped_key = &key[prefix.len()..];
                self.set(stripped_key, &value);
            }
        }
        self
    }

    /// Add command-line arguments to this config.
    ///
    /// Argument values override existing config values.
    pub fn with_args(mut self, args: &[String]) -> Self {
        let args_config = Self::from_args(args);
        self.merge(&args_config);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_is_empty() {
        let config = ConfigEnv::new();
        assert!(config.is_empty());
        assert_eq!(config.len(), 0);
    }

    #[test]
    fn test_set_and_get() {
        let mut config = ConfigEnv::new();
        config.set("key1", "value1");
        config.set("key2", "value2");

        assert_eq!(config.get("key1"), Some("value1"));
        assert_eq!(config.get("key2"), Some("value2"));
        assert_eq!(config.get("nonexistent"), None);
    }

    #[test]
    fn test_get_or_default() {
        let mut config = ConfigEnv::new();
        config.set("existing", "value");

        assert_eq!(config.get_or("existing", "default"), "value");
        assert_eq!(config.get_or("missing", "default"), "default");
    }

    #[test]
    fn test_contains() {
        let mut config = ConfigEnv::new();
        config.set("key", "value");

        assert!(config.contains("key"));
        assert!(!config.contains("missing"));
    }

    #[test]
    fn test_remove() {
        let mut config = ConfigEnv::new();
        config.set("key", "value");

        assert_eq!(config.remove("key"), Some("value".to_string()));
        assert_eq!(config.get("key"), None);
        assert_eq!(config.remove("nonexistent"), None);
    }

    #[test]
    fn test_get_int() {
        let mut config = ConfigEnv::new();
        config.set("port", "8080");
        config.set("count", "-5");
        config.set("invalid", "not_a_number");

        assert_eq!(config.get_int("port"), Some(8080));
        assert_eq!(config.get_int("count"), Some(-5));
        assert_eq!(config.get_int("invalid"), None);
        assert_eq!(config.get_int("missing"), None);
    }

    #[test]
    fn test_get_int_or() {
        let mut config = ConfigEnv::new();
        config.set("port", "8080");

        assert_eq!(config.get_int_or("port", 3000), 8080);
        assert_eq!(config.get_int_or("missing", 3000), 3000);
    }

    #[test]
    fn test_get_bool() {
        let mut config = ConfigEnv::new();
        config.set("enabled", "true");
        config.set("disabled", "false");
        config.set("yes_val", "yes");
        config.set("no_val", "no");
        config.set("one", "1");
        config.set("zero", "0");
        config.set("on_val", "ON");
        config.set("off_val", "OFF");
        config.set("invalid", "maybe");

        assert_eq!(config.get_bool("enabled"), Some(true));
        assert_eq!(config.get_bool("disabled"), Some(false));
        assert_eq!(config.get_bool("yes_val"), Some(true));
        assert_eq!(config.get_bool("no_val"), Some(false));
        assert_eq!(config.get_bool("one"), Some(true));
        assert_eq!(config.get_bool("zero"), Some(false));
        assert_eq!(config.get_bool("on_val"), Some(true));
        assert_eq!(config.get_bool("off_val"), Some(false));
        assert_eq!(config.get_bool("invalid"), None);
        assert_eq!(config.get_bool("missing"), None);
    }

    #[test]
    fn test_get_bool_or() {
        let mut config = ConfigEnv::new();
        config.set("flag", "true");

        assert_eq!(config.get_bool_or("flag", false), true);
        assert_eq!(config.get_bool_or("missing", true), true);
        assert_eq!(config.get_bool_or("missing", false), false);
    }

    #[test]
    fn test_from_args_key_equals_value() {
        let args = vec!["--port=8080".to_string(), "--host=localhost".to_string()];
        let config = ConfigEnv::from_args(&args);

        assert_eq!(config.get("port"), Some("8080"));
        assert_eq!(config.get("host"), Some("localhost"));
    }

    #[test]
    fn test_from_args_key_space_value() {
        let args = vec![
            "--port".to_string(),
            "8080".to_string(),
            "--host".to_string(),
            "localhost".to_string(),
        ];
        let config = ConfigEnv::from_args(&args);

        assert_eq!(config.get("port"), Some("8080"));
        assert_eq!(config.get("host"), Some("localhost"));
    }

    #[test]
    fn test_from_args_short_flags() {
        let args = vec![
            "-p".to_string(),
            "8080".to_string(),
            "-h".to_string(),
            "localhost".to_string(),
        ];
        let config = ConfigEnv::from_args(&args);

        assert_eq!(config.get("p"), Some("8080"));
        assert_eq!(config.get("h"), Some("localhost"));
    }

    #[test]
    fn test_from_args_boolean_flags() {
        let args = vec!["--verbose".to_string(), "--debug".to_string()];
        let config = ConfigEnv::from_args(&args);

        assert_eq!(config.get("verbose"), Some("true"));
        assert_eq!(config.get("debug"), Some("true"));
    }

    #[test]
    fn test_from_args_positional() {
        let args = vec![
            "input.txt".to_string(),
            "output.txt".to_string(),
            "--flag".to_string(),
        ];
        let config = ConfigEnv::from_args(&args);

        assert_eq!(config.get("_0"), Some("input.txt"));
        assert_eq!(config.get("_1"), Some("output.txt"));
        assert_eq!(config.get("flag"), Some("true"));
    }

    #[test]
    fn test_merge() {
        let mut config1 = ConfigEnv::new();
        config1.set("key1", "value1");
        config1.set("key2", "original");

        let mut config2 = ConfigEnv::new();
        config2.set("key2", "overridden");
        config2.set("key3", "value3");

        config1.merge(&config2);

        assert_eq!(config1.get("key1"), Some("value1"));
        assert_eq!(config1.get("key2"), Some("overridden"));
        assert_eq!(config1.get("key3"), Some("value3"));
    }

    #[test]
    fn test_keys_and_iter() {
        let mut config = ConfigEnv::new();
        config.set("a", "1");
        config.set("b", "2");

        let keys: Vec<&str> = config.keys().collect();
        assert_eq!(keys.len(), 2);
        assert!(keys.contains(&"a"));
        assert!(keys.contains(&"b"));

        let pairs: Vec<(&str, &str)> = config.iter().collect();
        assert_eq!(pairs.len(), 2);
    }

    #[test]
    fn test_with_args_chain() {
        let mut config = ConfigEnv::new();
        config.set("default", "value");
        config.set("port", "3000");

        let args = vec!["--port=8080".to_string()];
        let config = config.with_args(&args);

        assert_eq!(config.get("default"), Some("value"));
        assert_eq!(config.get("port"), Some("8080")); // overridden
    }

    #[test]
    fn test_default_trait() {
        let config: ConfigEnv = Default::default();
        assert!(config.is_empty());
    }
}
