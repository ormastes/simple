//! Build mode configuration for the Simple compiler.
//!
//! This module defines build modes (Debug, Release) that control
//! compiler behavior, optimizations, and validation rules.
//!
//! Also includes deterministic build configuration for reproducible outputs.

use chrono::{DateTime, Utc};

/// Build mode for compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuildMode {
    /// Debug mode: Full diagnostics, minimal optimizations, all runtime checks
    Debug,
    /// Release mode: Optimizations enabled, production-ready output
    Release,
}

/// Configuration for deterministic builds.
///
/// When enabled, ensures that builds are byte-identical across different
/// environments and build times, enabling reproducible builds and binary
/// verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeterministicConfig {
    /// Enable deterministic build mode
    pub enabled: bool,
    /// Override build timestamp (ISO 8601 format)
    pub timestamp: Option<String>,
    /// Random seed for deterministic ordering
    pub seed: u64,
    /// Normalize paths to relative paths
    pub normalize_paths: bool,
}

impl DeterministicConfig {
    /// Create a new deterministic config with all features enabled.
    pub fn new() -> Self {
        Self {
            enabled: true,
            timestamp: None,
            seed: 0,
            normalize_paths: true,
        }
    }

    /// Create a disabled deterministic config.
    pub fn disabled() -> Self {
        Self {
            enabled: false,
            timestamp: None,
            seed: 0,
            normalize_paths: false,
        }
    }

    /// Get the build timestamp as a DateTime, or current time if not specified.
    pub fn get_timestamp(&self) -> DateTime<Utc> {
        if let Some(ref ts) = self.timestamp {
            // Try to parse ISO 8601 timestamp
            if let Ok(dt) = DateTime::parse_from_rfc3339(ts) {
                return dt.with_timezone(&Utc);
            }
        }
        Utc::now()
    }

    /// Set the build timestamp from a string.
    pub fn with_timestamp(mut self, timestamp: String) -> Self {
        self.timestamp = Some(timestamp);
        self
    }

    /// Set the random seed.
    pub fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// Set whether to normalize paths.
    pub fn with_normalize_paths(mut self, normalize: bool) -> Self {
        self.normalize_paths = normalize;
        self
    }
}

impl Default for DeterministicConfig {
    fn default() -> Self {
        Self::disabled()
    }
}

impl BuildMode {
    /// Parse build mode from a string.
    pub fn from_str(s: &str) -> Result<Self, String> {
        match s.to_lowercase().as_str() {
            "debug" => Ok(BuildMode::Debug),
            "release" => Ok(BuildMode::Release),
            _ => Err(format!(
                "unknown build mode '{}', expected 'debug' or 'release'",
                s
            )),
        }
    }

    /// Returns true if this is debug mode.
    pub fn is_debug(self) -> bool {
        matches!(self, BuildMode::Debug)
    }

    /// Returns true if this is release mode.
    pub fn is_release(self) -> bool {
        matches!(self, BuildMode::Release)
    }

    /// Returns the mode name as a string.
    pub fn as_str(self) -> &'static str {
        match self {
            BuildMode::Debug => "debug",
            BuildMode::Release => "release",
        }
    }
}

impl Default for BuildMode {
    fn default() -> Self {
        BuildMode::Debug
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_debug() {
        assert_eq!(BuildMode::from_str("debug").unwrap(), BuildMode::Debug);
        assert_eq!(BuildMode::from_str("Debug").unwrap(), BuildMode::Debug);
        assert_eq!(BuildMode::from_str("DEBUG").unwrap(), BuildMode::Debug);
    }

    #[test]
    fn test_parse_release() {
        assert_eq!(BuildMode::from_str("release").unwrap(), BuildMode::Release);
        assert_eq!(BuildMode::from_str("Release").unwrap(), BuildMode::Release);
        assert_eq!(BuildMode::from_str("RELEASE").unwrap(), BuildMode::Release);
    }

    #[test]
    fn test_parse_invalid() {
        assert!(BuildMode::from_str("production").is_err());
        assert!(BuildMode::from_str("dev").is_err());
        assert!(BuildMode::from_str("").is_err());
    }

    #[test]
    fn test_is_debug() {
        assert!(BuildMode::Debug.is_debug());
        assert!(!BuildMode::Release.is_debug());
    }

    #[test]
    fn test_is_release() {
        assert!(BuildMode::Release.is_release());
        assert!(!BuildMode::Debug.is_release());
    }

    #[test]
    fn test_default() {
        assert_eq!(BuildMode::default(), BuildMode::Debug);
    }

    #[test]
    fn test_as_str() {
        assert_eq!(BuildMode::Debug.as_str(), "debug");
        assert_eq!(BuildMode::Release.as_str(), "release");
    }

    #[test]
    fn test_deterministic_config_new() {
        let config = DeterministicConfig::new();
        assert!(config.enabled);
        assert!(config.normalize_paths);
        assert_eq!(config.seed, 0);
        assert!(config.timestamp.is_none());
    }

    #[test]
    fn test_deterministic_config_disabled() {
        let config = DeterministicConfig::disabled();
        assert!(!config.enabled);
        assert!(!config.normalize_paths);
        assert_eq!(config.seed, 0);
        assert!(config.timestamp.is_none());
    }

    #[test]
    fn test_deterministic_config_default() {
        let config = DeterministicConfig::default();
        assert!(!config.enabled);
    }

    #[test]
    fn test_deterministic_config_with_timestamp() {
        let config = DeterministicConfig::new().with_timestamp("2025-01-15T10:00:00Z".to_string());
        assert_eq!(config.timestamp, Some("2025-01-15T10:00:00Z".to_string()));
    }

    #[test]
    fn test_deterministic_config_with_seed() {
        let config = DeterministicConfig::new().with_seed(42);
        assert_eq!(config.seed, 42);
    }

    #[test]
    fn test_deterministic_config_with_normalize_paths() {
        let config = DeterministicConfig::new().with_normalize_paths(false);
        assert!(!config.normalize_paths);
    }

    #[test]
    fn test_get_timestamp_with_override() {
        let config = DeterministicConfig::new().with_timestamp("2025-01-15T10:00:00Z".to_string());
        let timestamp = config.get_timestamp();
        assert_eq!(timestamp.to_rfc3339(), "2025-01-15T10:00:00+00:00");
    }

    #[test]
    fn test_get_timestamp_without_override() {
        let config = DeterministicConfig::new();
        let timestamp = config.get_timestamp();
        // Should return current time - just verify it's a valid timestamp
        assert!(timestamp.timestamp() > 0);
    }
}
