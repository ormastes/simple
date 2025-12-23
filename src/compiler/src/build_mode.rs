//! Build mode configuration for the Simple compiler.
//!
//! This module defines build modes (Debug, Release) that control
//! compiler behavior, optimizations, and validation rules.

/// Build mode for compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuildMode {
    /// Debug mode: Full diagnostics, minimal optimizations, all runtime checks
    Debug,
    /// Release mode: Optimizations enabled, production-ready output
    Release,
}

impl BuildMode {
    /// Parse build mode from a string.
    pub fn from_str(s: &str) -> Result<Self, String> {
        match s.to_lowercase().as_str() {
            "debug" => Ok(BuildMode::Debug),
            "release" => Ok(BuildMode::Release),
            _ => Err(format!("unknown build mode '{}', expected 'debug' or 'release'", s)),
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
}
