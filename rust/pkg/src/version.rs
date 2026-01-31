//! Semantic versioning support for package management
//!
//! Wraps the `semver` crate to integrate with the package manager error types.

use std::fmt;
use std::str::FromStr;

use crate::error::{PkgError, PkgResult};

/// A semantic version (e.g., "1.2.3")
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Version {
    inner: semver::Version,
}

impl Version {
    /// Create a new version from components
    pub fn new(major: u64, minor: u64, patch: u64) -> Self {
        Version {
            inner: semver::Version::new(major, minor, patch),
        }
    }

    /// Parse a version string
    pub fn parse(version: &str) -> PkgResult<Self> {
        let inner =
            semver::Version::parse(version).map_err(|e| PkgError::VersionParse(format!("{}: {}", version, e)))?;
        Ok(Version { inner })
    }

    /// Get the major version number
    pub fn major(&self) -> u64 {
        self.inner.major
    }

    /// Get the minor version number
    pub fn minor(&self) -> u64 {
        self.inner.minor
    }

    /// Get the patch version number
    pub fn patch(&self) -> u64 {
        self.inner.patch
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl FromStr for Version {
    type Err = PkgError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Version::parse(s)
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Version {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl Default for Version {
    fn default() -> Self {
        Version::new(0, 0, 0)
    }
}

/// A version requirement/constraint (e.g., "^1.0", ">=1.0,<3.0")
#[derive(Debug, Clone)]
pub struct VersionReq {
    inner: semver::VersionReq,
}

impl VersionReq {
    /// Create a requirement that matches any version
    pub fn any() -> Self {
        VersionReq {
            inner: semver::VersionReq::STAR,
        }
    }

    /// Parse a version requirement string
    ///
    /// Supports various formats:
    /// - Simple: "1.0", "1.0.0"
    /// - Caret: "^1.0" (compatible versions)
    /// - Tilde: "~1.0" (patch-level changes)
    /// - Comparison: ">=1.0", "<2.0", ">=1.0,<3.0"
    /// - Wildcard: "*", "1.*", "1.2.*"
    /// - Exact: "=1.0.0"
    pub fn parse(req: &str) -> PkgResult<Self> {
        let req = req.trim();

        // Handle empty or "*" as any
        if req.is_empty() || req == "*" {
            return Ok(Self::any());
        }

        // Try to parse as semver requirement
        let inner = semver::VersionReq::parse(req).map_err(|e| PkgError::VersionParse(format!("{}: {}", req, e)))?;

        Ok(VersionReq { inner })
    }

    /// Check if a version matches this requirement
    pub fn matches(&self, version: &Version) -> bool {
        self.inner.matches(&version.inner)
    }

    /// Check if this is the "any" requirement
    pub fn is_any(&self) -> bool {
        self.inner == semver::VersionReq::STAR
    }
}

impl fmt::Display for VersionReq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl FromStr for VersionReq {
    type Err = PkgError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        VersionReq::parse(s)
    }
}

impl Default for VersionReq {
    fn default() -> Self {
        VersionReq::any()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_version() {
        let v = Version::parse("1.2.3").unwrap();
        assert_eq!(v.major(), 1);
        assert_eq!(v.minor(), 2);
        assert_eq!(v.patch(), 3);
    }

    #[test]
    fn test_version_comparison() {
        let v1 = Version::parse("1.0.0").unwrap();
        let v2 = Version::parse("1.0.1").unwrap();
        let v3 = Version::parse("2.0.0").unwrap();

        assert!(v1 < v2);
        assert!(v2 < v3);
        assert!(v1 < v3);
    }

    #[test]
    fn test_parse_version_req_simple() {
        assert!(VersionReq::parse("1.0").is_ok());
        assert!(VersionReq::parse("1.0.0").is_ok());
        assert!(VersionReq::parse("0.1.0").is_ok());
    }

    #[test]
    fn test_parse_version_req_caret() {
        let req = VersionReq::parse("^1.0").unwrap();
        assert!(req.matches(&Version::parse("1.0.0").unwrap()));
        assert!(req.matches(&Version::parse("1.5.0").unwrap()));
        assert!(!req.matches(&Version::parse("2.0.0").unwrap()));
    }

    #[test]
    fn test_parse_version_req_tilde() {
        let req = VersionReq::parse("~1.2").unwrap();
        assert!(req.matches(&Version::parse("1.2.0").unwrap()));
        assert!(req.matches(&Version::parse("1.2.5").unwrap()));
        assert!(!req.matches(&Version::parse("1.3.0").unwrap()));
    }

    #[test]
    fn test_parse_version_req_comparison() {
        let req = VersionReq::parse(">=1.0, <3.0").unwrap();
        assert!(!req.matches(&Version::parse("0.9.0").unwrap()));
        assert!(req.matches(&Version::parse("1.0.0").unwrap()));
        assert!(req.matches(&Version::parse("2.5.0").unwrap()));
        assert!(!req.matches(&Version::parse("3.0.0").unwrap()));
    }

    #[test]
    fn test_parse_version_req_wildcard() {
        let req = VersionReq::parse("*").unwrap();
        assert!(req.is_any());
        assert!(req.matches(&Version::parse("0.0.1").unwrap()));
        assert!(req.matches(&Version::parse("99.99.99").unwrap()));
    }

    #[test]
    fn test_parse_version_req_exact() {
        let req = VersionReq::parse("=1.2.3").unwrap();
        assert!(req.matches(&Version::parse("1.2.3").unwrap()));
        assert!(!req.matches(&Version::parse("1.2.4").unwrap()));
    }

    #[test]
    fn test_version_display() {
        let v = Version::new(1, 2, 3);
        assert_eq!(v.to_string(), "1.2.3");
    }

    #[test]
    fn test_version_req_display() {
        let req = VersionReq::parse("^1.0").unwrap();
        assert!(req.to_string().contains("1.0"));
    }

    #[test]
    fn test_invalid_version() {
        assert!(Version::parse("not-a-version").is_err());
        assert!(Version::parse("1.2.3.4").is_err());
        assert!(Version::parse("").is_err());
    }

    #[test]
    fn test_invalid_version_req() {
        assert!(VersionReq::parse(">>>1.0").is_err());
    }
}
