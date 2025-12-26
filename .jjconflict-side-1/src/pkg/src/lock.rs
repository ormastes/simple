//! Lock file (simple.lock) handling for reproducible builds

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;

use crate::error::PkgResult;

/// Lock file for reproducible builds
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LockFile {
    /// Lock file format version
    #[serde(default = "default_version")]
    pub version: u32,
    /// Locked packages
    #[serde(default)]
    pub packages: Vec<LockedPackage>,
}

fn default_version() -> u32 {
    1
}

impl Default for LockFile {
    fn default() -> Self {
        LockFile {
            version: default_version(),
            packages: Vec::new(),
        }
    }
}

/// A locked package with exact resolution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LockedPackage {
    /// Package name
    pub name: String,
    /// Resolved version
    pub version: String,
    /// Source of the package
    pub source: PackageSource,
    /// Checksum for verification
    #[serde(default)]
    pub checksum: Option<String>,
    /// Dependencies of this package
    #[serde(default)]
    pub dependencies: Vec<String>,
}

/// Source of a locked package
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum PackageSource {
    /// Registry package
    Registry { registry: String },
    /// Git repository
    Git {
        url: String,
        #[serde(default)]
        rev: Option<String>,
    },
    /// Local path
    Path { path: String },
}

impl LockFile {
    /// Load lock file from path
    pub fn load(path: &Path) -> PkgResult<Self> {
        if !path.exists() {
            return Ok(LockFile::default());
        }
        let content = std::fs::read_to_string(path)?;
        Self::parse(&content)
    }

    /// Parse lock file from string
    pub fn parse(content: &str) -> PkgResult<Self> {
        let lock: LockFile = toml::from_str(content)?;
        Ok(lock)
    }

    /// Save lock file to path
    pub fn save(&self, path: &Path) -> PkgResult<()> {
        let content = toml::to_string_pretty(self)?;
        std::fs::write(path, content)?;
        Ok(())
    }

    /// Find a locked package by name
    pub fn find_package(&self, name: &str) -> Option<&LockedPackage> {
        self.packages.iter().find(|p| p.name == name)
    }

    /// Add or update a locked package
    pub fn add_package(&mut self, pkg: LockedPackage) {
        if let Some(existing) = self.packages.iter_mut().find(|p| p.name == pkg.name) {
            *existing = pkg;
        } else {
            self.packages.push(pkg);
        }
    }

    /// Remove a package from the lock file
    pub fn remove_package(&mut self, name: &str) -> Option<LockedPackage> {
        if let Some(pos) = self.packages.iter().position(|p| p.name == name) {
            Some(self.packages.remove(pos))
        } else {
            None
        }
    }

    /// Check if the lock file is empty
    pub fn is_empty(&self) -> bool {
        self.packages.is_empty()
    }

    /// Get all package names
    pub fn package_names(&self) -> Vec<&str> {
        self.packages.iter().map(|p| p.name.as_str()).collect()
    }

    /// Build a dependency graph from locked packages
    pub fn dependency_graph(&self) -> HashMap<&str, Vec<&str>> {
        self.packages
            .iter()
            .map(|p| {
                (
                    p.name.as_str(),
                    p.dependencies.iter().map(|s| s.as_str()).collect(),
                )
            })
            .collect()
    }
}

impl LockedPackage {
    /// Create a new locked package from a path dependency
    pub fn from_path(name: &str, version: &str, path: &str) -> Self {
        LockedPackage {
            name: name.to_string(),
            version: version.to_string(),
            source: PackageSource::Path {
                path: path.to_string(),
            },
            checksum: None,
            dependencies: Vec::new(),
        }
    }

    /// Create a new locked package from a git dependency
    pub fn from_git(name: &str, version: &str, url: &str, rev: Option<&str>) -> Self {
        LockedPackage {
            name: name.to_string(),
            version: version.to_string(),
            source: PackageSource::Git {
                url: url.to_string(),
                rev: rev.map(|s| s.to_string()),
            },
            checksum: None,
            dependencies: Vec::new(),
        }
    }

    /// Check if this is a path dependency
    pub fn is_path(&self) -> bool {
        matches!(self.source, PackageSource::Path { .. })
    }

    /// Check if this is a git dependency
    pub fn is_git(&self) -> bool {
        matches!(self.source, PackageSource::Git { .. })
    }

    /// Get the path for path dependencies
    pub fn get_path(&self) -> Option<&str> {
        match &self.source {
            PackageSource::Path { path } => Some(path),
            _ => None,
        }
    }

    /// Get the git URL for git dependencies
    pub fn get_git_url(&self) -> Option<&str> {
        match &self.source {
            PackageSource::Git { url, .. } => Some(url),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_lock_file() {
        let content = r#"
version = 1

[[packages]]
name = "http"
version = "1.0.0"
[packages.source]
type = "path"
path = "../http"

[[packages]]
name = "json"
version = "2.0.0"
dependencies = ["http"]
[packages.source]
type = "git"
url = "https://github.com/user/json"
rev = "abc123"
"#;
        let lock = LockFile::parse(content).unwrap();
        assert_eq!(lock.version, 1);
        assert_eq!(lock.packages.len(), 2);

        let http = lock.find_package("http").unwrap();
        assert!(http.is_path());
        assert_eq!(http.get_path(), Some("../http"));

        let json = lock.find_package("json").unwrap();
        assert!(json.is_git());
        assert_eq!(json.dependencies, vec!["http"]);
    }

    #[test]
    fn test_empty_lock_file() {
        let lock = LockFile::default();
        assert!(lock.is_empty());
        assert_eq!(lock.version, 1);
    }

    #[test]
    fn test_add_remove_package() {
        let mut lock = LockFile::default();

        let pkg = LockedPackage::from_path("mylib", "1.0.0", "../mylib");
        lock.add_package(pkg);
        assert!(!lock.is_empty());
        assert!(lock.find_package("mylib").is_some());

        lock.remove_package("mylib");
        assert!(lock.is_empty());
    }

    #[test]
    fn test_dependency_graph() {
        let mut lock = LockFile::default();
        lock.add_package(LockedPackage {
            name: "a".to_string(),
            version: "1.0.0".to_string(),
            source: PackageSource::Path {
                path: "../a".to_string(),
            },
            checksum: None,
            dependencies: vec!["b".to_string(), "c".to_string()],
        });
        lock.add_package(LockedPackage::from_path("b", "1.0.0", "../b"));
        lock.add_package(LockedPackage::from_path("c", "1.0.0", "../c"));

        let graph = lock.dependency_graph();
        assert_eq!(graph.get("a"), Some(&vec!["b", "c"]));
        assert_eq!(graph.get("b"), Some(&vec![]));
    }
}
