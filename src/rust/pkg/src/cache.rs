//! Global package cache management

use std::path::{Path, PathBuf};

use crate::error::{PkgError, PkgResult};

/// Global package cache
#[derive(Debug, Clone)]
pub struct Cache {
    /// Root cache directory
    root: PathBuf,
}

impl Cache {
    /// Create a new cache with the default location
    pub fn new() -> PkgResult<Self> {
        let cache_dir = Self::default_cache_dir()?;
        Ok(Cache { root: cache_dir })
    }

    /// Create a cache at a specific location
    pub fn at(path: PathBuf) -> Self {
        Cache { root: path }
    }

    /// Get the default cache directory
    pub fn default_cache_dir() -> PkgResult<PathBuf> {
        dirs_next::cache_dir()
            .map(|p| p.join("simple"))
            .ok_or_else(|| PkgError::Cache("Could not determine cache directory".to_string()))
    }

    /// Get the cache root directory
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Get the path for git repositories
    pub fn git_dir(&self) -> PathBuf {
        self.root.join("git")
    }

    /// Get the path for registry packages
    pub fn registry_dir(&self) -> PathBuf {
        self.root.join("registry")
    }

    /// Get the path for downloaded packages
    pub fn packages_dir(&self) -> PathBuf {
        self.root.join("packages")
    }

    /// Initialize the cache directory structure
    pub fn init(&self) -> PkgResult<()> {
        std::fs::create_dir_all(self.git_dir())?;
        std::fs::create_dir_all(self.registry_dir())?;
        std::fs::create_dir_all(self.packages_dir())?;
        Ok(())
    }

    /// Get the path for a specific git repository
    pub fn git_repo_path(&self, url: &str) -> PathBuf {
        let hash = Self::hash_url(url);
        self.git_dir().join(hash)
    }

    /// Get the path for a cached package
    pub fn package_path(&self, name: &str, version: &str) -> PathBuf {
        self.packages_dir().join(format!("{}-{}", name, version))
    }

    /// Check if a git repository is cached
    pub fn has_git_repo(&self, url: &str) -> bool {
        self.git_repo_path(url).exists()
    }

    /// Check if a package is cached
    pub fn has_package(&self, name: &str, version: &str) -> bool {
        self.package_path(name, version).exists()
    }

    /// Hash a URL to a safe directory name
    fn hash_url(url: &str) -> String {
        // Simple hash: use last part of URL + truncated hash
        let clean_url = url.trim_end_matches('/').trim_end_matches(".git");

        let name = clean_url.rsplit('/').next().unwrap_or("unknown");

        // Simple hash based on full URL
        let hash: u64 = url
            .bytes()
            .fold(0u64, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u64));

        format!("{}-{:x}", name, hash & 0xFFFFFFFF)
    }

    /// Clean the entire cache
    pub fn clean(&self) -> PkgResult<()> {
        if self.root.exists() {
            std::fs::remove_dir_all(&self.root)?;
        }
        Ok(())
    }

    /// Clean only git repositories
    pub fn clean_git(&self) -> PkgResult<()> {
        let git_dir = self.git_dir();
        if git_dir.exists() {
            std::fs::remove_dir_all(&git_dir)?;
        }
        Ok(())
    }

    /// Get the total size of the cache in bytes
    pub fn size(&self) -> PkgResult<u64> {
        if !self.root.exists() {
            return Ok(0);
        }
        Self::dir_size(&self.root)
    }

    /// Calculate directory size recursively
    fn dir_size(path: &Path) -> PkgResult<u64> {
        let mut size = 0;
        for entry in walkdir::WalkDir::new(path) {
            let entry = entry.map_err(|e| PkgError::Cache(e.to_string()))?;
            if entry.file_type().is_file() {
                size += entry.metadata().map(|m| m.len()).unwrap_or(0);
            }
        }
        Ok(size)
    }

    /// List all cached packages
    pub fn list_packages(&self) -> PkgResult<Vec<(String, String)>> {
        let mut packages = Vec::new();
        let packages_dir = self.packages_dir();

        if !packages_dir.exists() {
            return Ok(packages);
        }

        for entry in std::fs::read_dir(&packages_dir)? {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().to_string();
            if let Some((pkg_name, version)) = name.rsplit_once('-') {
                packages.push((pkg_name.to_string(), version.to_string()));
            }
        }

        Ok(packages)
    }
}

impl Default for Cache {
    fn default() -> Self {
        Cache::new().unwrap_or_else(|_| Cache {
            root: PathBuf::from(".simple-cache"),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_cache_paths() {
        let cache = Cache::at(PathBuf::from("/tmp/simple-cache"));
        assert_eq!(cache.root(), Path::new("/tmp/simple-cache"));
        assert_eq!(cache.git_dir(), PathBuf::from("/tmp/simple-cache/git"));
        assert_eq!(cache.packages_dir(), PathBuf::from("/tmp/simple-cache/packages"));
    }

    #[test]
    fn test_package_path() {
        let cache = Cache::at(PathBuf::from("/tmp/simple-cache"));
        let path = cache.package_path("http", "1.0.0");
        assert_eq!(path, PathBuf::from("/tmp/simple-cache/packages/http-1.0.0"));
    }

    #[test]
    fn test_git_repo_path() {
        let cache = Cache::at(PathBuf::from("/tmp/simple-cache"));
        let path = cache.git_repo_path("https://github.com/user/mylib");
        assert!(path.to_string_lossy().contains("mylib"));
    }

    #[test]
    fn test_hash_url() {
        // Same URL should produce same hash
        let hash1 = Cache::hash_url("https://github.com/user/mylib");
        let hash2 = Cache::hash_url("https://github.com/user/mylib");
        assert_eq!(hash1, hash2);

        // Different URLs should produce different hashes
        let hash3 = Cache::hash_url("https://github.com/user/otherlib");
        assert_ne!(hash1, hash3);
    }

    #[test]
    fn test_cache_init() {
        let temp_dir = std::env::temp_dir().join("simple-cache-test-init");
        let _ = fs::remove_dir_all(&temp_dir);

        let cache = Cache::at(temp_dir.clone());
        cache.init().unwrap();

        assert!(cache.git_dir().exists());
        assert!(cache.registry_dir().exists());
        assert!(cache.packages_dir().exists());

        let _ = fs::remove_dir_all(&temp_dir);
    }
}
