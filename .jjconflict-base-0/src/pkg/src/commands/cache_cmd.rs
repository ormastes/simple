//! `simple cache` commands - Manage the global package cache

use std::path::PathBuf;

use crate::cache::Cache;
use crate::error::PkgResult;

/// Information about the cache
#[derive(Debug)]
pub struct CacheInfo {
    /// Cache location
    pub location: PathBuf,
    /// Total size in bytes
    pub size_bytes: u64,
    /// Number of cached packages
    pub package_count: usize,
    /// Number of cached git repositories
    pub git_repo_count: usize,
}

/// Get cache information
pub fn cache_info() -> PkgResult<CacheInfo> {
    let cache = Cache::new()?;

    let packages = cache.list_packages()?;
    let git_count = count_git_repos(&cache)?;

    Ok(CacheInfo {
        location: cache.root().to_path_buf(),
        size_bytes: cache.size()?,
        package_count: packages.len(),
        git_repo_count: git_count,
    })
}

/// List all cached packages
pub fn cache_list() -> PkgResult<Vec<(String, String)>> {
    let cache = Cache::new()?;
    cache.list_packages()
}

/// Clean the entire cache
///
/// Returns the number of bytes freed.
pub fn cache_clean() -> PkgResult<u64> {
    let cache = Cache::new()?;
    let size = cache.size()?;
    cache.clean()?;
    Ok(size)
}

/// Clean only git repositories from cache
pub fn cache_clean_git() -> PkgResult<()> {
    let cache = Cache::new()?;
    cache.clean_git()
}

/// Count git repositories in cache
fn count_git_repos(cache: &Cache) -> PkgResult<usize> {
    let git_dir = cache.git_dir();
    if !git_dir.exists() {
        return Ok(0);
    }

    let count = std::fs::read_dir(&git_dir)?
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().map(|t| t.is_dir()).unwrap_or(false))
        .count();

    Ok(count)
}

/// Format bytes as human-readable size
pub fn format_size(bytes: u64) -> String {
    const KB: u64 = 1024;
    const MB: u64 = KB * 1024;
    const GB: u64 = MB * 1024;

    if bytes >= GB {
        format!("{:.2} GB", bytes as f64 / GB as f64)
    } else if bytes >= MB {
        format!("{:.2} MB", bytes as f64 / MB as f64)
    } else if bytes >= KB {
        format!("{:.2} KB", bytes as f64 / KB as f64)
    } else {
        format!("{} bytes", bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_size_bytes() {
        assert_eq!(format_size(0), "0 bytes");
        assert_eq!(format_size(512), "512 bytes");
        assert_eq!(format_size(1023), "1023 bytes");
    }

    #[test]
    fn test_format_size_kb() {
        assert_eq!(format_size(1024), "1.00 KB");
        assert_eq!(format_size(2048), "2.00 KB");
        assert_eq!(format_size(1536), "1.50 KB");
    }

    #[test]
    fn test_format_size_mb() {
        assert_eq!(format_size(1024 * 1024), "1.00 MB");
        assert_eq!(format_size(5 * 1024 * 1024), "5.00 MB");
    }

    #[test]
    fn test_format_size_gb() {
        assert_eq!(format_size(1024 * 1024 * 1024), "1.00 GB");
        assert_eq!(format_size(2 * 1024 * 1024 * 1024), "2.00 GB");
    }

    #[test]
    fn test_cache_info() {
        // This test just ensures the function doesn't panic
        let result = cache_info();
        assert!(result.is_ok());
    }

    #[test]
    fn test_cache_list() {
        let result = cache_list();
        assert!(result.is_ok());
    }
}
