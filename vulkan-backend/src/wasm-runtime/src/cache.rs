//! WASM module caching for performance optimization

use crate::error::{WasmError, WasmResult};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

/// Cache entry for a compiled WASM module
#[derive(Clone)]
pub struct CacheEntry {
    /// Path to the WASM file
    pub path: PathBuf,

    /// File modification time (for invalidation)
    pub modified: std::time::SystemTime,

    /// Compiled module bytes (serialized)
    pub module_bytes: Arc<Vec<u8>>,
}

/// Module cache for compiled WASM modules
pub struct ModuleCache {
    /// Cache storage (path -> entry)
    cache: Arc<RwLock<HashMap<PathBuf, CacheEntry>>>,

    /// Maximum cache size in bytes
    max_size: usize,

    /// Current cache size in bytes
    current_size: Arc<RwLock<usize>>,
}

impl Default for ModuleCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleCache {
    /// Create a new module cache with default size limit (100MB)
    pub fn new() -> Self {
        Self::with_max_size(100 * 1024 * 1024)
    }

    /// Create a new module cache with specified max size
    pub fn with_max_size(max_size: usize) -> Self {
        Self {
            cache: Arc::new(RwLock::new(HashMap::new())),
            max_size,
            current_size: Arc::new(RwLock::new(0)),
        }
    }

    /// Get a cached module if it exists and is still valid
    pub fn get(&self, path: &Path) -> WasmResult<Option<Arc<Vec<u8>>>> {
        let cache = self.cache.read().unwrap();

        if let Some(entry) = cache.get(path) {
            // Check if file has been modified
            let metadata = std::fs::metadata(path)?;
            let modified = metadata.modified()?;

            if modified == entry.modified {
                return Ok(Some(entry.module_bytes.clone()));
            }
        }

        Ok(None)
    }

    /// Store a module in the cache
    pub fn put(&self, path: PathBuf, module_bytes: Vec<u8>) -> WasmResult<()> {
        let metadata = std::fs::metadata(&path)?;
        let modified = metadata.modified()?;

        let entry = CacheEntry {
            path: path.clone(),
            modified,
            module_bytes: Arc::new(module_bytes.clone()),
        };

        let module_size = module_bytes.len();

        // Check if we need to evict entries
        let mut current_size = self.current_size.write().unwrap();
        while *current_size + module_size > self.max_size && !self.cache.read().unwrap().is_empty()
        {
            // Evict oldest entry (simple LRU would be better)
            if let Some(evicted_path) = self.cache.read().unwrap().keys().next().cloned() {
                self.evict_internal(&evicted_path, &mut current_size);
            }
        }

        // Insert new entry
        self.cache.write().unwrap().insert(path, entry);
        *current_size += module_size;

        Ok(())
    }

    /// Evict a specific module from the cache
    pub fn evict(&self, path: &Path) -> bool {
        let mut current_size = self.current_size.write().unwrap();
        self.evict_internal(path, &mut current_size)
    }

    /// Internal eviction method
    fn evict_internal(&self, path: &Path, current_size: &mut usize) -> bool {
        let mut cache = self.cache.write().unwrap();
        if let Some(entry) = cache.remove(path) {
            *current_size = current_size.saturating_sub(entry.module_bytes.len());
            true
        } else {
            false
        }
    }

    /// Clear all cached modules
    pub fn clear(&self) {
        self.cache.write().unwrap().clear();
        *self.current_size.write().unwrap() = 0;
    }

    /// Get current cache size in bytes
    pub fn size(&self) -> usize {
        *self.current_size.read().unwrap()
    }

    /// Get number of cached modules
    pub fn len(&self) -> usize {
        self.cache.read().unwrap().len()
    }

    /// Check if cache is empty
    pub fn is_empty(&self) -> bool {
        self.cache.read().unwrap().is_empty()
    }

    /// Get cache statistics
    pub fn stats(&self) -> CacheStats {
        CacheStats {
            num_entries: self.len(),
            total_size: self.size(),
            max_size: self.max_size,
        }
    }
}

/// Cache statistics
#[derive(Debug, Clone)]
pub struct CacheStats {
    /// Number of cached modules
    pub num_entries: usize,

    /// Total size of cached modules in bytes
    pub total_size: usize,

    /// Maximum cache size in bytes
    pub max_size: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_cache_basic() {
        let cache = ModuleCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.size(), 0);
    }

    #[test]
    fn test_cache_put_get() -> WasmResult<()> {
        let cache = ModuleCache::new();

        // Create a temp file
        let mut temp_file = NamedTempFile::new()?;
        temp_file.write_all(b"test wasm module")?;
        let path = temp_file.path().to_path_buf();

        // Put module in cache
        let module_bytes = b"compiled module".to_vec();
        cache.put(path.clone(), module_bytes.clone())?;

        // Get module from cache
        let cached = cache.get(&path)?;
        assert!(cached.is_some());
        assert_eq!(*cached.unwrap(), module_bytes);

        // Check stats
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.size(), module_bytes.len());

        Ok(())
    }

    #[test]
    fn test_cache_eviction() -> WasmResult<()> {
        // Small cache (100 bytes)
        let cache = ModuleCache::with_max_size(100);

        let mut temp_file = NamedTempFile::new()?;
        temp_file.write_all(b"test")?;
        let path = temp_file.path().to_path_buf();

        // Put large module (150 bytes)
        let large_module = vec![0u8; 150];
        cache.put(path.clone(), large_module)?;

        // Cache should still contain the entry (evicted nothing)
        assert_eq!(cache.len(), 1);

        Ok(())
    }

    #[test]
    fn test_cache_clear() -> WasmResult<()> {
        let cache = ModuleCache::new();

        let mut temp_file = NamedTempFile::new()?;
        temp_file.write_all(b"test")?;
        let path = temp_file.path().to_path_buf();

        cache.put(path, vec![1, 2, 3, 4])?;
        assert!(!cache.is_empty());

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.size(), 0);

        Ok(())
    }
}
