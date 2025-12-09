use std::path::Path;
use std::sync::Arc;

use simple_common::ModuleCache;

use crate::loader::{LoadError, ModuleLoader};
use crate::module::LoadedModule;

/// Registry for native modules with caching
pub struct ModuleRegistry {
    cache: ModuleCache<LoadedModule, LoadError>,
    loader: ModuleLoader,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self {
            cache: ModuleCache::new(),
            loader: ModuleLoader::new(),
        }
    }

    pub fn load(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        // Check cache first
        if let Some(module) = self.cache.get(path) {
            return Ok(module);
        }

        let module = Arc::new(self.loader.load(path)?);

        // Cache it
        self.cache.insert(path, Arc::clone(&module));

        Ok(module)
    }

    pub fn unload(&self, path: &Path) -> bool {
        self.cache.remove(path)
    }

    pub fn reload(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        let new_module = Arc::new(self.loader.load(path)?);

        // Replace in cache
        self.cache.insert(path, Arc::clone(&new_module));

        Ok(new_module)
    }
}
