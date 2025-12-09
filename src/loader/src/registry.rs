use std::path::Path;
use std::sync::Arc;

use simple_common::ModuleCache;

use crate::loader::{LoadError, ModuleLoader};
use crate::module::LoadedModule;
use crate::smf::SymbolBinding;

/// Global module registry for tracking loaded modules
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

    /// Load or get cached module
    pub fn load(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        // Check cache first
        if let Some(module) = self.cache.get(path) {
            return Ok(module);
        }

        // Load new module with import resolution against already-loaded modules
        let module = Arc::new(self.loader.load_with_resolver(path, |name| {
            self.resolve_symbol(name)
        })?);

        // Cache it
        self.cache.insert(path, Arc::clone(&module));

        Ok(module)
    }

    /// Unload a module
    pub fn unload(&self, path: &Path) -> bool {
        self.cache.remove(path)
    }

    /// Reload a module (for hot reload)
    pub fn reload(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        // Load new version
        let new_module = Arc::new(self.loader.load_with_resolver(path, |name| {
            self.resolve_symbol(name)
        })?);

        // Replace in cache
        self.cache.insert(path, Arc::clone(&new_module));

        Ok(new_module)
    }

    /// Resolve symbol across all loaded modules
    pub fn resolve_symbol(&self, name: &str) -> Option<usize> {
        for module in self.cache.modules() {
            if let Some(sym) = module.symbols.lookup(name) {
                if sym.binding == SymbolBinding::Global {
                    let addr = module.code_mem.as_ptr() as usize + sym.value as usize;
                    return Some(addr);
                }
            }
        }

        None
    }
}
