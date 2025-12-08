use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

use crate::loader::{LoadError, ModuleLoader};
use crate::module::LoadedModule;
use crate::smf::SymbolBinding;

/// Global module registry for tracking loaded modules
pub struct ModuleRegistry {
    modules: RwLock<HashMap<PathBuf, Arc<LoadedModule>>>,
    loader: ModuleLoader,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self {
            modules: RwLock::new(HashMap::new()),
            loader: ModuleLoader::new(),
        }
    }

    /// Load or get cached module
    pub fn load(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        let canonical = path.canonicalize()?;

        // Check cache
        {
            let modules = self.modules.read().unwrap();
            if let Some(module) = modules.get(&canonical) {
                return Ok(Arc::clone(module));
            }
        }

        // Load new module with import resolution against already-loaded modules
        let module = Arc::new(self.loader.load_with_resolver(&canonical, |name| {
            self.resolve_symbol(name)
        })?);

        // Cache it
        {
            let mut modules = self.modules.write().unwrap();
            modules.insert(canonical, Arc::clone(&module));
        }

        Ok(module)
    }

    /// Unload a module
    pub fn unload(&self, path: &Path) -> bool {
        let canonical = path.canonicalize().ok();

        if let Some(canonical) = canonical {
            let mut modules = self.modules.write().unwrap();
            modules.remove(&canonical).is_some()
        } else {
            false
        }
    }

    /// Reload a module (for hot reload)
    pub fn reload(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        let canonical = path.canonicalize()?;

        // Load new version
        let new_module = Arc::new(self.loader.load_with_resolver(&canonical, |name| {
            self.resolve_symbol(name)
        })?);

        // Replace in cache
        {
            let mut modules = self.modules.write().unwrap();
            modules.insert(canonical, Arc::clone(&new_module));
        }

        Ok(new_module)
    }

    /// Resolve symbol across all loaded modules
    pub fn resolve_symbol(&self, name: &str) -> Option<usize> {
        let modules = self.modules.read().unwrap();

        for module in modules.values() {
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
