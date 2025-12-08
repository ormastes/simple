use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

use crate::loader::{LoadError, ModuleLoader};
use crate::module::LoadedModule;

/// Registry for native modules with caching
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

    pub fn load(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        let canonical = path.canonicalize()?;

        {
            let modules = self.modules.read().unwrap();
            if let Some(m) = modules.get(&canonical) {
                return Ok(Arc::clone(m));
            }
        }

        let module = Arc::new(self.loader.load(&canonical)?);

        {
            let mut modules = self.modules.write().unwrap();
            modules.insert(canonical, Arc::clone(&module));
        }

        Ok(module)
    }

    pub fn unload(&self, path: &Path) -> bool {
        if let Ok(canonical) = path.canonicalize() {
            let mut modules = self.modules.write().unwrap();
            modules.remove(&canonical).is_some()
        } else {
            false
        }
    }

    pub fn reload(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        let canonical = path.canonicalize()?;
        let new_module = Arc::new(self.loader.load(&canonical)?);

        {
            let mut modules = self.modules.write().unwrap();
            modules.insert(canonical, Arc::clone(&new_module));
        }

        Ok(new_module)
    }
}
