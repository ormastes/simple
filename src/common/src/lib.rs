use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

pub mod config_env;
pub use config_env::ConfigEnv;

pub mod manual;
pub use manual::{Handle, HandlePool, ManualGc, Shared, Unique, WeakPtr};

pub mod actor;
pub use actor::{ActorHandle, ActorSpawner, Message, ThreadSpawner};

/// Common interface for dynamically loaded modules.
pub trait DynModule {
    /// Lookup a function symbol by name.
    fn get_fn<F: Copy>(&self, name: &str) -> Option<F>;

    /// Entry point convenience (typically `main`).
    fn entry_fn<F: Copy>(&self) -> Option<F>;
}

/// Common interface for module loaders.
pub trait DynLoader {
    type Module: DynModule;
    type Error: std::error::Error + 'static;

    /// Load a module from disk.
    fn load(&self, path: &Path) -> Result<Self::Module, Self::Error>;

    /// Load with an optional resolver for external symbols.
    fn load_with_resolver<F>(&self, path: &Path, resolver: F) -> Result<Self::Module, Self::Error>
    where
        F: Fn(&str) -> Option<usize>,
    {
        let _ = resolver;
        self.load(path)
    }
}

/// Generic module cache that can be reused by different loaders.
/// Provides caching, load, unload, and reload functionality.
pub struct ModuleCache<M, E> {
    modules: RwLock<HashMap<PathBuf, Arc<M>>>,
    _error: std::marker::PhantomData<E>,
}

impl<M, E> ModuleCache<M, E> {
    pub fn new() -> Self {
        Self {
            modules: RwLock::new(HashMap::new()),
            _error: std::marker::PhantomData,
        }
    }

    /// Get a cached module if it exists
    pub fn get(&self, path: &Path) -> Option<Arc<M>> {
        let canonical = path.canonicalize().ok()?;
        let modules = self.modules.read().unwrap();
        modules.get(&canonical).map(Arc::clone)
    }

    /// Insert a module into the cache
    pub fn insert(&self, path: &Path, module: Arc<M>) -> Option<PathBuf> {
        let canonical = path.canonicalize().ok()?;
        let mut modules = self.modules.write().unwrap();
        modules.insert(canonical.clone(), module);
        Some(canonical)
    }

    /// Remove a module from the cache
    pub fn remove(&self, path: &Path) -> bool {
        if let Ok(canonical) = path.canonicalize() {
            let mut modules = self.modules.write().unwrap();
            modules.remove(&canonical).is_some()
        } else {
            false
        }
    }

    /// Get all cached modules
    pub fn modules(&self) -> Vec<Arc<M>> {
        let modules = self.modules.read().unwrap();
        modules.values().map(Arc::clone).collect()
    }
}

impl<M, E> Default for ModuleCache<M, E> {
    fn default() -> Self {
        Self::new()
    }
}

pub mod gc;
