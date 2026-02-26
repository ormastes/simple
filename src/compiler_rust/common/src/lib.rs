use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

pub mod config_env;
pub use config_env::ConfigEnv;

pub mod file_reader;
pub use file_reader::{FileReader, MappedFile, ReadStrategy};

pub mod manual;
pub mod manual_mem;
pub use manual_mem::{Handle, HandlePool, ManualGc, Shared, Unique, WeakPtr};

pub mod actor;
pub use actor::{ActorHandle, ActorSpawner, Message, ThreadSpawner};

pub mod runtime_symbols;
pub use runtime_symbols::{AbiVersion, RuntimeSymbolProvider, RUNTIME_SYMBOL_NAMES};

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

/// Generic module registry that wraps a loader and cache.
/// Provides load, unload, and reload functionality with caching.
pub struct ModuleRegistry<L: DynLoader> {
    cache: ModuleCache<L::Module, L::Error>,
    loader: L,
}

impl<L: DynLoader> ModuleRegistry<L> {
    pub fn new(loader: L) -> Self {
        Self {
            cache: ModuleCache::new(),
            loader,
        }
    }

    /// Get the underlying cache for direct access
    pub fn cache(&self) -> &ModuleCache<L::Module, L::Error> {
        &self.cache
    }

    /// Get all cached modules
    pub fn modules(&self) -> Vec<Arc<L::Module>> {
        self.cache.modules()
    }

    /// Load or get cached module (simple version without resolver)
    pub fn load(&self, path: &Path) -> Result<Arc<L::Module>, L::Error> {
        // Check cache first
        if let Some(module) = self.cache.get(path) {
            return Ok(module);
        }

        let module = Arc::new(self.loader.load(path)?);
        self.cache.insert(path, Arc::clone(&module));
        Ok(module)
    }

    /// Load with a custom resolver for external symbols
    pub fn load_with_resolver<F>(&self, path: &Path, resolver: F) -> Result<Arc<L::Module>, L::Error>
    where
        F: Fn(&str) -> Option<usize>,
    {
        // Check cache first
        if let Some(module) = self.cache.get(path) {
            return Ok(module);
        }

        let module = Arc::new(self.loader.load_with_resolver(path, resolver)?);
        self.cache.insert(path, Arc::clone(&module));
        Ok(module)
    }

    /// Unload a module from cache
    pub fn unload(&self, path: &Path) -> bool {
        self.cache.remove(path)
    }

    /// Reload a module (simple version)
    pub fn reload(&self, path: &Path) -> Result<Arc<L::Module>, L::Error> {
        let new_module = Arc::new(self.loader.load(path)?);
        self.cache.insert(path, Arc::clone(&new_module));
        Ok(new_module)
    }

    /// Reload with a custom resolver
    pub fn reload_with_resolver<F>(&self, path: &Path, resolver: F) -> Result<Arc<L::Module>, L::Error>
    where
        F: Fn(&str) -> Option<usize>,
    {
        let new_module = Arc::new(self.loader.load_with_resolver(path, resolver)?);
        self.cache.insert(path, Arc::clone(&new_module));
        Ok(new_module)
    }
}

impl<L: DynLoader + Default> Default for ModuleRegistry<L> {
    fn default() -> Self {
        Self::new(L::default())
    }
}

pub mod platform;

pub mod fault_detection;

pub mod gc;

pub mod target;
pub use target::{
    LinkerFlavor, PointerSize, Target, TargetArch, TargetConfig, TargetOS, TargetParseError,
};

pub mod diagnostic;
pub use diagnostic::{Diagnostic, EasyFix, FixConfidence, Label, Replacement, Severity, Span};

pub mod fix_applicator;

pub mod easy_fix_rules;

pub mod protocol;
pub use protocol::{read_message, write_message, TransportError};

pub mod safety;
pub use safety::{
    // Arithmetic operations
    safe_add,
    safe_sub,
    safe_mul,
    safe_div,
    ArithmeticError,
    // Type conversions
    to_usize,
    to_i64,
    to_u64,
    to_i32,
    to_u32,
    ConversionError,
    // Array indexing
    safe_index,
    safe_index_mut,
    safe_index_signed,
    safe_index_mut_signed,
    IndexError,
    // Mutex operations
    safe_lock,
    try_lock,
    // String operations
    safe_char_at,
    safe_substring,
    safe_str_from_bytes,
    StringError,
};

#[macro_use]
pub mod safety_macros;
