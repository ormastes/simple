use std::path::Path;

pub mod config_env;
pub use config_env::ConfigEnv;

pub mod manual;
pub use manual::{Handle, HandlePool, ManualGc, Shared, Unique, WeakPtr};

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

pub mod gc;
