use std::sync::Arc;

use super::loader::ModuleLoader;
use super::module::LoadedModule;
use super::smf::SymbolBinding;

/// SMF module registry - type alias with extension methods for symbol resolution
pub type ModuleRegistryBase = simple_common::ModuleRegistry<ModuleLoader>;

/// Global module registry for tracking loaded SMF modules.
/// Extends the generic registry with symbol resolution across modules.
pub struct ModuleRegistry {
    inner: ModuleRegistryBase,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self {
            inner: ModuleRegistryBase::new(ModuleLoader::new()),
        }
    }

    /// Load or get cached module with cross-module symbol resolution
    pub fn load(&self, path: &std::path::Path) -> Result<Arc<LoadedModule>, super::loader::LoadError> {
        self.inner.load_with_resolver(path, |name| self.resolve_symbol(name))
    }

    /// Unload a module
    pub fn unload(&self, path: &std::path::Path) -> bool {
        self.inner.unload(path)
    }

    /// Reload a module (for hot reload)
    pub fn reload(&self, path: &std::path::Path) -> Result<Arc<LoadedModule>, super::loader::LoadError> {
        self.inner.reload_with_resolver(path, |name| self.resolve_symbol(name))
    }

    /// Resolve symbol across all loaded modules
    pub fn resolve_symbol(&self, name: &str) -> Option<usize> {
        for module in self.inner.modules() {
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

impl Default for ModuleRegistry {
    fn default() -> Self {
        Self::new()
    }
}
