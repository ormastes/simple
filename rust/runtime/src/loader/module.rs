use std::path::PathBuf;

use super::memory::ExecutableMemory;
use super::smf::*;
use simple_common::DynModule;

/// A loaded Simple module
pub struct LoadedModule {
    pub path: PathBuf,
    pub header: SmfHeader,
    pub code_mem: ExecutableMemory,
    pub data_mem: Option<ExecutableMemory>,
    pub symbols: SymbolTable,
    pub version: u32,
}

impl LoadedModule {
    /// Get function pointer by name
    pub fn get_function<F>(&self, name: &str) -> Option<F> {
        let sym = self.symbols.lookup(name)?;

        if sym.sym_type != SymbolType::Function {
            return None;
        }

        Some(unsafe { self.code_mem.get_fn(sym.value as usize) })
    }

    /// Get entry point (for executables)
    pub fn entry_point<F>(&self) -> Option<F> {
        if !self.header.is_executable() {
            return None;
        }

        Some(unsafe { self.code_mem.get_fn(self.header.entry_point as usize) })
    }

    /// Check if module supports hot reload
    pub fn is_reloadable(&self) -> bool {
        self.header.is_reloadable()
    }

    /// Get module source hash (for rebuild detection)
    pub fn source_hash(&self) -> u64 {
        self.header.source_hash
    }

    /// List all exported symbols
    pub fn exports(&self) -> Vec<(&str, SymbolType)> {
        self.symbols
            .exports()
            .map(|s| (self.symbols.symbol_name(s), s.sym_type))
            .collect()
    }
}

impl DynModule for LoadedModule {
    fn get_fn<F: Copy>(&self, name: &str) -> Option<F> {
        self.get_function(name)
    }

    fn entry_fn<F: Copy>(&self) -> Option<F> {
        self.entry_point()
    }
}
