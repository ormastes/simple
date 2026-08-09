use std::path::PathBuf;

use libloading::Library;

use crate::loader::load_symbol;
use simple_common::DynModule;

/// Loaded native module
pub struct LoadedModule {
    pub path: PathBuf,
    lib: Library,
    pub version: u32,
}

impl LoadedModule {
    pub(crate) fn new(path: PathBuf, lib: Library) -> Self {
        Self { path, lib, version: 1 }
    }

    /// Get function pointer by name
    pub fn get_function<F>(&self, name: &str) -> Option<F>
    where
        F: Copy,
    {
        load_symbol(&self.lib, name).ok()
    }

    /// Get entry point; by convention uses `main` symbol
    pub fn entry_point<F>(&self) -> Option<F>
    where
        F: Copy,
    {
        self.get_function("main")
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
