use std::ffi::CString;
use std::path::Path;

use libloading::Library;
use thiserror::Error;

use simple_common::DynLoader;

use crate::module::LoadedModule;

/// Loader for native dynamic libraries (.so/.dylib/.dll)
pub struct ModuleLoader;

impl ModuleLoader {
    pub fn new() -> Self {
        Self
    }

    pub fn load(&self, path: &Path) -> Result<LoadedModule, LoadError> {
        self.load_with_resolver(path, |_name| None)
    }

    /// Load a native library with a resolver compatible signature (unused for native libs).
    pub fn load_with_resolver<F>(
        &self,
        path: &Path,
        _resolver: F,
    ) -> Result<LoadedModule, LoadError>
    where
        F: Fn(&str) -> Option<usize>,
    {
        let lib = unsafe { Library::new(path) }.map_err(LoadError::Dl)?;
        Ok(LoadedModule::new(path.to_path_buf(), lib))
    }
}

impl Default for ModuleLoader {
    fn default() -> Self {
        Self::new()
    }
}

impl DynLoader for ModuleLoader {
    type Module = LoadedModule;
    type Error = LoadError;

    fn load(&self, path: &Path) -> Result<Self::Module, Self::Error> {
        ModuleLoader::load(self, path)
    }

    fn load_with_resolver<F>(&self, path: &Path, resolver: F) -> Result<Self::Module, Self::Error>
    where
        F: Fn(&str) -> Option<usize>,
    {
        ModuleLoader::load_with_resolver(self, path, resolver)
    }
}

#[derive(Debug, Error)]
pub enum LoadError {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("dlopen error: {0}")]
    Dl(#[from] libloading::Error),
    #[error("invalid symbol name: {0}")]
    InvalidSymbolName(String),
}

fn to_cstring(name: &str) -> Result<CString, LoadError> {
    CString::new(name.as_bytes()).map_err(|_| LoadError::InvalidSymbolName(name.to_string()))
}

pub(crate) fn load_symbol<F>(lib: &Library, name: &str) -> Result<F, LoadError>
where
    F: Copy,
{
    let cstr = to_cstring(name)?;
    unsafe {
        let sym: libloading::Symbol<F> = lib.get(cstr.as_bytes_with_nul())?;
        Ok(*sym)
    }
}
