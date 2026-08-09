use std::path::PathBuf;

use simple_native_loader::{LoadError, ModuleLoader};

type AddFn = unsafe extern "C" fn(i64, i64) -> i64;
type StrlenFn = unsafe extern "C" fn(*const libc::c_char) -> i64;

/// Safe wrapper around the native terminal library built in this crate.
pub struct TermNative {
    module: simple_native_loader::LoadedModule,
}

impl TermNative {
    /// Load the bundled native library.
    pub fn load() -> Result<Self, LoadError> {
        let path = PathBuf::from(env!("TERM_NATIVE_LIB"));
        let module = ModuleLoader::new().load(&path)?;
        Ok(Self { module })
    }

    pub fn add(&self, a: i64, b: i64) -> Option<i64> {
        let func: AddFn = self.module.get_function("term_add")?;
        Some(unsafe { func(a, b) })
    }

    pub fn strlen(&self, s: &str) -> Option<i64> {
        let func: StrlenFn = self.module.get_function("term_strlen")?;
        let cstr = std::ffi::CString::new(s).ok()?;
        Some(unsafe { func(cstr.as_ptr()) })
    }
}
