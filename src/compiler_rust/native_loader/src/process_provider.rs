//! Current-process symbol provider.
//!
//! Resolves runtime symbols from the already-running `simple` process image.
//! This avoids split-brain runtime state and gives SMF/JIT code access to the
//! same exported symbols the host executable was linked with.

use simple_runtime_abi::{AbiVersion, RUNTIME_SYMBOL_NAMES, RuntimeSymbolProvider};
use std::cell::RefCell;
use std::collections::HashMap;

#[cfg(unix)]
type ProcessHandle = *mut libc::c_void;
#[cfg(windows)]
type ProcessHandle = windows_sys::Win32::Foundation::HMODULE;

pub struct ProcessSymbolProvider {
    handle: ProcessHandle,
    cache: RefCell<HashMap<String, *const u8>>,
}

unsafe impl Send for ProcessSymbolProvider {}
unsafe impl Sync for ProcessSymbolProvider {}

impl ProcessSymbolProvider {
    pub fn new() -> Result<Self, String> {
        let handle = current_process_handle()?;
        Ok(Self {
            handle,
            cache: RefCell::new(HashMap::new()),
        })
    }
}

impl RuntimeSymbolProvider for ProcessSymbolProvider {
    fn get_symbol(&self, name: &str) -> Option<*const u8> {
        // Exact name first: real libc symbols such as `__errno_location`
        // begin with `_`. The ABI-underscore-stripped spelling (Mach-O
        // `_name` for `name`) is only a fallback.
        let stripped = name.strip_prefix('_');
        for candidate in std::iter::once(name).chain(stripped) {
            if let Some(&ptr) = self.cache.borrow().get(candidate) {
                return Some(ptr);
            }
            if let Some(ptr) = lookup_symbol(self.handle, candidate) {
                self.cache.borrow_mut().insert(candidate.to_string(), ptr);
                return Some(ptr);
            }
        }
        None
    }

    fn symbols(&self) -> &[&'static str] {
        RUNTIME_SYMBOL_NAMES
    }

    fn abi_version(&self) -> AbiVersion {
        AbiVersion::CURRENT
    }

    fn name(&self) -> &str {
        "process"
    }
}

#[cfg(unix)]
fn current_process_handle() -> Result<ProcessHandle, String> {
    let handle = unsafe { libc::dlopen(std::ptr::null(), libc::RTLD_NOW | libc::RTLD_GLOBAL) };
    if handle.is_null() {
        let error = unsafe {
            let err = libc::dlerror();
            if err.is_null() {
                "Unknown error".to_string()
            } else {
                std::ffi::CStr::from_ptr(err).to_string_lossy().into_owned()
            }
        };
        Err(format!("failed to open current process: {}", error))
    } else {
        Ok(handle)
    }
}

#[cfg(windows)]
fn current_process_handle() -> Result<ProcessHandle, String> {
    let handle = unsafe { windows_sys::Win32::System::LibraryLoader::GetModuleHandleW(std::ptr::null()) };
    if handle.is_null() {
        Err("failed to get current process module handle".to_string())
    } else {
        Ok(handle)
    }
}

#[cfg(unix)]
fn lookup_symbol(handle: ProcessHandle, name: &str) -> Option<*const u8> {
    let c_name = std::ffi::CString::new(name).ok()?;
    let sym = unsafe { libc::dlsym(handle, c_name.as_ptr()) };
    if sym.is_null() {
        None
    } else {
        Some(sym as *const u8)
    }
}

#[cfg(windows)]
fn lookup_symbol(handle: ProcessHandle, name: &str) -> Option<*const u8> {
    let c_name = std::ffi::CString::new(name).ok()?;
    let sym =
        unsafe { windows_sys::Win32::System::LibraryLoader::GetProcAddress(handle, c_name.as_ptr() as *const u8) };
    match sym {
        Some(f) => Some(f as *const () as *const u8),
        None => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A libc symbol whose real name begins with `_` must resolve by its exact
    // name. Stripping the Mach-O ABI underscore first turned
    // `__errno_location` into `_errno_location`, which glibc does not export,
    // so the JIT spliced the call into the interpreter and the run died with
    // "extern `__errno_location` ... backed by no implementation"
    // (test_coverage_wrapper_native_build_refused_by_scv_admission_2026_10_19).
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    #[test]
    fn exact_leading_underscore_libc_name_resolves() {
        let provider = ProcessSymbolProvider::new().expect("process handle");
        assert!(provider.get_symbol("__errno_location").is_some());
    }

    #[cfg(unix)]
    #[test]
    fn abi_underscore_spelling_still_resolves() {
        let provider = ProcessSymbolProvider::new().expect("process handle");
        assert!(provider.get_symbol("malloc").is_some());
        assert!(provider.get_symbol("_malloc").is_some());
    }

    #[cfg(unix)]
    #[test]
    fn unknown_symbol_is_none() {
        let provider = ProcessSymbolProvider::new().expect("process handle");
        assert!(provider.get_symbol("simple_no_such_symbol_zzqq").is_none());
    }
}
