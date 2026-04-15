//! Current-process symbol provider.
//!
//! Resolves runtime symbols from the already-running `simple` process image.
//! This avoids split-brain runtime state and gives SMF/JIT code access to the
//! same exported symbols the host executable was linked with.

use simple_common::{AbiVersion, RuntimeSymbolProvider, RUNTIME_SYMBOL_NAMES};
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
        let normalized = name.strip_prefix('_').unwrap_or(name);
        if let Some(&ptr) = self.cache.borrow().get(normalized) {
            return Some(ptr);
        }

        let ptr = lookup_symbol(self.handle, normalized)?;
        self.cache.borrow_mut().insert(normalized.to_string(), ptr);
        Some(ptr)
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
