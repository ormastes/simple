//! Cross-platform dynamic-library open/lookup, shared by every satellite
//! loader in this directory (SDL2, SDL3, GLFW, torch, Vulkan).
//!
//! Each of those files used to call `libc::dlopen`/`libc::dlsym` directly
//! and unconditionally. `libc` is a `cfg(unix)`-only dependency of this
//! crate (see `Cargo.toml`'s `[target.'cfg(unix)'.dependencies]`), so on
//! Windows every one of those references failed to even LINK — "unresolved
//! module or unlinked crate `libc`" — rather than failing at runtime for a
//! missing library, which is what the code actually intended to handle.
//! Found blocking the whole Rust seed build 2026-08-09 (`sdl2.rs`), then
//! the identical pattern in four more files once the first was fixed.
//!
//! `interpreter_extern/gpu.rs`'s `load_symbol`/`load_opencl` already carried
//! a correct `#[cfg(unix)]`/`#[cfg(windows)]` split using
//! `windows_sys::Win32::System::LibraryLoader::{LoadLibraryA, GetProcAddress}`
//! — this module extracts that same pattern into one shared, tested helper
//! instead of re-deriving it five more times.
//!
//! Semantics preserved from the original `libc::dlopen(path, RTLD_LAZY |
//! RTLD_LOCAL)` call sites: lazy binding (an unresolved symbol in the
//! library is fine as long as nothing calls it), library-local symbol
//! visibility. Windows' `LoadLibraryA` has no lazy/eager distinction (PE
//! imports always resolve at load time) and no visibility flag to set, so
//! `dlopen_compat` on Windows is just the `LoadLibraryA` call.

use std::ffi::{c_void, CString};

/// Open a dynamic library by path (POSIX) or by name/relative-path search
/// (Windows — matches `LoadLibraryA`'s own DLL search order). Returns `None`
/// if the path is not representable as a `CString` (embedded NUL) or the
/// load fails.
pub fn dlopen_compat(path: &str) -> Option<*mut c_void> {
    let c_path = CString::new(path).ok()?;
    #[cfg(unix)]
    {
        let handle = unsafe { libc::dlopen(c_path.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL) };
        if handle.is_null() {
            None
        } else {
            Some(handle)
        }
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::System::LibraryLoader::LoadLibraryA;
        let handle = unsafe { LoadLibraryA(c_path.as_ptr() as *const u8) };
        if handle.is_null() {
            None
        } else {
            Some(handle as *mut c_void)
        }
    }
}

/// Resolve a symbol already linked into the CURRENT process (no library
/// handle involved) — the POSIX idiom is `dlsym(RTLD_DEFAULT, name)`, used
/// when the caller's own binary was statically linked against the symbol's
/// providing library (see `vulkan.rs`, which looks up its own
/// `rt_vulkan_*` runtime symbols this way rather than dlopen-ing anything).
/// Windows has no direct `RTLD_DEFAULT` equivalent, but `GetModuleHandleA`
/// with a null module name returns a handle to the running executable
/// itself, which `GetProcAddress` can then search — the same "look in what
/// is already loaded, starting with me" semantic.
pub fn dlsym_self_compat(name: &str) -> Option<*mut c_void> {
    let c_name = CString::new(name).ok()?;
    #[cfg(unix)]
    {
        let addr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_name.as_ptr()) };
        if addr.is_null() {
            None
        } else {
            Some(addr)
        }
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::System::LibraryLoader::{GetModuleHandleA, GetProcAddress};
        let module = unsafe { GetModuleHandleA(std::ptr::null()) };
        if module.is_null() {
            return None;
        }
        let addr = unsafe { GetProcAddress(module, c_name.as_ptr() as *const u8) };
        addr.map(|f| f as *mut c_void)
    }
}

/// Resolve a symbol in a library previously opened by [`dlopen_compat`].
/// Returns `None` for an unresolved name or a `name` not representable as a
/// `CString` (embedded NUL).
pub fn dlsym_compat(handle: *mut c_void, name: &str) -> Option<*mut c_void> {
    let c_name = CString::new(name).ok()?;
    #[cfg(unix)]
    {
        let addr = unsafe { libc::dlsym(handle, c_name.as_ptr()) };
        if addr.is_null() {
            None
        } else {
            Some(addr)
        }
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::System::LibraryLoader::GetProcAddress;
        let addr = unsafe { GetProcAddress(handle as _, c_name.as_ptr() as *const u8) };
        addr.map(|f| f as *mut c_void)
    }
}
