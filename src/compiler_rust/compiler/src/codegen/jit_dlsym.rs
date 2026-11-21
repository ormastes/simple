//! Process-symbol resolvability for JIT imports, shared by the seed JIT
//! (`jit.rs`) and the `rt_cranelift_*` provider (`cranelift_sffi.rs`), which
//! the `simple-compiler-backfill` crate also compiles by `#[path]`. Keep this
//! file free of seed-crate dependencies: only `std`, `libc` and `windows-sys`.

#[cfg(not(windows))]
pub(crate) fn dlsym_lookup(name: &str) -> Option<*const u8> {
    let Ok(c_name) = std::ffi::CString::new(name) else {
        return None;
    };
    // SAFETY: `dlsym(RTLD_DEFAULT, ..)` with a valid C string; this is the same
    // call cranelift-jit's `lookup_with_dlsym` makes to resolve the symbol.
    let sym = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_name.as_ptr()) };
    if sym.is_null() {
        None
    } else {
        Some(sym as *const u8)
    }
}

#[cfg(not(windows))]
pub(crate) fn dlsym_resolves(name: &str) -> bool {
    dlsym_lookup(name).is_some()
}

#[cfg(windows)]
fn cached_windows_module_handles() -> &'static [usize] {
    use std::sync::OnceLock;
    use windows_sys::Win32::System::LibraryLoader;

    static HANDLES: OnceLock<Vec<usize>> = OnceLock::new();
    HANDLES.get_or_init(|| {
        let mut out = vec![0usize];
        for dll in [
            b"ucrtbase.dll\0".as_slice(),
            b"kernel32.dll\0".as_slice(),
            b"advapi32.dll\0".as_slice(),
            b"bcrypt.dll\0".as_slice(),
            b"ntdll.dll\0".as_slice(),
            b"secur32.dll\0".as_slice(),
            b"shell32.dll\0".as_slice(),
            b"ole32.dll\0".as_slice(),
        ] {
            let mut handle = unsafe { LibraryLoader::GetModuleHandleA(dll.as_ptr()) };
            if handle.is_null() {
                handle = unsafe { LibraryLoader::LoadLibraryA(dll.as_ptr()) };
            }
            if !handle.is_null() {
                out.push(handle as usize);
            }
        }
        out
    })
}

#[cfg(windows)]
pub(crate) fn dlsym_lookup(name: &str) -> Option<*const u8> {
    // Mirror cranelift-jit's own Windows fallback resolver
    // (`GetProcAddress` against the running executable image, then `ucrtbase.dll`),
    // plus Win32 system DLLs referenced by direct Windows SFFI declarations
    // (`kernel32.dll`, `advapi32.dll`, `bcrypt.dll`, `ntdll.dll`, `secur32.dll`,
    // `shell32.dll`, `ole32.dll`). Nonexistent symbols still return `None` so
    // `unresolved_imports_called` refuses unresolvable cross-module imports cleanly.
    use windows_sys::Win32::Foundation::HMODULE;
    use windows_sys::Win32::System::LibraryLoader;

    let Ok(c_name) = std::ffi::CString::new(name) else {
        return None;
    };
    let c_name_ptr = c_name.as_ptr();

    unsafe {
        for &handle in cached_windows_module_handles() {
            if let Some(addr) = LibraryLoader::GetProcAddress(handle as HMODULE, c_name_ptr.cast()) {
                return Some(addr as *const u8);
            }
        }
    }
    None
}

#[cfg(windows)]
pub(crate) fn dlsym_resolves(name: &str) -> bool {
    dlsym_lookup(name).is_some()
}
