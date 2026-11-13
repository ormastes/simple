//! Process-symbol resolvability for JIT imports, shared by the seed JIT
//! (`jit.rs`) and the `rt_cranelift_*` provider (`cranelift_sffi.rs`), which
//! the `simple-compiler-backfill` crate also compiles by `#[path]`. Keep this
//! file free of seed-crate dependencies: only `std`, `libc` and `windows-sys`.

#[cfg(not(windows))]
pub(crate) fn dlsym_resolves(name: &str) -> bool {
    let Ok(c_name) = std::ffi::CString::new(name) else {
        return false;
    };
    // SAFETY: `dlsym(RTLD_DEFAULT, ..)` with a valid C string; this is the same
    // call cranelift-jit's `lookup_with_dlsym` makes to resolve the symbol.
    let sym = unsafe { libc::dlsym(libc::RTLD_DEFAULT, c_name.as_ptr()) };
    !sym.is_null()
}

#[cfg(windows)]
pub(crate) fn dlsym_resolves(name: &str) -> bool {
    // Mirror cranelift-jit's own Windows fallback resolver exactly
    // (vendor `cranelift-jit-0.116.1/src/backend.rs::lookup_with_dlsym`):
    // `GetProcAddress` against the running executable image, then against
    // `ucrtbase.dll`. Blindly returning `true` here (the previous behaviour)
    // meant `unresolved_imports_called` could never detect an
    // unresolvable cross-module Simple symbol on Windows: cranelift-jit
    // itself would fail the SAME lookup, bind the GOT slot to NULL, and the
    // first call through it SIGSEGVs with nothing on stderr — this is the
    // root cause of `seed_jit_app_module_function_call_segfaults_windows_2026-09-13.md`
    // and `seed_jit_function_local_use_segfaults_2026-09-13.md`: both
    // repros reach a cross-module Simple function symbol that resolves to
    // neither a registered runtime symbol nor a process/CRT export, so the
    // guard must say `false` and let `compile_module` de-JIT to the
    // interpreter instead of finalizing a NULL import.
    use windows_sys::Win32::Foundation::HMODULE;
    use windows_sys::Win32::System::LibraryLoader;

    let Ok(c_name) = std::ffi::CString::new(name) else {
        return false;
    };
    let c_name_ptr = c_name.as_ptr();

    unsafe {
        let handles: [*mut core::ffi::c_void; 2] = [
            // The running executable image itself.
            std::ptr::null_mut(),
            // The local C runtime, exactly as cranelift-jit tries it.
            LibraryLoader::GetModuleHandleA(b"ucrtbase.dll\0".as_ptr()) as *mut core::ffi::c_void,
        ];
        for handle in &handles {
            if LibraryLoader::GetProcAddress(*handle as HMODULE, c_name_ptr.cast()).is_some() {
                return true;
            }
        }
    }
    false
}
