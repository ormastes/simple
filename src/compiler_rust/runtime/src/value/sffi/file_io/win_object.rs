//! Kernel object identity for the Windows service-logon namespace owner.
//!
//! Rust twin of `rt_win_compare_object_handles` in `src/runtime/runtime_native.c`.
//! `CompareObjectHandles` lives only in kernelbase.dll, so it is resolved at run
//! time; when the entry point is unavailable (or off Windows) the result is 0
//! ("not identical") so callers fail closed.

#[no_mangle]
pub extern "C" fn rt_win_compare_object_handles(first: i64, second: i64) -> i32 {
    #[cfg(windows)]
    {
        use windows_sys::Win32::System::LibraryLoader::{GetModuleHandleW, GetProcAddress};
        type CompareFn = unsafe extern "system" fn(isize, isize) -> i32;
        let name: Vec<u16> = "kernelbase.dll\0".encode_utf16().collect();
        let module = unsafe { GetModuleHandleW(name.as_ptr()) };
        if module.is_null() {
            return 0;
        }
        let Some(sym) = (unsafe { GetProcAddress(module, b"CompareObjectHandles\0".as_ptr()) }) else {
            return 0;
        };
        let compare: CompareFn = unsafe { std::mem::transmute(sym) };
        if unsafe { compare(first as isize, second as isize) } != 0 { 1 } else { 0 }
    }
    #[cfg(not(windows))]
    {
        let _ = (first, second);
        0
    }
}
