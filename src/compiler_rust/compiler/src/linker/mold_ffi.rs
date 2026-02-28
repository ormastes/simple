//! Mold linker FFI for Simple language.
//!
//! This module provides FFI functions for the Simple linker to detect and
//! use mold, lld, or system ld linkers.
//!
//! # Linker Detection Order
//!
//! 1. Bundled mold (adjacent to Simple executable)
//! 2. System mold (in PATH)
//! 3. LLD (ld.lld in PATH)
//! 4. System ld (in PATH)
//!
//! # License
//!
//! Mold 2.0+ is MIT licensed and can be freely bundled with Simple.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::path::PathBuf;
use std::process::Command;

/// Find the bundled mold binary path.
///
/// Looks for mold in these locations:
/// 1. Same directory as the Simple executable
/// 2. ../bin relative to the executable
/// 3. ../lib/simple relative to the executable
fn get_bundled_mold_path() -> Option<PathBuf> {
    let exe_path = std::env::current_exe().ok()?;
    let exe_dir = exe_path.parent()?;

    // Platform-specific binary name
    #[cfg(target_os = "linux")]
    let mold_name = if cfg!(target_arch = "x86_64") {
        "mold-linux-x86_64"
    } else if cfg!(target_arch = "aarch64") {
        "mold-linux-aarch64"
    } else {
        "mold"
    };

    #[cfg(target_os = "macos")]
    let mold_name = if cfg!(target_arch = "x86_64") {
        "mold-macos-x86_64"
    } else if cfg!(target_arch = "aarch64") {
        "mold-macos-aarch64"
    } else {
        "mold"
    };

    #[cfg(target_os = "freebsd")]
    let mold_name = if cfg!(target_arch = "x86_64") {
        "mold-freebsd-x86_64"
    } else if cfg!(target_arch = "aarch64") {
        "mold-freebsd-aarch64"
    } else {
        "mold"
    };

    #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "freebsd")))]
    let mold_name = "mold";

    // Check locations in order
    let candidates = [
        exe_dir.join(mold_name),
        exe_dir.join("mold"),
        exe_dir.join("../bin/mold"),
        exe_dir.join("../bin").join(mold_name),
        exe_dir.join("../lib/simple/mold"),
        exe_dir.join("../lib/simple").join(mold_name),
    ];

    for candidate in &candidates {
        if candidate.exists() && candidate.is_file() {
            // Verify it's executable
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if let Ok(meta) = candidate.metadata() {
                    if meta.permissions().mode() & 0o111 != 0 {
                        return candidate.canonicalize().ok();
                    }
                }
            }
            #[cfg(not(unix))]
            {
                return candidate.canonicalize().ok();
            }
        }
    }

    None
}

/// Find mold in system PATH.
fn find_in_path(name: &str) -> Option<PathBuf> {
    #[cfg(unix)]
    {
        let output = Command::new("which").arg(name).output().ok()?;

        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout);
            let path = path.trim();
            if !path.is_empty() {
                return Some(PathBuf::from(path));
            }
        }
    }

    #[cfg(windows)]
    {
        let output = Command::new("where").arg(name).output().ok()?;

        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout);
            let path = path.lines().next()?.trim();
            if !path.is_empty() {
                return Some(PathBuf::from(path));
            }
        }
    }

    None
}

/// Convert a PathBuf to a C string for FFI.
fn path_to_c_string(path: PathBuf) -> Option<CString> {
    CString::new(path.to_string_lossy().as_bytes()).ok()
}

// ============================================================================
// FFI Functions (called from Simple)
// ============================================================================

/// Find mold executable path.
///
/// Returns the path to mold if found, or null if not available.
/// Checks bundled mold first, then system PATH.
#[no_mangle]
pub extern "C" fn mold_ffi_find_mold() -> *const c_char {
    // Try bundled mold first
    if let Some(path) = get_bundled_mold_path() {
        if let Some(c_str) = path_to_c_string(path) {
            return c_str.into_raw();
        }
    }

    // Try system mold
    if let Some(path) = find_in_path("mold") {
        if let Some(c_str) = path_to_c_string(path) {
            return c_str.into_raw();
        }
    }

    std::ptr::null()
}

/// Find lld executable path.
///
/// Returns the path to ld.lld if found, or null if not available.
#[no_mangle]
pub extern "C" fn mold_ffi_find_lld() -> *const c_char {
    // Try ld.lld first (common on Linux)
    if let Some(path) = find_in_path("ld.lld") {
        if let Some(c_str) = path_to_c_string(path) {
            return c_str.into_raw();
        }
    }

    // Try lld (sometimes installed as just 'lld')
    if let Some(path) = find_in_path("lld") {
        if let Some(c_str) = path_to_c_string(path) {
            return c_str.into_raw();
        }
    }

    // On Windows, try lld-link (MSVC-compatible LLD variant)
    #[cfg(target_os = "windows")]
    if let Some(path) = find_in_path("lld-link") {
        if let Some(c_str) = path_to_c_string(path) {
            return c_str.into_raw();
        }
    }

    std::ptr::null()
}

/// Find system ld executable path.
///
/// Returns the path to ld if found, or null if not available.
#[no_mangle]
pub extern "C" fn mold_ffi_find_ld() -> *const c_char {
    if let Some(path) = find_in_path("ld") {
        if let Some(c_str) = path_to_c_string(path) {
            return c_str.into_raw();
        }
    }

    std::ptr::null()
}

/// Execute linker with arguments.
///
/// Returns the exit code, or -1 on execution failure.
///
/// # Safety
///
/// `linker_path` and `args` must be valid null-terminated C strings.
/// `args` is a null-terminated array of C string pointers.
#[no_mangle]
pub unsafe extern "C" fn mold_ffi_execute(
    linker_path: *const c_char,
    args: *const *const c_char,
    args_len: usize,
) -> i32 {
    if linker_path.is_null() {
        return -1;
    }

    let linker = match CStr::from_ptr(linker_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let mut cmd = Command::new(linker);

    // Add arguments
    if !args.is_null() {
        for i in 0..args_len {
            let arg_ptr = *args.add(i);
            if arg_ptr.is_null() {
                break;
            }
            if let Ok(arg) = CStr::from_ptr(arg_ptr).to_str() {
                cmd.arg(arg);
            }
        }
    }

    match cmd.status() {
        Ok(status) => status.code().unwrap_or(-1),
        Err(_) => -1,
    }
}

/// Write code as an ELF object file.
///
/// # Safety
///
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn mold_ffi_write_elf_object(
    code: *const u8,
    code_len: usize,
    name: *const c_char,
    output_path: *const c_char,
) -> i32 {
    if code.is_null() || name.is_null() || output_path.is_null() {
        return -1;
    }

    let output = match CStr::from_ptr(output_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let code_slice = std::slice::from_raw_parts(code, code_len);

    // For now, just write the raw bytes
    // TODO: Properly wrap in ELF object format if not already
    match std::fs::write(output, code_slice) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Get file size in bytes.
///
/// Returns -1 if the file doesn't exist or can't be accessed.
///
/// # Safety
///
/// `path` must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn mold_ffi_get_file_size(path: *const c_char) -> i64 {
    if path.is_null() {
        return -1;
    }

    let path_str = match CStr::from_ptr(path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match std::fs::metadata(path_str) {
        Ok(meta) => meta.len() as i64,
        Err(_) => -1,
    }
}

/// Free a C string allocated by this module.
///
/// # Safety
///
/// `ptr` must have been returned by one of the find functions in this module.
#[no_mangle]
pub unsafe extern "C" fn mold_ffi_free_string(ptr: *mut c_char) {
    if !ptr.is_null() {
        drop(CString::from_raw(ptr));
    }
}

/// Create a temporary directory.
///
/// Returns the path to the temporary directory, or null on failure.
/// The caller is responsible for cleaning up the directory.
#[no_mangle]
pub extern "C" fn mold_ffi_create_temp_dir() -> *const c_char {
    match tempfile::tempdir() {
        Ok(dir) => {
            // We need to keep the TempDir to prevent it from being cleaned up
            // when this function returns. The caller is responsible for cleanup.
            let path = dir.keep();
            if let Some(c_str) = path_to_c_string(path) {
                return c_str.into_raw();
            }
            std::ptr::null()
        }
        Err(_) => std::ptr::null(),
    }
}

/// Remove a directory and its contents.
///
/// # Safety
///
/// `path` must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn mold_ffi_cleanup_temp_dir(path: *const c_char) -> i32 {
    if path.is_null() {
        return -1;
    }

    let path_str = match CStr::from_ptr(path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match std::fs::remove_dir_all(path_str) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

// ============================================================================
// Rust API (for internal use)
// ============================================================================

/// Linker type enumeration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkerType {
    Mold,
    Lld,
    Ld,
}

impl LinkerType {
    pub fn as_str(&self) -> &'static str {
        match self {
            LinkerType::Mold => "mold",
            LinkerType::Lld => "lld",
            LinkerType::Ld => "ld",
        }
    }
}

/// Find the best available linker.
///
/// Returns the path and type of the linker, or an error if none found.
pub fn find_linker() -> Result<(PathBuf, LinkerType), &'static str> {
    // Try mold first (bundled then system)
    if let Some(path) = get_bundled_mold_path() {
        return Ok((path, LinkerType::Mold));
    }
    if let Some(path) = find_in_path("mold") {
        return Ok((path, LinkerType::Mold));
    }

    // Try lld
    if let Some(path) = find_in_path("ld.lld") {
        return Ok((path, LinkerType::Lld));
    }
    if let Some(path) = find_in_path("lld") {
        return Ok((path, LinkerType::Lld));
    }

    // Try system ld
    if let Some(path) = find_in_path("ld") {
        return Ok((path, LinkerType::Ld));
    }

    Err("No linker found. Please install mold, lld, or ensure ld is in PATH.")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_linker() {
        // Should find at least system ld on most Unix systems
        let result = find_linker();
        // Don't assert success - depends on system configuration
        if let Ok((path, linker_type)) = result {
            println!("Found linker: {:?} at {:?}", linker_type, path);
        }
    }

    #[test]
    fn test_find_in_path() {
        // ld should exist on most Unix systems
        #[cfg(unix)]
        {
            let result = find_in_path("ls");
            assert!(result.is_some(), "ls should be in PATH");
        }
    }
}
