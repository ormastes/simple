//! Directory Operations
//!
//! This module provides directory operations including:
//! - Create: Create directories (with optional recursive creation)
//! - CreateAll: Create directories recursively
//! - List: List directory entries
//! - Remove: Remove directories (with optional recursive removal)
//! - RemoveAll: Remove directories recursively with safety checks
//! - Find: Find files matching patterns (with optional recursion)
//! - Glob: List files matching glob patterns
//! - Walk: Walk directory tree recursively
//! - CurrentDir: Get/set current working directory

use crate::value::collections::{rt_array_new, rt_array_push, rt_string_new};
use crate::value::RuntimeValue;
use std::path::Path;

/// Create directory (with optional recursive creation)
#[no_mangle]
pub unsafe extern "C" fn rt_dir_create(path_ptr: *const u8, path_len: u64, recursive: bool) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    if recursive {
        std::fs::create_dir_all(path_str).is_ok()
    } else {
        std::fs::create_dir(path_str).is_ok()
    }
}

/// List directory entries
#[no_mangle]
pub unsafe extern "C" fn rt_dir_list(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    if path_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::fs::read_dir(path_str) {
        Ok(entries) => {
            // Collect entry names first to know the count
            let names: Vec<String> = entries
                .flatten()
                .filter_map(|entry| entry.file_name().into_string().ok())
                .collect();

            // Create array with correct capacity
            let array_handle = rt_array_new(names.len() as u64);

            for name in names {
                let bytes = name.as_bytes();
                let str_value = rt_string_new(bytes.as_ptr(), bytes.len() as u64);
                rt_array_push(array_handle, str_value);
            }

            array_handle
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Remove a directory
#[no_mangle]
pub unsafe extern "C" fn rt_dir_remove(path_ptr: *const u8, path_len: u64, recursive: bool) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    if recursive {
        std::fs::remove_dir_all(path_str).is_ok()
    } else {
        std::fs::remove_dir(path_str).is_ok()
    }
}

/// Find files matching pattern (simplified glob matching)
/// Returns List[String] of matching file paths
#[no_mangle]
pub unsafe extern "C" fn rt_file_find(
    dir_ptr: *const u8,
    dir_len: u64,
    pattern_ptr: *const u8,
    pattern_len: u64,
    recursive: bool,
) -> RuntimeValue {
    use std::fs;

    // Helper to check if filename matches simple glob pattern
    fn matches_pattern(filename: &str, pattern: &str) -> bool {
        // Handle simple patterns: "*", "*.ext", "prefix*", "*suffix"
        if pattern == "*" {
            return true;
        }

        if let Some(ext) = pattern.strip_prefix("*.") {
            return filename.ends_with(&format!(".{}", ext));
        }

        if let Some(prefix) = pattern.strip_suffix('*') {
            return filename.starts_with(prefix);
        }

        if let Some(suffix) = pattern.strip_prefix('*') {
            return filename.ends_with(suffix);
        }

        // Exact match
        filename == pattern
    }

    if dir_ptr.is_null() || pattern_ptr.is_null() {
        return rt_array_new(0);
    }

    let dir_bytes = std::slice::from_raw_parts(dir_ptr, dir_len as usize);
    let dir_str = match std::str::from_utf8(dir_bytes) {
        Ok(s) => s,
        Err(_) => return rt_array_new(0),
    };

    let pattern_bytes = std::slice::from_raw_parts(pattern_ptr, pattern_len as usize);
    let pattern_str = match std::str::from_utf8(pattern_bytes) {
        Ok(s) => s,
        Err(_) => return rt_array_new(0),
    };

    let dir_path = Path::new(dir_str);
    let mut results = Vec::new();

    // Non-recursive: just list immediate directory entries
    if !recursive {
        if let Ok(entries) = fs::read_dir(dir_path) {
            for entry in entries.flatten() {
                if let Some(filename) = entry.file_name().to_str() {
                    if matches_pattern(filename, pattern_str) {
                        if let Some(path_str) = entry.path().to_str() {
                            results.push(path_str.to_string());
                        }
                    }
                }
            }
        }
    } else {
        // Recursive: walk directory tree
        fn walk_dir(dir: &Path, pattern: &str, results: &mut Vec<String>) {
            if let Ok(entries) = fs::read_dir(dir) {
                for entry in entries.flatten() {
                    let path = entry.path();

                    if path.is_file() {
                        if let Some(filename) = entry.file_name().to_str() {
                            if matches_pattern(filename, pattern) {
                                if let Some(path_str) = path.to_str() {
                                    results.push(path_str.to_string());
                                }
                            }
                        }
                    } else if path.is_dir() {
                        walk_dir(&path, pattern, results);
                    }
                }
            }
        }

        walk_dir(dir_path, pattern_str, &mut results);
    }

    // Create array with results
    let arr = rt_array_new(results.len() as u64);
    for path in results {
        let path_val = rt_string_new(path.as_ptr(), path.len() as u64);
        rt_array_push(arr, path_val);
    }

    arr
}

/// List files matching glob pattern in directory
/// Returns List[String] of matching file paths
#[no_mangle]
pub unsafe extern "C" fn rt_dir_glob(
    dir_ptr: *const u8,
    dir_len: u64,
    pattern_ptr: *const u8,
    pattern_len: u64,
) -> RuntimeValue {
    // For now, implement glob as non-recursive find
    rt_file_find(dir_ptr, dir_len, pattern_ptr, pattern_len, false)
}

/// Create directory with all parent directories
/// Equivalent to mkdir -p
#[no_mangle]
pub unsafe extern "C" fn rt_dir_create_all(path_ptr: *const u8, path_len: u64) -> bool {
    rt_dir_create(path_ptr, path_len, true)
}

/// Walk directory recursively, returning all files and directories
/// Returns List[String] of all paths found
#[no_mangle]
pub unsafe extern "C" fn rt_dir_walk(path_ptr: *const u8, path_len: u64) -> RuntimeValue {
    use std::fs;

    if path_ptr.is_null() {
        return rt_array_new(0);
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return rt_array_new(0),
    };

    let dir_path = Path::new(path_str);
    let mut results = Vec::new();

    fn walk_recursive(dir: &Path, results: &mut Vec<String>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();

                if let Some(path_str) = path.to_str() {
                    results.push(path_str.to_string());
                }

                if path.is_dir() {
                    walk_recursive(&path, results);
                }
            }
        }
    }

    walk_recursive(dir_path, &mut results);

    let arr = rt_array_new(results.len() as u64);
    for path in results {
        let path_val = rt_string_new(path.as_ptr(), path.len() as u64);
        rt_array_push(arr, path_val);
    }

    arr
}

/// Get current working directory
#[no_mangle]
pub extern "C" fn rt_current_dir() -> RuntimeValue {
    match std::env::current_dir() {
        Ok(path) => {
            let path_str = path.to_string_lossy();
            let bytes = path_str.as_bytes();
            unsafe { rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Set current working directory
#[no_mangle]
pub unsafe extern "C" fn rt_set_current_dir(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::env::set_current_dir(path_str).is_ok()
}

/// Protected paths that should never be removed
const PROTECTED_PATHS: &[&str] = &[
    "/",
    "/home",
    "/usr",
    "/bin",
    "/sbin",
    "/etc",
    "/var",
    "/tmp",
    "/opt",
    "/lib",
    "/lib64",
    "/boot",
    "/dev",
    "/proc",
    "/sys",
    "/root",
];

/// Check if a path is protected and should not be removed
fn is_protected_path(path: &Path) -> bool {
    // Check path components - reject if too short
    let components: Vec<_> = path.components().collect();
    if components.len() <= 2 {
        // Path like "/" or "/home" - too dangerous
        return true;
    }

    // Check against blocklist
    let path_str = path.to_string_lossy();
    for protected in PROTECTED_PATHS {
        if path_str.as_ref() == *protected {
            return true;
        }
    }

    // Check if it's user's home directory
    if let Some(home) = std::env::var_os("HOME") {
        let home_path = Path::new(&home);
        if path == home_path {
            return true;
        }
    }

    false
}

/// Remove directory and all contents recursively with safety checks
/// Refuses to remove protected system directories
#[no_mangle]
pub unsafe extern "C" fn rt_dir_remove_all(path_ptr: *const u8, path_len: u64) -> bool {
    if path_ptr.is_null() {
        return false;
    }

    let path_bytes = std::slice::from_raw_parts(path_ptr, path_len as usize);
    let path_str = match std::str::from_utf8(path_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let path = Path::new(path_str);

    // Canonicalize path to resolve symlinks and get absolute path
    let canonical = match path.canonicalize() {
        Ok(p) => p,
        Err(_) => return false, // Path doesn't exist or can't be resolved
    };

    // Safety check: refuse to remove protected paths
    if is_protected_path(&canonical) {
        eprintln!(
            "rt_dir_remove_all: Refusing to remove protected path: {}",
            canonical.display()
        );
        return false;
    }

    // Actually remove the directory
    std::fs::remove_dir_all(&canonical).is_ok()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::rt_array_len;
    use std::fs;
    use tempfile::TempDir;

    // Helper to create string pointer for FFI
    fn str_to_ptr(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn test_dir_create() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("new_dir");
        let path_str = dir_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_dir_create(ptr, len, false));
            assert!(dir_path.exists());
            assert!(dir_path.is_dir());
        }
    }

    #[test]
    fn test_dir_create_recursive() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("a").join("b").join("c");
        let path_str = dir_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_dir_create(ptr, len, true));
            assert!(dir_path.exists());
            assert!(dir_path.is_dir());
        }
    }

    #[test]
    fn test_dir_list() {
        let temp_dir = TempDir::new().unwrap();
        fs::write(temp_dir.path().join("file1.txt"), "").unwrap();
        fs::write(temp_dir.path().join("file2.txt"), "").unwrap();
        fs::create_dir(temp_dir.path().join("subdir")).unwrap();

        let path_str = temp_dir.path().to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let result = rt_dir_list(ptr, len);
            assert!(!result.is_nil());

            let count = rt_array_len(result);
            // Should have 3 entries (file1.txt, file2.txt, subdir)
            // But allow for platform differences in directory listing
            assert!(count >= 3, "Expected at least 3 entries, got {}", count);
        }
    }

    #[test]
    fn test_dir_remove() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("to_remove");
        fs::create_dir(&dir_path).unwrap();

        let path_str = dir_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_dir_remove(ptr, len, false));
            assert!(!dir_path.exists());
        }
    }

    #[test]
    fn test_file_find_non_recursive() {
        let temp_dir = TempDir::new().unwrap();
        fs::write(temp_dir.path().join("test1.txt"), "").unwrap();
        fs::write(temp_dir.path().join("test2.txt"), "").unwrap();
        fs::write(temp_dir.path().join("other.md"), "").unwrap();

        let dir_str = temp_dir.path().to_str().unwrap();
        let (dir_ptr, dir_len) = str_to_ptr(dir_str);
        let (pattern_ptr, pattern_len) = str_to_ptr("*.txt");

        unsafe {
            let result = rt_file_find(dir_ptr, dir_len, pattern_ptr, pattern_len, false);
            let count = rt_array_len(result);
            assert_eq!(count, 2); // test1.txt, test2.txt
        }
    }

    #[test]
    fn test_dir_create_all() {
        let temp_dir = TempDir::new().unwrap();
        let nested_path = temp_dir.path().join("a").join("b").join("c");
        let path_str = nested_path.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_dir_create_all(ptr, len));
            assert!(nested_path.exists());
            assert!(nested_path.is_dir());
        }
    }

    #[test]
    fn test_dir_walk() {
        let temp_dir = TempDir::new().unwrap();

        // Create structure: file1.txt, subdir/file2.txt
        fs::write(temp_dir.path().join("file1.txt"), "").unwrap();
        let subdir = temp_dir.path().join("subdir");
        fs::create_dir(&subdir).unwrap();
        fs::write(subdir.join("file2.txt"), "").unwrap();

        let path_str = temp_dir.path().to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            let result = rt_dir_walk(ptr, len);
            let count = rt_array_len(result);
            // Should find: file1.txt, subdir, subdir/file2.txt
            assert_eq!(count, 3);
        }
    }

    #[test]
    fn test_current_dir() {
        use crate::value::collections::{rt_string_data, rt_string_len};

        unsafe {
            let result = rt_current_dir();
            assert!(!result.is_nil());

            let len = rt_string_len(result);
            let ptr = rt_string_data(result);
            let slice = std::slice::from_raw_parts(ptr, len as usize);
            let cwd = String::from_utf8_lossy(slice).to_string();

            // Should return a non-empty absolute path
            assert!(!cwd.is_empty());
            assert!(cwd.starts_with('/') || cwd.contains(':'));
        }
    }

    #[test]
    fn test_set_current_dir() {
        use crate::value::collections::{rt_string_data, rt_string_len};

        // Save original directory
        let original = std::env::current_dir().unwrap();

        let temp_dir = TempDir::new().unwrap();
        let path_str = temp_dir.path().to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            // Change directory
            assert!(rt_set_current_dir(ptr, len));

            // Verify change
            let result = rt_current_dir();
            let result_len = rt_string_len(result);
            let result_ptr = rt_string_data(result);
            let slice = std::slice::from_raw_parts(result_ptr, result_len as usize);
            let new_cwd = String::from_utf8_lossy(slice).to_string();

            // Canonicalize both paths for comparison
            let expected = temp_dir.path().canonicalize().unwrap();
            let actual = std::path::Path::new(&new_cwd).canonicalize().unwrap();
            assert_eq!(actual, expected);
        }

        // Restore original directory
        std::env::set_current_dir(original).unwrap();
    }

    #[test]
    fn test_dir_remove_all() {
        let temp_dir = TempDir::new().unwrap();

        // Create nested structure
        let to_remove = temp_dir.path().join("to_remove");
        fs::create_dir(&to_remove).unwrap();
        fs::write(to_remove.join("file.txt"), "content").unwrap();
        let subdir = to_remove.join("subdir");
        fs::create_dir(&subdir).unwrap();
        fs::write(subdir.join("nested.txt"), "nested").unwrap();

        let path_str = to_remove.to_str().unwrap();
        let (ptr, len) = str_to_ptr(path_str);

        unsafe {
            assert!(rt_dir_remove_all(ptr, len));
            assert!(!to_remove.exists());
        }
    }

    #[test]
    fn test_dir_remove_all_refuses_protected() {
        // Try to remove root - should fail
        let (ptr, len) = str_to_ptr("/");

        unsafe {
            assert!(!rt_dir_remove_all(ptr, len));
        }
    }

    #[test]
    fn test_is_protected_path() {
        use std::path::Path;

        // Test protected paths
        assert!(super::is_protected_path(Path::new("/")));
        assert!(super::is_protected_path(Path::new("/home")));
        assert!(super::is_protected_path(Path::new("/usr")));

        // Test paths that should not be protected (deep enough)
        assert!(!super::is_protected_path(Path::new("/tmp/test/subdir")));
        assert!(!super::is_protected_path(Path::new("/home/user/project")));
    }
}
