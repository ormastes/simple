// File system FFI functions for build system
// Provides file operations, directory operations, and file metadata

use super::RuntimeValue;
use std::os::raw::c_char;
use std::ffi::{CStr, CString};
use std::path::Path;
use std::fs;
use std::io::Read;

/// Check if file exists
#[no_mangle]
pub extern "C" fn rt_file_exists(path: *const c_char) -> bool {
    if path.is_null() {
        return false;
    }

    let c_str = unsafe { CStr::from_ptr(path) };
    if let Ok(path_str) = c_str.to_str() {
        Path::new(path_str).exists()
    } else {
        false
    }
}

/// Get file size in bytes
#[no_mangle]
pub extern "C" fn rt_file_size(path: *const c_char) -> i64 {
    if path.is_null() {
        return -1;
    }

    let c_str = unsafe { CStr::from_ptr(path) };
    if let Ok(path_str) = c_str.to_str() {
        match fs::metadata(path_str) {
            Ok(metadata) => metadata.len() as i64,
            Err(_) => -1,
        }
    } else {
        -1
    }
}

/// Copy file from src to dst
#[no_mangle]
pub extern "C" fn rt_file_copy(src: *const c_char, dst: *const c_char) -> bool {
    if src.is_null() || dst.is_null() {
        return false;
    }

    let src_cstr = unsafe { CStr::from_ptr(src) };
    let dst_cstr = unsafe { CStr::from_ptr(dst) };

    if let (Ok(src_str), Ok(dst_str)) = (src_cstr.to_str(), dst_cstr.to_str()) {
        fs::copy(src_str, dst_str).is_ok()
    } else {
        false
    }
}

/// Create directory (including parent directories)
#[no_mangle]
pub extern "C" fn rt_dir_create(path: *const c_char) -> bool {
    if path.is_null() {
        return false;
    }

    let c_str = unsafe { CStr::from_ptr(path) };
    if let Ok(path_str) = c_str.to_str() {
        fs::create_dir_all(path_str).is_ok()
    } else {
        false
    }
}

/// Remove file
#[no_mangle]
pub extern "C" fn rt_file_remove(path: *const c_char) -> bool {
    if path.is_null() {
        return false;
    }

    let c_str = unsafe { CStr::from_ptr(path) };
    if let Ok(path_str) = c_str.to_str() {
        fs::remove_file(path_str).is_ok()
    } else {
        false
    }
}

/// Remove directory (recursive)
#[no_mangle]
pub extern "C" fn rt_dir_remove(path: *const c_char) -> bool {
    if path.is_null() {
        return false;
    }

    let c_str = unsafe { CStr::from_ptr(path) };
    if let Ok(path_str) = c_str.to_str() {
        fs::remove_dir_all(path_str).is_ok()
    } else {
        false
    }
}

/// Calculate SHA256 hash of file
#[no_mangle]
pub extern "C" fn rt_file_hash_sha256(path: *const c_char) -> *mut c_char {
    use sha2::{Sha256, Digest};

    if path.is_null() {
        return CString::new("").unwrap().into_raw();
    }

    let c_str = unsafe { CStr::from_ptr(path) };
    if let Ok(path_str) = c_str.to_str() {
        match fs::File::open(path_str) {
            Ok(mut file) => {
                let mut hasher = Sha256::new();
                let mut buffer = Vec::new();

                if file.read_to_end(&mut buffer).is_ok() {
                    hasher.update(&buffer);
                    let result = hasher.finalize();
                    let hash_str = format!("{:x}", result);

                    match CString::new(hash_str) {
                        Ok(cstr) => cstr.into_raw(),
                        Err(_) => CString::new("").unwrap().into_raw(),
                    }
                } else {
                    CString::new("").unwrap().into_raw()
                }
            }
            Err(_) => CString::new("").unwrap().into_raw(),
        }
    } else {
        CString::new("").unwrap().into_raw()
    }
}

/// Run external process and capture output
/// Returns (stdout, stderr, exit_code) as a tuple
#[no_mangle]
pub extern "C" fn rt_process_run(
    cmd: *const c_char,
    args_ptr: *const *const c_char,
    args_count: usize,
) -> RuntimeValue {
    use super::{rt_dict_new, rt_dict_set, rt_string_new};
    use std::process::Command;

    // Create result dict
    let result_dict = rt_dict_new();

    if cmd.is_null() {
        // Return error result
        let empty = CString::new("").unwrap();
        rt_dict_set(result_dict, rt_string_new(b"stdout\0".as_ptr() as *const c_char), rt_string_new(empty.as_ptr()));
        rt_dict_set(result_dict, rt_string_new(b"stderr\0".as_ptr() as *const c_char), rt_string_new(CString::new("Command is null").unwrap().as_ptr()));
        rt_dict_set(result_dict, rt_string_new(b"exit_code\0".as_ptr() as *const c_char), RuntimeValue::from_i64(-1));
        return result_dict;
    }

    let cmd_cstr = unsafe { CStr::from_ptr(cmd) };
    let cmd_str = match cmd_cstr.to_str() {
        Ok(s) => s,
        Err(_) => {
            let empty = CString::new("").unwrap();
            rt_dict_set(result_dict, rt_string_new(b"stdout\0".as_ptr() as *const c_char), rt_string_new(empty.as_ptr()));
            rt_dict_set(result_dict, rt_string_new(b"stderr\0".as_ptr() as *const c_char), rt_string_new(CString::new("Invalid command").unwrap().as_ptr()));
            rt_dict_set(result_dict, rt_string_new(b"exit_code\0".as_ptr() as *const c_char), RuntimeValue::from_i64(-1));
            return result_dict;
        }
    };

    // Build command with arguments
    let mut command = Command::new(cmd_str);

    if !args_ptr.is_null() && args_count > 0 {
        let args_slice = unsafe { std::slice::from_raw_parts(args_ptr, args_count) };

        for &arg_ptr in args_slice {
            if !arg_ptr.is_null() {
                let arg_cstr = unsafe { CStr::from_ptr(arg_ptr) };
                if let Ok(arg_str) = arg_cstr.to_str() {
                    command.arg(arg_str);
                }
            }
        }
    }

    // Execute command
    match command.output() {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let exit_code = output.status.code().unwrap_or(-1) as i64;

            let stdout_cstr = CString::new(stdout).unwrap();
            let stderr_cstr = CString::new(stderr).unwrap();

            rt_dict_set(result_dict, rt_string_new(b"stdout\0".as_ptr() as *const c_char), rt_string_new(stdout_cstr.as_ptr()));
            rt_dict_set(result_dict, rt_string_new(b"stderr\0".as_ptr() as *const c_char), rt_string_new(stderr_cstr.as_ptr()));
            rt_dict_set(result_dict, rt_string_new(b"exit_code\0".as_ptr() as *const c_char), RuntimeValue::from_i64(exit_code));

            result_dict
        }
        Err(e) => {
            let empty = CString::new("").unwrap();
            let error_msg = CString::new(format!("Failed to execute: {}", e)).unwrap();

            rt_dict_set(result_dict, rt_string_new(b"stdout\0".as_ptr() as *const c_char), rt_string_new(empty.as_ptr()));
            rt_dict_set(result_dict, rt_string_new(b"stderr\0".as_ptr() as *const c_char), rt_string_new(error_msg.as_ptr()));
            rt_dict_set(result_dict, rt_string_new(b"exit_code\0".as_ptr() as *const c_char), RuntimeValue::from_i64(-1));

            result_dict
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    #[test]
    fn test_file_operations() {
        use std::fs::File;
        use std::io::Write;

        // Create test file
        let test_path = "/tmp/test_file_ops.txt";
        let mut file = File::create(test_path).unwrap();
        file.write_all(b"Hello, World!").unwrap();
        drop(file);

        let path_cstr = CString::new(test_path).unwrap();

        // Test exists
        assert!(rt_file_exists(path_cstr.as_ptr()));

        // Test size
        let size = rt_file_size(path_cstr.as_ptr());
        assert_eq!(size, 13);

        // Test copy
        let dst_path = "/tmp/test_file_ops_copy.txt";
        let dst_cstr = CString::new(dst_path).unwrap();
        assert!(rt_file_copy(path_cstr.as_ptr(), dst_cstr.as_ptr()));
        assert!(rt_file_exists(dst_cstr.as_ptr()));

        // Cleanup
        fs::remove_file(test_path).ok();
        fs::remove_file(dst_path).ok();
    }

    #[test]
    fn test_directory_operations() {
        let test_dir = "/tmp/test_dir_ops";
        let path_cstr = CString::new(test_dir).unwrap();

        // Create directory
        assert!(rt_dir_create(path_cstr.as_ptr()));
        assert!(Path::new(test_dir).exists());

        // Remove directory
        assert!(rt_dir_remove(path_cstr.as_ptr()));
        assert!(!Path::new(test_dir).exists());
    }
}
