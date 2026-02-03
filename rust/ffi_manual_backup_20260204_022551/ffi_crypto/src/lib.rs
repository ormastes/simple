//! crypto module
//!
//! Cryptographic Operations FFI
//! 
//! Hashing functions: SHA1, SHA256, xxHash, Argon2.

use sha1::Sha1;
use sha2::Sha256;
use sha2::Digest;
use xxhash_rust::xxh3::xxh3_64;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Calculate SHA1 hash of string
#[no_mangle]
pub unsafe extern "C" fn rt_hash_sha1(data: *const c_char) -> *mut c_char {
    let data_str = CStr::from_ptr(data as *const i8).to_string_lossy();
    let mut hasher = Sha1::new();
    hasher.update(data_str.as_bytes());
    let result = hasher.finalize();
    let hex = format!("{:x}", result);
    CString::new(hex).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
}

/// Calculate SHA256 hash of string
#[no_mangle]
pub unsafe extern "C" fn rt_hash_sha256(data: *const c_char) -> *mut c_char {
    let data_str = CStr::from_ptr(data as *const i8).to_string_lossy();
    let mut hasher = Sha256::new();
    hasher.update(data_str.as_bytes());
    let result = hasher.finalize();
    let hex = format!("{:x}", result);
    CString::new(hex).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
}

/// Calculate xxHash3 64-bit hash (fast non-cryptographic)
#[no_mangle]
pub unsafe extern "C" fn rt_hash_xxh3(data: *const c_char) -> u64 {
    let data_str = CStr::from_ptr(data as *const i8).to_string_lossy();
    xxh3_64(data_str.as_bytes())
}

/// Calculate SHA256 hash of file contents
#[no_mangle]
pub unsafe extern "C" fn rt_file_hash_sha256(path: *const c_char) -> *mut c_char {
    use std::fs::File;
    use std::io::Read;
    let path_str = CStr::from_ptr(path as *const i8).to_string_lossy();
    match File::open(path_str.as_ref()) {
        Ok(mut file) => {
            let mut hasher = Sha256::new();
            let mut buffer = [0u8; 8192];
            loop {
                match file.read(&mut buffer) {
                    Ok(0) => break,
                    Ok(n) => hasher.update(&buffer[..n]),
                    Err(_) => return std::ptr::null_mut(),
                }
            }
            let result = hasher.finalize();
            let hex = format!("{:x}", result);
            CString::new(hex).ok().map(|c| c.into_raw()).unwrap_or(std::ptr::null_mut())
        }
        Err(_) => std::ptr::null_mut(),
    }
}

