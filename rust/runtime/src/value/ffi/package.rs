//! Package Management FFI
//! Provides FFI functions for SPK package operations, checksums, and file operations

use sha2::{Digest, Sha256};
use std::ffi::{CStr, CString};
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::os::raw::c_char;
use std::path::Path;

/// Calculate SHA256 checksum of a file
///
/// # Safety
/// - `file_path` must be a valid null-terminated C string
/// - Returns a heap-allocated C string that must be freed by the caller
#[no_mangle]
pub unsafe extern "C" fn rt_package_sha256(file_path: *const c_char) -> *mut c_char {
    if file_path.is_null() {
        return std::ptr::null_mut();
    }

    let path_str = match CStr::from_ptr(file_path).to_str() {
        Ok(s) => s,
        Err(_) => return std::ptr::null_mut(),
    };

    match calculate_sha256(path_str) {
        Ok(hash) => {
            let result = format!("sha256:{}", hash);
            CString::new(result).unwrap().into_raw()
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// Calculate SHA256 checksum of a file (internal)
fn calculate_sha256(file_path: &str) -> io::Result<String> {
    let mut file = File::open(file_path)?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 8192];

    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }

    let result = hasher.finalize();
    Ok(format!("{:x}", result))
}

/// Create a tarball from a directory
///
/// # Safety
/// - `source_dir` must be a valid null-terminated C string
/// - `output_path` must be a valid null-terminated C string
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_create_tarball(source_dir: *const c_char, output_path: *const c_char) -> i32 {
    if source_dir.is_null() || output_path.is_null() {
        return -1;
    }

    let source = match CStr::from_ptr(source_dir).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let output = match CStr::from_ptr(output_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match create_tarball(source, output) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Create a tarball from a directory (internal)
fn create_tarball(source_dir: &str, output_path: &str) -> io::Result<()> {
    use flate2::write::GzEncoder;
    use flate2::Compression;
    use tar::Builder;

    let tar_gz = File::create(output_path)?;
    let enc = GzEncoder::new(tar_gz, Compression::default());
    let mut tar = Builder::new(enc);

    tar.append_dir_all(".", source_dir)?;
    tar.finish()?;

    Ok(())
}

/// Extract a tarball to a directory
///
/// # Safety
/// - `tarball_path` must be a valid null-terminated C string
/// - `dest_dir` must be a valid null-terminated C string
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_extract_tarball(tarball_path: *const c_char, dest_dir: *const c_char) -> i32 {
    if tarball_path.is_null() || dest_dir.is_null() {
        return -1;
    }

    let tarball = match CStr::from_ptr(tarball_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let dest = match CStr::from_ptr(dest_dir).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match extract_tarball(tarball, dest) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Extract a tarball to a directory (internal)
fn extract_tarball(tarball_path: &str, dest_dir: &str) -> io::Result<()> {
    use flate2::read::GzDecoder;
    use tar::Archive;

    let tar_gz = File::open(tarball_path)?;
    let tar = GzDecoder::new(tar_gz);
    let mut archive = Archive::new(tar);

    archive.unpack(dest_dir)?;

    Ok(())
}

/// Get file size
///
/// # Safety
/// - `file_path` must be a valid null-terminated C string
/// - Returns file size in bytes, or -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_file_size(file_path: *const c_char) -> i64 {
    if file_path.is_null() {
        return -1;
    }

    let path = match CStr::from_ptr(file_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match fs::metadata(path) {
        Ok(metadata) => metadata.len() as i64,
        Err(_) => -1,
    }
}

/// Copy file
///
/// # Safety
/// - `src_path` must be a valid null-terminated C string
/// - `dst_path` must be a valid null-terminated C string
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_copy_file(src_path: *const c_char, dst_path: *const c_char) -> i32 {
    if src_path.is_null() || dst_path.is_null() {
        return -1;
    }

    let src = match CStr::from_ptr(src_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let dst = match CStr::from_ptr(dst_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match fs::copy(src, dst) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Create directory (with parents)
///
/// # Safety
/// - `dir_path` must be a valid null-terminated C string
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_mkdir_all(dir_path: *const c_char) -> i32 {
    if dir_path.is_null() {
        return -1;
    }

    let path = match CStr::from_ptr(dir_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match fs::create_dir_all(path) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Remove directory (recursive)
///
/// # Safety
/// - `dir_path` must be a valid null-terminated C string
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_remove_dir_all(dir_path: *const c_char) -> i32 {
    if dir_path.is_null() {
        return -1;
    }

    let path = match CStr::from_ptr(dir_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match fs::remove_dir_all(path) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Create symbolic link
///
/// # Safety
/// - `target` must be a valid null-terminated C string
/// - `link_path` must be a valid null-terminated C string
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_create_symlink(target: *const c_char, link_path: *const c_char) -> i32 {
    if target.is_null() || link_path.is_null() {
        return -1;
    }

    let target_str = match CStr::from_ptr(target).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let link_str = match CStr::from_ptr(link_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        match symlink(target_str, link_str) {
            Ok(_) => 0,
            Err(_) => -1,
        }
    }

    #[cfg(windows)]
    {
        use std::os::windows::fs::symlink_file;
        match symlink_file(target_str, link_str) {
            Ok(_) => 0,
            Err(_) => -1,
        }
    }
}

/// Set file permissions (Unix only)
///
/// # Safety
/// - `file_path` must be a valid null-terminated C string
/// - `mode` is Unix permission bits (e.g., 0o755)
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_chmod(file_path: *const c_char, mode: u32) -> i32 {
    if file_path.is_null() {
        return -1;
    }

    let path = match CStr::from_ptr(file_path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let perms = fs::Permissions::from_mode(mode);
        match fs::set_permissions(path, perms) {
            Ok(_) => 0,
            Err(_) => -1,
        }
    }

    #[cfg(not(unix))]
    {
        // Windows doesn't have Unix-style permissions
        0
    }
}

/// Check if path exists
///
/// # Safety
/// - `path` must be a valid null-terminated C string
/// - Returns 1 if exists, 0 if not, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_exists(path: *const c_char) -> i32 {
    if path.is_null() {
        return -1;
    }

    let path_str = match CStr::from_ptr(path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    if Path::new(path_str).exists() {
        1
    } else {
        0
    }
}

/// Check if path is a directory
///
/// # Safety
/// - `path` must be a valid null-terminated C string
/// - Returns 1 if directory, 0 if not, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_is_dir(path: *const c_char) -> i32 {
    if path.is_null() {
        return -1;
    }

    let path_str = match CStr::from_ptr(path).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    if Path::new(path_str).is_dir() {
        1
    } else {
        0
    }
}

/// Free a C string allocated by this module
///
/// # Safety
/// - `ptr` must be a pointer returned by one of the rt_package_* functions
#[no_mangle]
pub unsafe extern "C" fn rt_package_free_string(ptr: *mut c_char) {
    if !ptr.is_null() {
        let _ = CString::from_raw(ptr);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Write;
    use tempfile::TempDir;

    #[test]
    fn test_sha256() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let mut file = File::create(&file_path).unwrap();
        file.write_all(b"Hello, World!").unwrap();

        let hash = calculate_sha256(file_path.to_str().unwrap()).unwrap();
        // SHA256 of "Hello, World!"
        assert_eq!(hash, "dffd6021bb2bd5b0af676290809ec3a53191dd81c7f70a4b28688a362182986f");
    }

    #[test]
    fn test_create_and_extract_tarball() {
        let temp_dir = TempDir::new().unwrap();
        let source_dir = temp_dir.path().join("source");
        let tarball_path = temp_dir.path().join("test.tar.gz");
        let extract_dir = temp_dir.path().join("extract");

        // Create source directory with file
        fs::create_dir(&source_dir).unwrap();
        let test_file = source_dir.join("test.txt");
        let mut file = File::create(&test_file).unwrap();
        file.write_all(b"test content").unwrap();

        // Create tarball
        create_tarball(source_dir.to_str().unwrap(), tarball_path.to_str().unwrap()).unwrap();
        assert!(tarball_path.exists());

        // Extract tarball
        fs::create_dir(&extract_dir).unwrap();
        extract_tarball(tarball_path.to_str().unwrap(), extract_dir.to_str().unwrap()).unwrap();

        // Verify extracted file
        let extracted_file = extract_dir.join("test.txt");
        assert!(extracted_file.exists());
        let content = fs::read_to_string(extracted_file).unwrap();
        assert_eq!(content, "test content");
    }
}
