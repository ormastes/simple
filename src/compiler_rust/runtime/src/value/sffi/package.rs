//! Package Management SFFI
//! Provides SFFI functions for SPK package operations, checksums, and file operations

use sha2::{Digest, Sha256};
use std::ffi::CString;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::os::raw::c_char;
use std::path::Path;

/// Decode a Simple `text` argument passed as an explicit `(ptr, len)` pair.
///
/// The whole `rt_package_*` family used to take `*const c_char` and decode with
/// `CStr::from_ptr`. That signature is unreachable from generated code: Simple
/// heap strings are allocated by `alloc_runtime_string` as
/// `size_of::<RuntimeString>() + len` with **no trailing NUL**, so
/// `rt_string_data` never yields a null-terminated pointer and there is no sound
/// way for codegen to satisfy a `*const c_char` parameter without copying. The
/// repo's dominant, sound convention — used by every `rt_file_*` / `rt_dir_*`
/// entry point — is an explicit `(ptr, len)` pair expanded by
/// `expand_text_args` in `compiler/src/codegen/instr/calls.rs`. This family now
/// follows it. See
/// `doc/08_tracking/bug/rt_package_chmod_family_fails_from_jit_key_left_world_readable_2026-08-08.md`.
///
/// # Safety
/// - `ptr` must be null, or point to at least `len` initialized bytes.
unsafe fn text_arg<'a>(ptr: *const u8, len: usize) -> Option<&'a str> {
    if ptr.is_null() {
        return None;
    }
    if len == 0 {
        return Some("");
    }
    std::str::from_utf8(std::slice::from_raw_parts(ptr, len)).ok()
}

/// Calculate SHA256 checksum of a file
///
/// # Safety
/// - `file_path`/`file_path_len` must describe a valid UTF-8 byte range
/// - Returns a heap-allocated C string that must be freed by the caller
#[no_mangle]
pub unsafe extern "C" fn rt_package_sha256(file_path: *const u8, file_path_len: usize) -> *mut c_char {
    let path_str = match text_arg(file_path, file_path_len) {
        Some(s) => s,
        None => return std::ptr::null_mut(),
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

fn packaging_compression_unavailable() -> io::Error {
    io::Error::other("packaging compression support is disabled in this runtime build")
}

fn package_compression_unavailable(name: &str) {
    eprintln!(
        "Runtime error: {name} is unavailable in this runtime build (enable Cargo feature `packaging-compression`)"
    );
}

/// Create a tarball from a directory
///
/// # Safety
/// - `source_dir`/`source_dir_len` must describe a valid UTF-8 byte range
/// - `output_path`/`output_path_len` must describe a valid UTF-8 byte range
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_create_tarball(
    source_dir: *const u8,
    source_dir_len: usize,
    output_path: *const u8,
    output_path_len: usize,
) -> i32 {
    #[cfg(not(feature = "packaging-compression"))]
    {
        let _ = source_dir;
        let _ = source_dir_len;
        let _ = output_path;
        let _ = output_path_len;
        package_compression_unavailable("rt_package_create_tarball");
        -1
    }

    #[cfg(feature = "packaging-compression")]
    {
        let source = match text_arg(source_dir, source_dir_len) {
            Some(s) => s,
            None => return -1,
        };

        let output = match text_arg(output_path, output_path_len) {
            Some(s) => s,
            None => return -1,
        };

        match create_tarball(source, output) {
            Ok(_) => 0,
            Err(_) => -1,
        }
    }
}

/// Create a tarball from a directory (internal)
#[cfg(feature = "packaging-compression")]
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

#[cfg(not(feature = "packaging-compression"))]
fn create_tarball(source_dir: &str, output_path: &str) -> io::Result<()> {
    let _ = source_dir;
    let _ = output_path;
    Err(packaging_compression_unavailable())
}

/// Extract a tarball to a directory
///
/// # Safety
/// - `tarball_path`/`tarball_path_len` must describe a valid UTF-8 byte range
/// - `dest_dir`/`dest_dir_len` must describe a valid UTF-8 byte range
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_extract_tarball(
    tarball_path: *const u8,
    tarball_path_len: usize,
    dest_dir: *const u8,
    dest_dir_len: usize,
) -> i32 {
    #[cfg(not(feature = "packaging-compression"))]
    {
        let _ = tarball_path;
        let _ = tarball_path_len;
        let _ = dest_dir;
        let _ = dest_dir_len;
        package_compression_unavailable("rt_package_extract_tarball");
        -1
    }

    #[cfg(feature = "packaging-compression")]
    {
        let tarball = match text_arg(tarball_path, tarball_path_len) {
            Some(s) => s,
            None => return -1,
        };

        let dest = match text_arg(dest_dir, dest_dir_len) {
            Some(s) => s,
            None => return -1,
        };

        match extract_tarball(tarball, dest) {
            Ok(_) => 0,
            Err(_) => -1,
        }
    }
}

/// Extract a tarball to a directory (internal)
#[cfg(feature = "packaging-compression")]
fn extract_tarball(tarball_path: &str, dest_dir: &str) -> io::Result<()> {
    use flate2::read::GzDecoder;
    use tar::Archive;

    let tar_gz = File::open(tarball_path)?;
    let tar = GzDecoder::new(tar_gz);
    let mut archive = Archive::new(tar);

    archive.unpack(dest_dir)?;

    Ok(())
}

#[cfg(not(feature = "packaging-compression"))]
fn extract_tarball(tarball_path: &str, dest_dir: &str) -> io::Result<()> {
    let _ = tarball_path;
    let _ = dest_dir;
    Err(packaging_compression_unavailable())
}

/// Get file size
///
/// # Safety
/// - `file_path`/`file_path_len` must describe a valid UTF-8 byte range
/// - Returns file size in bytes, or -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_file_size(file_path: *const u8, file_path_len: usize) -> i64 {
    let path = match text_arg(file_path, file_path_len) {
        Some(s) => s,
        None => return -1,
    };

    match fs::metadata(path) {
        Ok(metadata) => metadata.len() as i64,
        Err(_) => -1,
    }
}

/// Copy file
///
/// # Safety
/// - `src_path`/`src_path_len` must describe a valid UTF-8 byte range
/// - `dst_path`/`dst_path_len` must describe a valid UTF-8 byte range
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_copy_file(
    src_path: *const u8,
    src_path_len: usize,
    dst_path: *const u8,
    dst_path_len: usize,
) -> i32 {
    let src = match text_arg(src_path, src_path_len) {
        Some(s) => s,
        None => return -1,
    };

    let dst = match text_arg(dst_path, dst_path_len) {
        Some(s) => s,
        None => return -1,
    };

    match fs::copy(src, dst) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Create directory (with parents)
///
/// # Safety
/// - `dir_path`/`dir_path_len` must describe a valid UTF-8 byte range
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_mkdir_all(dir_path: *const u8, dir_path_len: usize) -> i32 {
    let path = match text_arg(dir_path, dir_path_len) {
        Some(s) => s,
        None => return -1,
    };

    match fs::create_dir_all(path) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Remove directory (recursive)
///
/// # Safety
/// - `dir_path`/`dir_path_len` must describe a valid UTF-8 byte range
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_remove_dir_all(dir_path: *const u8, dir_path_len: usize) -> i32 {
    let path = match text_arg(dir_path, dir_path_len) {
        Some(s) => s,
        None => return -1,
    };

    match fs::remove_dir_all(path) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Create symbolic link
///
/// # Safety
/// - `target`/`target_len` must describe a valid UTF-8 byte range
/// - `link_path`/`link_path_len` must describe a valid UTF-8 byte range
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_create_symlink(
    target: *const u8,
    target_len: usize,
    link_path: *const u8,
    link_path_len: usize,
) -> i32 {
    let target_str = match text_arg(target, target_len) {
        Some(s) => s,
        None => return -1,
    };

    let link_str = match text_arg(link_path, link_path_len) {
        Some(s) => s,
        None => return -1,
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
/// - `file_path`/`file_path_len` must describe a valid UTF-8 byte range
/// - `mode` is Unix permission bits (e.g., 0o755)
/// - Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_chmod(file_path: *const u8, file_path_len: usize, mode: u32) -> i32 {
    let path = match text_arg(file_path, file_path_len) {
        Some(s) => s,
        None => return -1,
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
/// - `path`/`path_len` must describe a valid UTF-8 byte range
/// - Returns 1 if exists, 0 if not, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_exists(path: *const u8, path_len: usize) -> i32 {
    let path_str = match text_arg(path, path_len) {
        Some(s) => s,
        None => return -1,
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
/// - `path`/`path_len` must describe a valid UTF-8 byte range
/// - Returns 1 if directory, 0 if not, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_package_is_dir(path: *const u8, path_len: usize) -> i32 {
    let path_str = match text_arg(path, path_len) {
        Some(s) => s,
        None => return -1,
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

    #[cfg(feature = "packaging-compression")]
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
