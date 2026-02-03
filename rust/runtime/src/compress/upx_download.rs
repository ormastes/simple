//! UPX auto-download and cache management
//!
//! This module provides automatic downloading and caching of UPX binaries
//! from GitHub releases when UPX is not found in the system PATH.
//!
//! Cache location: ~/.simple/tools/upx/<version>/upx
//!
//! Supported platforms:
//! - Linux: x86_64, aarch64, i686
//! - macOS: x86_64 (Intel), aarch64 (Apple Silicon)
//! - Windows: x86_64

use simple_common::target::{Target, TargetArch, TargetOS};
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

/// UPX version to download if not found
const UPX_VERSION: &str = "4.2.4";

/// GitHub releases URL base
const UPX_RELEASES_BASE: &str = "https://github.com/upx/upx/releases/download";

/// Get the cache directory for UPX tools
///
/// Returns: ~/.simple/tools/upx/
pub fn get_upx_cache_dir() -> Result<PathBuf, String> {
    // Use syscall instead of dirs-next crate
    use std::ffi::CStr;
    let home = unsafe {
        let ptr = crate::syscalls_ffi::rt_env_home();
        if ptr.is_null() {
            return Err("Cannot determine home directory".to_string());
        }
        let c_str = CStr::from_ptr(ptr);
        let home_str = c_str.to_string_lossy().into_owned();
        libc::free(ptr as *mut libc::c_void);
        PathBuf::from(home_str)
    };

    let cache_dir = home.join(".simple").join("tools").join("upx");

    // Create directory if it doesn't exist
    if !cache_dir.exists() {
        fs::create_dir_all(&cache_dir).map_err(|e| format!("Failed to create cache directory: {}", e))?;
    }

    Ok(cache_dir)
}

/// Get the path to a specific UPX version in cache
///
/// Returns: ~/.simple/tools/upx/<version>/upx
pub fn get_cached_upx_path(version: &str) -> Result<PathBuf, String> {
    let cache_dir = get_upx_cache_dir()?;
    let version_dir = cache_dir.join(version);

    #[cfg(windows)]
    let binary_name = "upx.exe";
    #[cfg(not(windows))]
    let binary_name = "upx";

    Ok(version_dir.join(binary_name))
}

/// Check if UPX is available in the system PATH
///
/// Returns: Some(path) if found in PATH, None otherwise
pub fn find_upx_in_path() -> Option<PathBuf> {
    Command::new("upx").arg("--version").output().ok().and_then(|output| {
        if output.status.success() {
            // Try to get the full path using 'which' on Unix or 'where' on Windows
            #[cfg(unix)]
            let which_output = Command::new("which").arg("upx").output().ok()?;
            #[cfg(windows)]
            let which_output = Command::new("where").arg("upx").output().ok()?;

            if which_output.status.success() {
                let path_str = String::from_utf8_lossy(&which_output.stdout);
                let path = path_str.trim();
                if !path.is_empty() {
                    return Some(PathBuf::from(path));
                }
            }

            // Fallback: just return "upx" as a path
            Some(PathBuf::from("upx"))
        } else {
            None
        }
    })
}

/// Find UPX binary (system PATH or cache)
///
/// Priority:
/// 1. System PATH (if installed)
/// 2. Cache (~/.simple/tools/upx/latest/)
/// 3. Cache (~/.simple/tools/upx/<UPX_VERSION>/)
///
/// Returns: Some(path) if found, None if not available
pub fn find_upx_binary() -> Option<PathBuf> {
    // 1. Check system PATH
    if let Some(path) = find_upx_in_path() {
        return Some(path);
    }

    // 2. Check cache (latest)
    if let Ok(latest_path) = get_cached_upx_path("latest") {
        if latest_path.exists() {
            return Some(latest_path);
        }
    }

    // 3. Check cache (specific version)
    if let Ok(version_path) = get_cached_upx_path(UPX_VERSION) {
        if version_path.exists() {
            return Some(version_path);
        }
    }

    None
}

/// Get the UPX release filename for the current platform
///
/// Returns: filename like "upx-4.2.4-amd64_linux.tar.xz"
fn get_upx_release_filename(version: &str) -> Result<String, String> {
    let target = Target::host();

    let arch_str = match target.arch {
        TargetArch::X86_64 => "amd64",
        TargetArch::Aarch64 => {
            if target.os == TargetOS::MacOS {
                "arm64"
            } else {
                "arm64"
            }
        }
        TargetArch::X86 => "i386",
        _ => {
            return Err(format!(
                "Unsupported architecture for UPX download: {}",
                target.arch.name()
            ))
        }
    };

    let os_str = match target.os {
        TargetOS::Linux => "linux",
        TargetOS::MacOS => "macos",
        TargetOS::Windows => "win64",
        _ => return Err(format!("Unsupported OS for UPX download: {}", target.os.name())),
    };

    // Format: upx-{version}-{arch}_{os}.tar.xz
    // Examples:
    // - upx-4.2.4-amd64_linux.tar.xz
    // - upx-4.2.4-arm64_macos.tar.xz
    // - upx-4.2.4-amd64_win64.zip (Windows uses zip)

    if target.os == TargetOS::Windows {
        Ok(format!("upx-{}-{}_{}.zip", version, arch_str, os_str))
    } else {
        Ok(format!("upx-{}-{}_{}.tar.xz", version, arch_str, os_str))
    }
}

/// Get the download URL for a specific UPX version
///
/// Returns: Full URL to the release archive
fn get_upx_download_url(version: &str) -> Result<String, String> {
    let filename = get_upx_release_filename(version)?;
    Ok(format!("{}/v{}/{}", UPX_RELEASES_BASE, version, filename))
}

/// Download a file from URL to a local path
///
/// Returns: Ok(()) on success, Err on failure
fn download_file(url: &str, dest: &Path) -> Result<(), String> {
    eprintln!("Downloading from: {}", url);

    let response = ureq::get(url)
        .call()
        .map_err(|e| format!("HTTP request failed: {}", e))?;

    let status = response.status();
    if status != 200 {
        return Err(format!("HTTP error {}: {}", status, response.status_text()));
    }

    // Read response body
    let mut reader = response.into_reader();
    let mut buffer = Vec::new();
    reader
        .read_to_end(&mut buffer)
        .map_err(|e| format!("Failed to read response: {}", e))?;

    // Write to destination
    let mut file = fs::File::create(dest).map_err(|e| format!("Failed to create destination file: {}", e))?;
    file.write_all(&buffer)
        .map_err(|e| format!("Failed to write file: {}", e))?;

    Ok(())
}

/// Extract UPX binary from .tar.xz archive
///
/// Archives have structure: upx-{version}-{platform}/upx
/// Extract to: dest_dir/upx
fn extract_tar_xz(archive_path: &Path, dest_dir: &Path) -> Result<PathBuf, String> {
    use std::io::BufReader;
    use tar::Archive;
    use xz2::read::XzDecoder;

    let file = fs::File::open(archive_path).map_err(|e| format!("Failed to open archive: {}", e))?;
    let buf_reader = BufReader::new(file);
    let xz_decoder = XzDecoder::new(buf_reader);
    let mut archive = Archive::new(xz_decoder);

    #[cfg(windows)]
    let binary_name = "upx.exe";
    #[cfg(not(windows))]
    let binary_name = "upx";

    let mut upx_binary_path: Option<PathBuf> = None;

    for entry_result in archive
        .entries()
        .map_err(|e| format!("Failed to read archive entries: {}", e))?
    {
        let mut entry = entry_result.map_err(|e| format!("Failed to read entry: {}", e))?;
        let path = entry.path().map_err(|e| format!("Failed to get entry path: {}", e))?;

        // Look for the upx binary (in any subdirectory)
        if path.file_name().and_then(|s| s.to_str()) == Some(binary_name) {
            let dest_path = dest_dir.join(binary_name);
            entry
                .unpack(&dest_path)
                .map_err(|e| format!("Failed to extract {}: {}", binary_name, e))?;
            upx_binary_path = Some(dest_path);
            break;
        }
    }

    match upx_binary_path {
        Some(path) => {
            // Set executable permissions on Unix
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mut perms = fs::metadata(&path)
                    .map_err(|e| format!("Failed to get file metadata: {}", e))?
                    .permissions();
                perms.set_mode(0o755);
                fs::set_permissions(&path, perms)
                    .map_err(|e| format!("Failed to set executable permissions: {}", e))?;
            }

            Ok(path)
        }
        None => Err(format!("UPX binary not found in archive")),
    }
}

/// Verify SHA256 checksum of a file (placeholder - checksums not implemented yet)
///
/// TODO: Download and verify checksums from UPX releases
fn verify_checksum(_file_path: &Path, _expected: &str) -> Result<(), String> {
    // For now, skip checksum verification
    // In production, download SHA256SUMS file and verify
    Ok(())
}

/// Download UPX from GitHub releases
///
/// Downloads, extracts, and caches the UPX binary
///
/// Returns: Path to the downloaded UPX binary
pub fn download_upx(version: &str) -> Result<PathBuf, String> {
    let url = get_upx_download_url(version)?;
    let cache_dir = get_upx_cache_dir()?;

    // Create version-specific directory
    let version_dir = cache_dir.join(version);
    if !version_dir.exists() {
        fs::create_dir_all(&version_dir).map_err(|e| format!("Failed to create version directory: {}", e))?;
    }

    // Download to temporary file
    let temp_dir = std::env::temp_dir();
    let filename = get_upx_release_filename(version)?;
    let temp_archive = temp_dir.join(&filename);

    eprintln!("Downloading UPX {}...", version);
    download_file(&url, &temp_archive)?;

    // Extract archive
    eprintln!("Extracting UPX binary...");
    let upx_path = extract_tar_xz(&temp_archive, &version_dir)?;

    // Clean up temporary archive
    let _ = fs::remove_file(&temp_archive);

    // Create "latest" symlink (Unix) or copy (Windows)
    let latest_dir = cache_dir.join("latest");
    if latest_dir.exists() {
        let _ = fs::remove_dir_all(&latest_dir);
    }

    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(&version_dir, &latest_dir)
            .map_err(|e| format!("Failed to create 'latest' symlink: {}", e))?;
    }
    #[cfg(windows)]
    {
        fs::create_dir_all(&latest_dir).map_err(|e| format!("Failed to create 'latest' directory: {}", e))?;
        let latest_upx = latest_dir.join("upx.exe");
        fs::copy(&upx_path, &latest_upx).map_err(|e| format!("Failed to copy to 'latest': {}", e))?;
    }

    eprintln!("UPX {} installed to: {}", version, upx_path.display());

    Ok(upx_path)
}

/// Ensure UPX is available (system or auto-download)
///
/// This is the main entry point for getting UPX.
/// Priority:
/// 1. System PATH
/// 2. Cached version
/// 3. Auto-download
///
/// Returns: Path to UPX binary
pub fn ensure_upx_available() -> Result<PathBuf, String> {
    // Try to find existing UPX
    if let Some(path) = find_upx_binary() {
        return Ok(path);
    }

    // Not found - auto-download
    eprintln!("UPX not found in PATH or cache.");
    download_upx(UPX_VERSION)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_cache_dir() {
        let result = get_upx_cache_dir();
        assert!(result.is_ok(), "Should get cache directory");

        let path = result.unwrap();
        assert!(path.to_string_lossy().contains(".simple/tools/upx"));
    }

    #[test]
    fn test_get_cached_path() {
        let result = get_cached_upx_path("4.2.4");
        assert!(result.is_ok());

        let path = result.unwrap();
        assert!(path.to_string_lossy().contains("4.2.4"));

        #[cfg(windows)]
        assert!(path.to_string_lossy().ends_with("upx.exe"));
        #[cfg(not(windows))]
        assert!(path.to_string_lossy().ends_with("upx"));
    }

    #[test]
    fn test_get_release_filename() {
        let result = get_upx_release_filename("4.2.4");

        // Should succeed on supported platforms
        let target = Target::host();
        if matches!(target.os, TargetOS::Linux | TargetOS::MacOS | TargetOS::Windows)
            && matches!(target.arch, TargetArch::X86_64 | TargetArch::Aarch64 | TargetArch::X86)
        {
            assert!(result.is_ok());
            let filename = result.unwrap();
            assert!(filename.starts_with("upx-4.2.4-"));
        }
    }

    #[test]
    fn test_get_download_url() {
        let result = get_upx_download_url("4.2.4");

        let target = Target::host();
        if matches!(target.os, TargetOS::Linux | TargetOS::MacOS | TargetOS::Windows)
            && matches!(target.arch, TargetArch::X86_64 | TargetArch::Aarch64 | TargetArch::X86)
        {
            assert!(result.is_ok());
            let url = result.unwrap();
            assert!(url.starts_with("https://github.com/upx/upx/releases/download/v4.2.4/"));
        }
    }

    #[test]
    fn test_find_upx_in_path() {
        // This test will pass if UPX is installed
        let result = find_upx_in_path();
        // Don't assert - just check it doesn't panic
        if let Some(path) = result {
            assert!(path.to_string_lossy().len() > 0);
        }
    }

    #[test]
    fn test_platform_support() {
        let target = Target::host();

        // Check if current platform is supported
        let supported = matches!(
            (target.os, target.arch),
            (TargetOS::Linux, TargetArch::X86_64)
                | (TargetOS::Linux, TargetArch::Aarch64)
                | (TargetOS::Linux, TargetArch::X86)
                | (TargetOS::MacOS, TargetArch::X86_64)
                | (TargetOS::MacOS, TargetArch::Aarch64)
                | (TargetOS::Windows, TargetArch::X86_64)
        );

        if supported {
            assert!(get_upx_release_filename("4.2.4").is_ok());
        } else {
            assert!(get_upx_release_filename("4.2.4").is_err());
        }
    }
}
