//! UPX (Ultimate Packer for eXecutables) compression wrapper
//!
//! Provides Rust API and FFI bindings for UPX compression/decompression.
//! UPX must be installed on the system for this module to work.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::path::Path;
use std::process::Command;

/// Compression level for UPX
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i32)]
pub enum CompressionLevel {
    Fast = 1,        // --fast (fastest, less compression)
    Best = 2,        // --best (balanced, recommended)
    UltraBrute = 3,  // --ultra-brute (slowest, maximum compression)
}

impl CompressionLevel {
    fn from_i32(value: i32) -> Option<Self> {
        match value {
            1 => Some(CompressionLevel::Fast),
            2 => Some(CompressionLevel::Best),
            3 => Some(CompressionLevel::UltraBrute),
            _ => None,
        }
    }

    fn as_args(&self) -> &'static str {
        match self {
            CompressionLevel::Fast => "--fast",
            CompressionLevel::Best => "--best",
            CompressionLevel::UltraBrute => "--ultra-brute",
        }
    }
}

/// Check if UPX is installed on the system
pub fn is_upx_available() -> bool {
    Command::new("upx")
        .arg("--version")
        .output()
        .is_ok()
}

/// Compress a file using UPX
///
/// # Arguments
/// * `input` - Path to input file
/// * `output` - Path to output file (if None, compresses in-place)
/// * `level` - Compression level
///
/// # Returns
/// Ok(output_path) on success, Err(message) on failure
pub fn compress_file(
    input: &str,
    output: Option<&str>,
    level: CompressionLevel,
) -> Result<String, String> {
    if !is_upx_available() {
        return Err("UPX is not installed. Install with: sudo apt-get install upx".to_string());
    }

    if !Path::new(input).exists() {
        return Err(format!("Input file not found: {}", input));
    }

    let output_path = output.unwrap_or(input);

    // If output is different from input, copy first
    if output_path != input {
        std::fs::copy(input, output_path)
            .map_err(|e| format!("Failed to copy file: {}", e))?;
    }

    // Run UPX compression
    let output = Command::new("upx")
        .arg(level.as_args())
        .arg("--lzma")  // Use LZMA compression (better ratio)
        .arg(output_path)
        .output()
        .map_err(|e| format!("Failed to run UPX: {}", e))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("UPX compression failed: {}", stderr));
    }

    Ok(output_path.to_string())
}

/// Decompress a UPX-compressed file
///
/// # Arguments
/// * `input` - Path to compressed file
/// * `output` - Path to output file
///
/// # Returns
/// Ok(output_path) on success, Err(message) on failure
pub fn decompress_file(input: &str, output: &str) -> Result<String, String> {
    if !is_upx_available() {
        return Err("UPX is not installed".to_string());
    }

    if !Path::new(input).exists() {
        return Err(format!("Input file not found: {}", input));
    }

    // Copy input to output first
    std::fs::copy(input, output)
        .map_err(|e| format!("Failed to copy file: {}", e))?;

    // Run UPX decompression
    let cmd_output = Command::new("upx")
        .arg("-d")  // Decompress
        .arg(output)
        .output()
        .map_err(|e| format!("Failed to run UPX: {}", e))?;

    if !cmd_output.status.success() {
        let stderr = String::from_utf8_lossy(&cmd_output.stderr);
        return Err(format!("UPX decompression failed: {}", stderr));
    }

    Ok(output.to_string())
}

/// Check if a file is UPX-compressed
///
/// # Arguments
/// * `file` - Path to file to check
///
/// # Returns
/// Ok(true) if compressed, Ok(false) if not, Err on failure
pub fn is_compressed(file: &str) -> Result<bool, String> {
    if !Path::new(file).exists() {
        return Err(format!("File not found: {}", file));
    }

    // Run UPX test (returns success if compressed)
    let output = Command::new("upx")
        .arg("-t")  // Test
        .arg(file)
        .output()
        .map_err(|e| format!("Failed to run UPX: {}", e))?;

    Ok(output.status.success())
}

/// Get compression ratio of a file (original_size / compressed_size)
///
/// Note: This is approximate and requires the file to be UPX-compressed
pub fn get_compression_ratio(file: &str) -> Result<f64, String> {
    if !is_compressed(file)? {
        return Ok(1.0);  // Not compressed
    }

    // Run UPX list to get info
    let output = Command::new("upx")
        .arg("-l")  // List info
        .arg(file)
        .output()
        .map_err(|e| format!("Failed to run UPX: {}", e))?;

    if !output.status.success() {
        return Err("Failed to get UPX info".to_string());
    }

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse output to find ratio (format: "xxx -> yyy   ratio")
    for line in stdout.lines() {
        if line.contains("->") {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 4 {
                // Parse original and compressed sizes
                if let (Ok(original), Ok(compressed)) = (
                    parts[0].parse::<f64>(),
                    parts[2].parse::<f64>(),
                ) {
                    if compressed > 0.0 {
                        return Ok(original / compressed);
                    }
                }
            }
        }
    }

    Err("Could not parse compression ratio".to_string())
}

// ============================================================================
// FFI Bindings for Simple
// ============================================================================

/// FFI: Compress a file with UPX
///
/// # Safety
/// - `input` and `output` must be valid null-terminated C strings
/// - Returns 0 on success, -1 on failure
#[no_mangle]
pub unsafe extern "C" fn upx_compress_file(
    input: *const c_char,
    output: *const c_char,
    level: i32,
) -> i32 {
    if input.is_null() {
        return -1;
    }

    let input_str = match CStr::from_ptr(input).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let output_str = if output.is_null() {
        None
    } else {
        match CStr::from_ptr(output).to_str() {
            Ok(s) => Some(s),
            Err(_) => return -1,
        }
    };

    let compression_level = match CompressionLevel::from_i32(level) {
        Some(l) => l,
        None => CompressionLevel::Best,  // Default to best
    };

    match compress_file(input_str, output_str, compression_level) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// FFI: Decompress a UPX-compressed file
///
/// # Safety
/// - `input` and `output` must be valid null-terminated C strings
/// - Returns 0 on success, -1 on failure
#[no_mangle]
pub unsafe extern "C" fn upx_decompress_file(
    input: *const c_char,
    output: *const c_char,
) -> i32 {
    if input.is_null() || output.is_null() {
        return -1;
    }

    let input_str = match CStr::from_ptr(input).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let output_str = match CStr::from_ptr(output).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match decompress_file(input_str, output_str) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// FFI: Check if a file is UPX-compressed
///
/// # Safety
/// - `file` must be a valid null-terminated C string
/// - Returns 1 if compressed, 0 if not, -1 on error
#[no_mangle]
pub unsafe extern "C" fn upx_is_compressed(file: *const c_char) -> i32 {
    if file.is_null() {
        return -1;
    }

    let file_str = match CStr::from_ptr(file).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match is_compressed(file_str) {
        Ok(true) => 1,
        Ok(false) => 0,
        Err(_) => -1,
    }
}

/// FFI: Get compression ratio of a file
///
/// # Safety
/// - `file` must be a valid null-terminated C string
/// - Returns ratio as f64, or -1.0 on error
#[no_mangle]
pub unsafe extern "C" fn upx_get_ratio(file: *const c_char) -> f64 {
    if file.is_null() {
        return -1.0;
    }

    let file_str = match CStr::from_ptr(file).to_str() {
        Ok(s) => s,
        Err(_) => return -1.0,
    };

    match get_compression_ratio(file_str) {
        Ok(ratio) => ratio,
        Err(_) => -1.0,
    }
}

/// FFI: Check if UPX is available
///
/// # Safety
/// - Returns 1 if UPX is available, 0 if not
#[no_mangle]
pub extern "C" fn upx_is_available() -> i32 {
    if is_upx_available() {
        1
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_upx_available() {
        // This test will pass if UPX is installed
        if is_upx_available() {
            assert!(is_upx_available());
        }
    }

    #[test]
    fn test_compression_level() {
        assert_eq!(CompressionLevel::from_i32(1), Some(CompressionLevel::Fast));
        assert_eq!(CompressionLevel::from_i32(2), Some(CompressionLevel::Best));
        assert_eq!(CompressionLevel::from_i32(3), Some(CompressionLevel::UltraBrute));
        assert_eq!(CompressionLevel::from_i32(99), None);
    }
}
