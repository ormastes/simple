//! Self-extracting executable builder
//!
//! This module provides functionality to create self-extracting executables
//! using pure Rust LZMA compression (no UPX dependency).
//!
//! The resulting executables contain:
//! - A minimal decompressor stub (~40 KB)
//! - LZMA-compressed original binary
//! - Metadata trailer
//!
//! Advantages over UPX:
//! - Pure Rust implementation
//! - No external dependencies
//! - Portable across platforms
//! - Custom compression levels

use crate::compress::lzma_stub::{Trailer, TRAILER_SIZE};
use std::ffi::{CStr, CString};
use std::fs;
use std::io::Write;
use std::os::raw::c_char;
use std::path::Path;

/// Compression level for LZMA
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LzmaLevel {
    Fast = 1,    // Level 1 - fastest
    Normal = 6,  // Level 6 - balanced (default)
    Best = 9,    // Level 9 - best compression
}

impl LzmaLevel {
    pub fn from_i32(value: i32) -> Option<Self> {
        match value {
            1 => Some(LzmaLevel::Fast),
            6 => Some(LzmaLevel::Normal),
            9 => Some(LzmaLevel::Best),
            _ => None,
        }
    }

    pub fn as_u32(&self) -> u32 {
        match self {
            LzmaLevel::Fast => 1,
            LzmaLevel::Normal => 6,
            LzmaLevel::Best => 9,
        }
    }
}

/// Compress data with LZMA
fn compress_lzma(data: &[u8], level: LzmaLevel) -> Result<Vec<u8>, String> {
    use xz2::write::XzEncoder;

    let mut encoder = XzEncoder::new(Vec::new(), level.as_u32());

    encoder
        .write_all(data)
        .map_err(|e| format!("LZMA compression failed: {}", e))?;

    encoder
        .finish()
        .map_err(|e| format!("LZMA compression finish failed: {}", e))
}

/// Simple CRC32 implementation
fn crc32(data: &[u8]) -> u32 {
    let mut crc = 0xFFFFFFFFu32;

    for &byte in data {
        crc ^= byte as u32;
        for _ in 0..8 {
            if crc & 1 != 0 {
                crc = (crc >> 1) ^ 0xEDB88320;
            } else {
                crc >>= 1;
            }
        }
    }

    !crc
}

/// Get or build the decompressor stub binary
///
/// For now, this returns a placeholder. In production, this would:
/// 1. Include pre-compiled stub via include_bytes!
/// 2. Or build stub on-demand using cargo
fn get_stub_binary() -> Result<Vec<u8>, String> {
    // TODO: Build actual stub binary
    // For now, return a minimal ELF header as placeholder

    // In production, this would be:
    // const STUB_BINARY: &[u8] = include_bytes!("../../../target/stub/lzma_stub");
    // Ok(STUB_BINARY.to_vec())

    // For now, use a placeholder that will be replaced
    // The actual stub will be built separately
    Err("Stub binary not yet built. Run 'cargo build --bin lzma_stub' first.".to_string())
}

/// Create a self-extracting executable
///
/// # Arguments
/// * `input` - Path to input binary
/// * `output` - Path to output self-extracting binary
/// * `level` - Compression level (Fast, Normal, Best)
///
/// # Returns
/// Ok(compression_ratio) on success, Err on failure
pub fn create_self_extracting(
    input: &Path,
    output: &Path,
    level: LzmaLevel,
) -> Result<f64, String> {
    // Read input binary
    let original = fs::read(input).map_err(|e| format!("Failed to read input file: {}", e))?;
    let original_size = original.len();

    if original_size == 0 {
        return Err("Input file is empty".to_string());
    }

    // Get decompressor stub
    let stub = get_stub_binary()?;
    let stub_size = stub.len();

    // Compress payload
    eprintln!("Compressing {} bytes with LZMA...", original_size);
    let compressed = compress_lzma(&original, level)?;
    let payload_size = compressed.len();

    eprintln!(
        "Compressed: {} -> {} bytes ({:.2}x)",
        original_size,
        payload_size,
        original_size as f64 / payload_size as f64
    );

    // Calculate checksum
    let checksum = crc32(&compressed);

    // Create trailer
    let trailer = Trailer::new(
        stub_size as u64,
        payload_size as u64,
        original_size as u64,
        checksum,
    );

    // Write output file
    let mut output_file =
        fs::File::create(output).map_err(|e| format!("Failed to create output file: {}", e))?;

    // Write stub
    output_file
        .write_all(&stub)
        .map_err(|e| format!("Failed to write stub: {}", e))?;

    // Write compressed payload
    output_file
        .write_all(&compressed)
        .map_err(|e| format!("Failed to write payload: {}", e))?;

    // Write trailer
    output_file
        .write_all(&trailer.to_bytes())
        .map_err(|e| format!("Failed to write trailer: {}", e))?;

    // Set executable permissions on Unix
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = output_file
            .metadata()
            .map_err(|e| format!("Failed to get output file metadata: {}", e))?
            .permissions();
        perms.set_mode(0o755);
        fs::set_permissions(output, perms)
            .map_err(|e| format!("Failed to set executable permissions: {}", e))?;
    }

    let total_size = stub_size + payload_size + TRAILER_SIZE;
    let ratio = original_size as f64 / total_size as f64;

    eprintln!(
        "Created self-extracting executable: {} bytes ({}x compression including stub)",
        total_size, ratio
    );

    Ok(ratio)
}

/// Get compression ratio of a self-extracting executable
///
/// Returns: original_size / total_size
pub fn get_compression_ratio(path: &Path) -> Result<f64, String> {
    use crate::compress::lzma_stub::read_trailer;

    let trailer = read_trailer(path)?;

    let total_size = trailer.stub_size + trailer.payload_size + TRAILER_SIZE as u64;
    let ratio = trailer.original_size as f64 / total_size as f64;

    Ok(ratio)
}

/// Check if creating a self-extracting version would save space
///
/// Returns true if self-extracting would be smaller than original
pub fn is_worth_compressing(input: &Path) -> Result<bool, String> {
    let original = fs::read(input).map_err(|e| format!("Failed to read input file: {}", e))?;
    let original_size = original.len();

    // Quick test: compress a sample
    let sample_size = original_size.min(1024 * 1024); // First 1 MB
    let compressed = compress_lzma(&original[..sample_size], LzmaLevel::Normal)?;

    // Estimate total size
    let compression_ratio = sample_size as f64 / compressed.len() as f64;
    let estimated_compressed = (original_size as f64 / compression_ratio) as usize;

    // Get stub size (if available)
    let stub_size = match get_stub_binary() {
        Ok(stub) => stub.len(),
        Err(_) => 40 * 1024, // Estimate 40 KB
    };

    let estimated_total = stub_size + estimated_compressed + TRAILER_SIZE;

    Ok(estimated_total < original_size)
}

/// Create self-extracting executable with auto-level selection
///
/// Tries different compression levels and picks the best one
pub fn create_self_extracting_auto(input: &Path, output: &Path) -> Result<f64, String> {
    let levels = [LzmaLevel::Fast, LzmaLevel::Normal, LzmaLevel::Best];

    let mut best_ratio = 0.0;
    let mut best_level = LzmaLevel::Normal;

    // Quick test with small sample
    let original = fs::read(input).map_err(|e| format!("Failed to read input file: {}", e))?;
    let sample_size = original.len().min(256 * 1024); // 256 KB sample

    for &level in &levels {
        let compressed = compress_lzma(&original[..sample_size], level)?;
        let ratio = sample_size as f64 / compressed.len() as f64;

        if ratio > best_ratio {
            best_ratio = ratio;
            best_level = level;
        }
    }

    eprintln!("Auto-selected compression level: {:?}", best_level);

    create_self_extracting(input, output, best_level)
}

// ============================================================================
// FFI Bindings for Simple
// ============================================================================

/// FFI: Create a self-extracting executable
///
/// # Safety
/// - `input` and `output` must be valid null-terminated C strings
/// - `level` should be 1 (fast), 6 (normal), or 9 (best)
/// - Returns 0 on success, -1 on failure
#[no_mangle]
pub unsafe extern "C" fn self_extract_create(
    input: *const c_char,
    output: *const c_char,
    level: i32,
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

    let lzma_level = LzmaLevel::from_i32(level).unwrap_or(LzmaLevel::Normal);

    match create_self_extracting(Path::new(input_str), Path::new(output_str), lzma_level) {
        Ok(_) => 0,
        Err(e) => {
            eprintln!("Self-extract creation failed: {}", e);
            -1
        }
    }
}

/// FFI: Check if a file is a self-extracting executable
///
/// # Safety
/// - `file` must be a valid null-terminated C string
/// - Returns 1 if self-extracting, 0 if not, -1 on error
#[no_mangle]
pub unsafe extern "C" fn self_extract_is_compressed(file: *const c_char) -> i32 {
    if file.is_null() {
        return -1;
    }

    let file_str = match CStr::from_ptr(file).to_str() {
        Ok(s) => s,
        Err(_) => return -1,
    };

    match crate::compress::lzma_stub::is_self_extracting(Path::new(file_str)) {
        Ok(true) => 1,
        Ok(false) => 0,
        Err(_) => -1,
    }
}

/// FFI: Get compression ratio of a self-extracting executable
///
/// # Safety
/// - `file` must be a valid null-terminated C string
/// - Returns ratio as f64, or -1.0 on error
#[no_mangle]
pub unsafe extern "C" fn self_extract_get_ratio(file: *const c_char) -> f64 {
    if file.is_null() {
        return -1.0;
    }

    let file_str = match CStr::from_ptr(file).to_str() {
        Ok(s) => s,
        Err(_) => return -1.0,
    };

    match get_compression_ratio(Path::new(file_str)) {
        Ok(ratio) => ratio,
        Err(_) => -1.0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lzma_level() {
        assert_eq!(LzmaLevel::from_i32(1), Some(LzmaLevel::Fast));
        assert_eq!(LzmaLevel::from_i32(6), Some(LzmaLevel::Normal));
        assert_eq!(LzmaLevel::from_i32(9), Some(LzmaLevel::Best));
        assert_eq!(LzmaLevel::from_i32(5), None);
    }

    #[test]
    fn test_crc32() {
        let data = b"Hello, World!";
        let crc = crc32(data);

        // Known CRC32 for "Hello, World!"
        assert_eq!(crc, 0xec4ac3d0);
    }

    #[test]
    fn test_compress_lzma() {
        let data = b"Hello, World! ".repeat(100);
        let compressed = compress_lzma(&data, LzmaLevel::Normal);

        assert!(compressed.is_ok());
        let compressed = compressed.unwrap();
        assert!(compressed.len() < data.len());

        println!(
            "Compressed {} -> {} bytes ({}x)",
            data.len(),
            compressed.len(),
            data.len() as f64 / compressed.len() as f64
        );
    }

    #[test]
    fn test_compress_lzma_levels() {
        let data = b"The quick brown fox jumps over the lazy dog. ".repeat(1000);

        let fast = compress_lzma(&data, LzmaLevel::Fast).unwrap();
        let normal = compress_lzma(&data, LzmaLevel::Normal).unwrap();
        let best = compress_lzma(&data, LzmaLevel::Best).unwrap();

        // Best should be smallest (or equal)
        assert!(best.len() <= normal.len());
        assert!(normal.len() <= fast.len());

        println!("Fast: {} bytes", fast.len());
        println!("Normal: {} bytes", normal.len());
        println!("Best: {} bytes", best.len());
    }
}
