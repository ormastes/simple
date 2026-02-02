//! LZMA decompressor stub for self-extracting executables
//!
//! This module builds a minimal standalone binary that can decompress
//! and execute LZMA-compressed payloads embedded in self-extracting executables.
//!
//! Binary format:
//! ```
//! ┌──────────────────────────┐
//! │ Decompressor Stub (~40KB)│ ← This code, compiled
//! ├──────────────────────────┤
//! │ Compressed Payload       │ ← LZMA-compressed original binary
//! ├──────────────────────────┤
//! │ Trailer (32 bytes)       │ ← Metadata
//! │   - magic: [u8; 4]       │   "SPLX"
//! │   - stub_size: u64       │   Offset to payload
//! │   - payload_size: u64    │   Compressed size
//! │   - original_size: u64   │   Uncompressed size
//! │   - checksum: u32        │   CRC32 of payload
//! │   - reserved: u32        │   Future use
//! └──────────────────────────┘
//! ```

use std::fs;
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;

/// Magic number for self-extracting executables: "SPLX"
pub const MAGIC: [u8; 4] = *b"SPLX";

/// Size of the trailer in bytes
pub const TRAILER_SIZE: usize = 32;

/// Trailer structure at the end of self-extracting binaries
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Trailer {
    /// Magic number: "SPLX"
    pub magic: [u8; 4],
    /// Size of the decompressor stub
    pub stub_size: u64,
    /// Size of compressed payload
    pub payload_size: u64,
    /// Size of original (uncompressed) binary
    pub original_size: u64,
    /// CRC32 checksum of compressed payload
    pub checksum: u32,
    /// Reserved for future use
    pub reserved: u32,
}

impl Trailer {
    /// Parse trailer from bytes
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() != TRAILER_SIZE {
            return Err(format!(
                "Invalid trailer size: expected {}, got {}",
                TRAILER_SIZE,
                bytes.len()
            ));
        }

        let mut magic = [0u8; 4];
        magic.copy_from_slice(&bytes[0..4]);

        if magic != MAGIC {
            return Err(format!("Invalid magic: expected {:?}, got {:?}", MAGIC, magic));
        }

        let stub_size = u64::from_le_bytes([
            bytes[4], bytes[5], bytes[6], bytes[7], bytes[8], bytes[9], bytes[10], bytes[11],
        ]);
        let payload_size = u64::from_le_bytes([
            bytes[12], bytes[13], bytes[14], bytes[15], bytes[16], bytes[17], bytes[18], bytes[19],
        ]);
        let original_size = u64::from_le_bytes([
            bytes[20], bytes[21], bytes[22], bytes[23], bytes[24], bytes[25], bytes[26], bytes[27],
        ]);
        let checksum = u32::from_le_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]);

        Ok(Trailer {
            magic,
            stub_size,
            payload_size,
            original_size,
            checksum,
            reserved: 0,
        })
    }

    /// Serialize trailer to bytes
    pub fn to_bytes(&self) -> [u8; TRAILER_SIZE] {
        let mut bytes = [0u8; TRAILER_SIZE];

        bytes[0..4].copy_from_slice(&self.magic);
        bytes[4..12].copy_from_slice(&self.stub_size.to_le_bytes());
        bytes[12..20].copy_from_slice(&self.payload_size.to_le_bytes());
        bytes[20..28].copy_from_slice(&self.original_size.to_le_bytes());
        bytes[28..32].copy_from_slice(&self.checksum.to_le_bytes());

        bytes
    }

    /// Create a new trailer
    pub fn new(stub_size: u64, payload_size: u64, original_size: u64, checksum: u32) -> Self {
        Trailer {
            magic: MAGIC,
            stub_size,
            payload_size,
            original_size,
            checksum,
            reserved: 0,
        }
    }
}

/// Check if a file is a self-extracting executable
pub fn is_self_extracting(path: &Path) -> Result<bool, String> {
    let mut file = fs::File::open(path).map_err(|e| format!("Failed to open file: {}", e))?;

    let file_size = file
        .metadata()
        .map_err(|e| format!("Failed to get file metadata: {}", e))?
        .len();

    if file_size < TRAILER_SIZE as u64 {
        return Ok(false);
    }

    // Read trailer
    file.seek(SeekFrom::End(-(TRAILER_SIZE as i64)))
        .map_err(|e| format!("Failed to seek to trailer: {}", e))?;

    let mut trailer_bytes = [0u8; TRAILER_SIZE];
    file.read_exact(&mut trailer_bytes)
        .map_err(|e| format!("Failed to read trailer: {}", e))?;

    // Check magic
    Ok(trailer_bytes[0..4] == MAGIC)
}

/// Read trailer from a self-extracting executable
pub fn read_trailer(path: &Path) -> Result<Trailer, String> {
    let mut file = fs::File::open(path).map_err(|e| format!("Failed to open file: {}", e))?;

    let file_size = file
        .metadata()
        .map_err(|e| format!("Failed to get file metadata: {}", e))?
        .len();

    if file_size < TRAILER_SIZE as u64 {
        return Err("File too small to contain trailer".to_string());
    }

    // Read trailer
    file.seek(SeekFrom::End(-(TRAILER_SIZE as i64)))
        .map_err(|e| format!("Failed to seek to trailer: {}", e))?;

    let mut trailer_bytes = [0u8; TRAILER_SIZE];
    file.read_exact(&mut trailer_bytes)
        .map_err(|e| format!("Failed to read trailer: {}", e))?;

    Trailer::from_bytes(&trailer_bytes)
}

/// Extract payload from self-extracting executable
pub fn extract_payload(path: &Path, trailer: &Trailer) -> Result<Vec<u8>, String> {
    let mut file = fs::File::open(path).map_err(|e| format!("Failed to open file: {}", e))?;

    // Seek to payload (after stub)
    file.seek(SeekFrom::Start(trailer.stub_size))
        .map_err(|e| format!("Failed to seek to payload: {}", e))?;

    // Read compressed payload
    let mut compressed = vec![0u8; trailer.payload_size as usize];
    file.read_exact(&mut compressed)
        .map_err(|e| format!("Failed to read payload: {}", e))?;

    // Verify checksum
    let actual_checksum = crc32(&compressed);
    if actual_checksum != trailer.checksum {
        return Err(format!(
            "Checksum mismatch: expected {}, got {}",
            trailer.checksum, actual_checksum
        ));
    }

    Ok(compressed)
}

/// Decompress LZMA payload
pub fn decompress_lzma(compressed: &[u8], expected_size: usize) -> Result<Vec<u8>, String> {
    use xz2::read::XzDecoder;

    let mut decoder = XzDecoder::new(compressed);
    let mut decompressed = Vec::with_capacity(expected_size);

    decoder
        .read_to_end(&mut decompressed)
        .map_err(|e| format!("LZMA decompression failed: {}", e))?;

    if decompressed.len() != expected_size {
        return Err(format!(
            "Decompressed size mismatch: expected {}, got {}",
            expected_size,
            decompressed.len()
        ));
    }

    Ok(decompressed)
}

/// Extract and decompress payload from self-extracting executable
pub fn extract_and_decompress(path: &Path) -> Result<Vec<u8>, String> {
    let trailer = read_trailer(path)?;
    let compressed = extract_payload(path, &trailer)?;
    decompress_lzma(&compressed, trailer.original_size as usize)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trailer_roundtrip() {
        let trailer = Trailer::new(1024, 2048, 4096, 0x12345678);
        let bytes = trailer.to_bytes();

        assert_eq!(bytes.len(), TRAILER_SIZE);
        assert_eq!(&bytes[0..4], b"SPLX");

        let parsed = Trailer::from_bytes(&bytes).unwrap();
        assert_eq!(parsed.stub_size, 1024);
        assert_eq!(parsed.payload_size, 2048);
        assert_eq!(parsed.original_size, 4096);
        assert_eq!(parsed.checksum, 0x12345678);
    }

    #[test]
    fn test_trailer_invalid_magic() {
        let mut bytes = [0u8; TRAILER_SIZE];
        bytes[0..4].copy_from_slice(b"XXXX");

        let result = Trailer::from_bytes(&bytes);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Invalid magic"));
    }

    #[test]
    fn test_crc32() {
        let data = b"Hello, World!";
        let crc = crc32(data);

        // Known CRC32 for "Hello, World!"
        assert_eq!(crc, 0xec4ac3d0);
    }

    #[test]
    fn test_crc32_empty() {
        let data = b"";
        let crc = crc32(data);

        // CRC32 of empty data
        assert_eq!(crc, 0x00000000);
    }
}
