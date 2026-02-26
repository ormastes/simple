//! Compression support for SMF bytecode sections.
//!
//! Supports transparent compression/decompression of section data.
//! Currently only "none" is implemented. Zstd and LZ4 are defined
//! but require adding the corresponding crate dependencies.

use std::io;

/// Compression method identifier (matches SMF header `compression` field).
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompressionMethod {
    /// No compression.
    None = 0,
    /// Zstd compression (requires `zstd` crate).
    Zstd = 1,
    /// LZ4 compression (requires `lz4` crate).
    Lz4 = 2,
}

impl CompressionMethod {
    /// Parse from the raw header byte.
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(CompressionMethod::None),
            1 => Some(CompressionMethod::Zstd),
            2 => Some(CompressionMethod::Lz4),
            _ => None,
        }
    }
}

/// Compress data using the specified method.
pub fn compress(data: &[u8], method: CompressionMethod, _level: u8) -> io::Result<Vec<u8>> {
    match method {
        CompressionMethod::None => Ok(data.to_vec()),
        CompressionMethod::Zstd => Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "Zstd compression not yet available (add `zstd` dependency)",
        )),
        CompressionMethod::Lz4 => Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "LZ4 compression not yet available (add `lz4` dependency)",
        )),
    }
}

/// Decompress data using the specified method.
pub fn decompress(data: &[u8], method: CompressionMethod) -> io::Result<Vec<u8>> {
    match method {
        CompressionMethod::None => Ok(data.to_vec()),
        CompressionMethod::Zstd => Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "Zstd decompression not yet available (add `zstd` dependency)",
        )),
        CompressionMethod::Lz4 => Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "LZ4 decompression not yet available (add `lz4` dependency)",
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compression_none_roundtrip() {
        let data = b"Hello, bytecode world!";
        let compressed = compress(data, CompressionMethod::None, 0).unwrap();
        assert_eq!(compressed, data);
        let decompressed = decompress(&compressed, CompressionMethod::None).unwrap();
        assert_eq!(decompressed, data);
    }

    #[test]
    fn test_compression_method_from_u8() {
        assert_eq!(CompressionMethod::from_u8(0), Some(CompressionMethod::None));
        assert_eq!(CompressionMethod::from_u8(1), Some(CompressionMethod::Zstd));
        assert_eq!(CompressionMethod::from_u8(2), Some(CompressionMethod::Lz4));
        assert_eq!(CompressionMethod::from_u8(255), None);
    }

    #[test]
    fn test_zstd_not_available() {
        let result = compress(b"test", CompressionMethod::Zstd, 3);
        assert!(result.is_err());
    }
}
