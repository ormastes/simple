//! Compression utilities module
//!
//! Provides compression/decompression functionality including:
//! - UPX executable compression

pub mod upx;

// Re-export main types
pub use upx::{CompressionLevel, compress_file, decompress_file, is_compressed, is_upx_available};
