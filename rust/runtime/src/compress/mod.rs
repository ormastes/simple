//! Compression utilities module
//!
//! Provides compression/decompression functionality including:
//! - UPX executable compression
//! - Automatic UPX download and caching

pub mod upx;
pub mod upx_download;

// Re-export main types
pub use upx::{CompressionLevel, compress_file, decompress_file, is_compressed, is_upx_available};
pub use upx_download::{ensure_upx_available, find_upx_binary, download_upx};
