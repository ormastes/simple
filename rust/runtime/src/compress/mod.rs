//! Compression utilities module
//!
//! Provides compression/decompression functionality including:
//! - UPX executable compression
//! - Automatic UPX download and caching
//! - Self-extracting executables (LZMA-based)

pub mod upx;
pub mod upx_download;
pub mod lzma_stub;
pub mod self_extract;

// Re-export main types
pub use upx::{CompressionLevel, compress_file, decompress_file, is_compressed, is_upx_available};
pub use upx_download::{ensure_upx_available, find_upx_binary, download_upx};
pub use lzma_stub::{is_self_extracting, read_trailer, Trailer};
pub use self_extract::{create_self_extracting, get_compression_ratio as get_self_extract_ratio};
