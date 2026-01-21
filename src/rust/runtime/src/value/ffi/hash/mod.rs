//! Hash function FFI modules.
//!
//! Provides cryptographic and non-cryptographic hash functions for compiled Simple code.
//!
//! ## Available Hash Functions
//!
//! - **SHA1** (`sha1`) - 160-bit cryptographic hash (deprecated for security, use SHA256)
//! - **SHA256** (`sha256`) - 256-bit cryptographic hash (recommended for security)
//! - **XXHash** (`xxhash`) - Fast non-cryptographic hash (recommended for hash tables)
//!
//! ## Usage Pattern
//!
//! All hash functions follow the same pattern:
//! 1. Create a hasher: `rt_xxx_new()`
//! 2. Write data: `rt_xxx_write(handle, data, len)`
//! 3. Finalize: `rt_xxx_finish(handle)` or `rt_xxx_finish_bytes(handle)`
//!
//! Optional operations:
//! - Reset: `rt_xxx_reset(handle)` - Reuse the hasher
//! - Free: `rt_xxx_free(handle)` - Clean up resources

pub mod sha1;
pub mod sha256;
pub mod xxhash;

// Re-export all hash functions
pub use sha1::*;
pub use sha256::*;
pub use xxhash::*;
