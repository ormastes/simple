//! SimpleOS-specific definitions.
//!
//! This module mirrors `std::os::hermit` in shape: it exposes the
//! SimpleOS-flavoured extension traits for `OsStr`/`OsString` plus the
//! raw-POSIX type aliases that SimpleOS's libc surfaces.
//!
//! SimpleOS treats `OsStr` as a bag of bytes (the kernel and FAT32 layer
//! both operate on raw `&[u8]` paths), so the extension traits here are
//! identical in spirit to `std::os::unix::ffi`.

#![stable(feature = "rustc_private", since = "1.0.0")]

pub mod ffi;
pub mod raw;
