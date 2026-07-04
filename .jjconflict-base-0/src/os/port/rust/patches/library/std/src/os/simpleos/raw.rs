//! SimpleOS-specific raw type definitions.
//!
//! These aliases mirror what `libsimpleos_c` exposes through `<sys/stat.h>`
//! and `<sys/types.h>`. They are intentionally minimal — only the types
//! referenced by `sys::pal::simpleos::fs` are surfaced here. If the PAL
//! grows new syscalls (e.g. `getdents`, `statfs`) add the corresponding
//! aliases below rather than re-exporting libc wholesale.

#![stable(feature = "raw_ext", since = "1.1.0")]
#![deprecated(
    since = "1.8.0",
    note = "these type aliases are no longer supported by the standard library, \
            the `libc` crate on crates.io should be used instead for the correct \
            definitions"
)]
#![allow(deprecated)]

#[stable(feature = "raw_ext", since = "1.1.0")]
pub type dev_t = u64;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type ino_t = u64;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type mode_t = u32;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type nlink_t = u64;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type uid_t = u32;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type gid_t = u32;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type off_t = i64;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type blkcnt_t = i64;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type blksize_t = i64;
#[stable(feature = "raw_ext", since = "1.1.0")]
pub type time_t = i64;

/// Nanosecond-granular time value. Matches POSIX `struct timespec`.
#[repr(C)]
#[derive(Clone)]
#[stable(feature = "raw_ext", since = "1.1.0")]
pub struct timespec {
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub tv_sec: time_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub tv_nsec: i64,
}

/// POSIX `struct stat` as exposed by `libsimpleos_c`. Field order and
/// widths must match the C layout exactly.
#[repr(C)]
#[derive(Clone)]
#[stable(feature = "raw_ext", since = "1.1.0")]
pub struct stat {
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_dev: dev_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_ino: ino_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_mode: mode_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_nlink: nlink_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_uid: uid_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_gid: gid_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_rdev: dev_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_size: off_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_blksize: blksize_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_blocks: blkcnt_t,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_atime: timespec,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_mtime: timespec,
    #[stable(feature = "raw_ext", since = "1.1.0")]
    pub st_ctime: timespec,
}
