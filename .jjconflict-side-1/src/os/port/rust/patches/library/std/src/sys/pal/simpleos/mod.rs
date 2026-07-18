//! Platform abstraction layer for the `simpleos` target family.
//!
//! Hosts a freestanding-ish libstd on top of `libsimpleos_c`. Only the
//! primitives libsimpleos_c currently exports are wired to real externs;
//! everything else returns `ErrorKind::Unsupported`.

#![allow(dead_code)]
#![allow(missing_docs)]

pub mod alloc;
pub mod args;
pub mod env;
pub mod exit;
pub mod fs;
pub mod io;
pub mod net;
pub mod pipe;
pub mod process;
pub mod stdio;
pub mod thread;
pub mod time;

pub use self::exit::exit;

// Re-export unsupported shims for areas SimpleOS does not yet model.
#[path = "../unsupported/common.rs"]
pub mod common;
#[path = "../unsupported/os.rs"]
pub mod os;
#[path = "../unsupported/thread_local_key.rs"]
pub mod thread_local_key;
#[path = "../unsupported/thread_parking.rs"]
pub mod thread_parking;

pub use self::common::{abort_internal, decode_error_kind, hashmap_random_keys, is_interrupted};

/// Early init hook. SimpleOS `_start` passes `(argc, argv)` into libstd through
/// `args::init`; other subsystems currently need no setup.
///
/// # Safety
/// Must be called exactly once from the runtime entry point before any libstd
/// function that reads command-line arguments.
pub unsafe fn init(argc: isize, argv: *const *const u8, _sigpipe: u8) {
    unsafe { args::init(argc, argv) }
}

pub unsafe fn cleanup() {}
