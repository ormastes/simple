//! Platform abstraction layer for the Simple compiler.
//!
//! Provides cross-platform wrappers over std::fs, std::process, std::env
//! for use by the compiler binary itself (not for compiled programs).

pub mod dir;
pub mod env;
pub mod fs;
pub mod path;
pub mod process;
pub mod sysroot;
pub mod time;

use crate::target::{Target, TargetArch, TargetOS};

/// Information about the host platform.
#[derive(Debug, Clone)]
pub struct PlatformInfo {
    pub os: TargetOS,
    pub arch: TargetArch,
    pub is_little_endian: bool,
    pub pointer_size: usize,
}

impl PlatformInfo {
    /// Detect the host platform.
    pub fn detect_host() -> Self {
        let target = Target::host();
        let config = target.config();
        Self {
            os: target.os,
            arch: target.arch,
            is_little_endian: config.is_little_endian,
            pointer_size: config.pointer_bytes,
        }
    }
}

/// Detect the host platform information.
pub fn detect_host() -> PlatformInfo {
    PlatformInfo::detect_host()
}
