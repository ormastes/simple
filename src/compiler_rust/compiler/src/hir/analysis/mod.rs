//! HIR analysis passes
//!
//! This module contains various analysis passes for the HIR:
//! - Ghost code purity checking (VER-001)

pub mod ghost_checker;
pub mod unsafe_ffi_checker;

pub use ghost_checker::{GhostAnalysisResult, GhostChecker, GhostError, GhostErrorKind, GhostWarning};
pub use unsafe_ffi_checker::{check_unsafe_ffi, unsafe_ffi_deny_enabled, UnsafeFfiViolation};
