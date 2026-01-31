//! HIR analysis passes
//!
//! This module contains various analysis passes for the HIR:
//! - Ghost code purity checking (VER-001)

pub mod ghost_checker;

pub use ghost_checker::{GhostAnalysisResult, GhostChecker, GhostError, GhostErrorKind, GhostWarning};
