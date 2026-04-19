//! Lint checker — split into focused submodules for maintainability.
//!
//! - `checker_core`: struct, helpers, emit, directives, check_module, collect_functions
//! - `checker_annotations`: decorator/attribute whitelist checks
//! - `checker_types`: public-API type checks (bare bool, primitive, per-node dispatch)
//! - `checker_sspec`: SSpec quality, TODO format, placeholder/stub detection
//! - `checker_args`: unnamed-duplicate-typed-args call-site check
//! - `checker_resources`: resource leaks, init-boundary, bypass validity, too-many-args

mod checker_annotations;
mod checker_args;
mod checker_core;
mod checker_resources;
mod checker_sspec;
mod checker_types;

pub use checker_core::LintChecker;
