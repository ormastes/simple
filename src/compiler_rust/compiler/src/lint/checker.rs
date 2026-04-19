//! Lint checker — split into focused submodules for maintainability.
//!
//! - `checker_core`: struct, helpers, emit, directives, check_module, collect_functions
//! - `checker_annotations`: decorator/attribute whitelist checks
//! - `checker_types`: public-API type checks (bare bool, primitive, per-node dispatch)
//! - `checker_sspec`: SSpec quality, TODO format, placeholder/stub detection
//! - `checker_args`: unnamed-duplicate-typed-args call-site check
//! - `checker_resources`: resource leaks, init-boundary, bypass validity, too-many-args

#[path = "checker_annotations.rs"]
mod checker_annotations;
#[path = "checker_args.rs"]
mod checker_args;
#[path = "checker_core.rs"]
mod checker_core;
#[path = "checker_resources.rs"]
mod checker_resources;
#[path = "checker_sspec.rs"]
mod checker_sspec;
#[path = "checker_types.rs"]
mod checker_types;

pub use checker_core::LintChecker;
