//! Lint checker — thin dispatcher that re-exports LintChecker from submodules.
//!
//! #![skip_todo]

#[path = "checker_core.rs"]
mod checker_core;

#[path = "checker_annotations.rs"]
mod checker_annotations;

#[path = "checker_types.rs"]
mod checker_types;

#[path = "checker_sspec.rs"]
mod checker_sspec;

#[path = "checker_args.rs"]
mod checker_args;

#[path = "checker_resources.rs"]
mod checker_resources;

pub use checker_core::LintChecker;
