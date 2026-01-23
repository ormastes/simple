//! Test runner CLI command for Simple language.
//!
//! Provides a unified test runner that discovers and executes tests
//! in the BDD spec format (*_spec.spl, *_test.spl).
//!
//! # Module Structure
//!
//! - `types` - Core data structures (TestOptions, TestRunResult, etc.)
//! - `execution` - Test file execution logic
//! - `doctest` - Doctest discovery and running
//! - `runner` - Main test orchestration
//! - `args` - Command-line argument parsing
//! - `diagrams` - Diagram generation from test runs
//! - `watch` - Watch mode for automatic re-running
//! - `discovery` - Test discovery and summarization
//! - `coverage` - Coverage tracking utilities
//! - `feature_db` - Feature database updates
//! - `test_db_update` - Test database updates
//! - `static_registry` - Static test metadata for fast queries

mod types;
mod execution;
mod doctest;
mod runner;
mod args;
mod diagrams;
mod watch;
mod discovery;
mod coverage;
mod feature_db;
mod test_db_update;
mod cpu_monitor;
mod parallel;
pub mod static_registry;

// Re-export public API for backward compatibility
pub use types::{TestLevel, OutputFormat, TestOptions, TestFileResult, TestRunResult};
pub use execution::{parse_test_output, run_test_file};
pub use runner::run_tests;
pub use args::parse_test_args;
pub use watch::watch_tests;
pub use static_registry::StaticTestRegistry;

// Re-export from parent modules
use super::test_discovery;
use super::test_output;
pub use super::test_output::print_summary;
