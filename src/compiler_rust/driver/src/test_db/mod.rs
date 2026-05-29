//! Test execution database - tracks test results and timing.
//!
//! V3 format: Tree structure + string interning + split stable/volatile files.
//!
//! - `test_db.sdn` — stable data (strings, files, suites, tests) tracked in jj
//! - `test_db_runs.sdn` — volatile data (timing, runs, changes) jj-ignored
//!
//! Auto-generates: doc/test/test_result.md

pub mod types;
pub mod run_record;
pub mod runs;
pub mod loader;
pub mod saver;
pub mod update;
pub mod docs;
#[cfg(test)]
mod tests;

// Re-export all public items so existing `use crate::test_db::*` paths work unchanged.
pub use types::*;
pub use run_record::*;
pub use runs::*;
pub use loader::load_test_db;
pub use saver::save_test_db;
pub use update::update_test_result;
pub use docs::*;
