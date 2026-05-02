//! Code migration commands for Simple language.
//!
//! Provides automated migration tools for syntax changes and deprecations.
//!
//! ## Module Structure
//!
//! - `cli`: Command-line interface and help system
//! - `file_walker`: File discovery and summary utilities
//! - `generics`: Generic syntax migration ([] → <>)
//! - `print`: Print/println syntax migration
//! - `spipe`: SPipe test migration (print-based → docstrings)

pub mod cli;
pub mod file_walker;
pub mod generics;
pub mod print;
pub mod spipe;

// Re-export main entry point for backward compatibility
pub use cli::run_migrate;

// Re-export migration functions for backward compatibility
pub use generics::migrate_generics;
pub use print::migrate_print_syntax;
pub use spipe::{migrate_file_spipe, migrate_spipe_docstrings};
