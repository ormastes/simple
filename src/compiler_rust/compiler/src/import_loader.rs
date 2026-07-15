//! Module import loading and resolution utilities.

// Re-export from pipeline module
pub use crate::pipeline::module_loader::{collect_direct_imported_module_paths, collect_imported_module_paths};
pub(crate) use crate::pipeline::module_loader::{load_module_with_imports, load_module_with_imports_for_target};
pub(crate) use crate::pipeline::script_detection::has_script_statements;
