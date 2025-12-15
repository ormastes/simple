//! Module import loading and resolution utilities.

// Re-export from pipeline module
pub(crate) use crate::pipeline::script_detection::has_script_statements;
pub(crate) use crate::pipeline::module_loader::load_module_with_imports;
