//! Module loading and resolution for the Simple interpreter.
//!
//! This module is organized into focused submodules:
//! - `path_resolution`: Resolving module paths from import statements
//! - `module_loader`: Loading and parsing module files
//! - `module_evaluator`: Evaluating module statements and collecting exports
//! - `export_handler`: Handling re-export statements
//! - `module_merger`: Merging module definitions into global state
//!
//! All public functions are re-exported for backward compatibility.

// Import module cache from parent
use super::module_cache;

// Submodules
mod export_handler;
mod module_evaluator;
mod module_loader;
mod module_merger;
mod path_resolution;

// Note: evaluation_helpers is a private submodule of module_evaluator

// Re-export public functions for backward compatibility
pub use module_evaluator::evaluate_module_exports;
pub use module_loader::{get_import_alias, load_and_merge_module};
pub use module_merger::merge_module_definitions;
pub use path_resolution::resolve_module_path;
