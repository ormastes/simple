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
pub use path_resolution::{resolve_module_path, clear_path_resolution_cache};

use std::collections::HashMap;
use simple_parser::ast::{ClassDef, FunctionDef, ImportTarget};
use crate::error::CompileError;
use crate::value::{Env, Value};

type Enums = HashMap<String, simple_parser::ast::EnumDef>;

/// Try loading deferred (lazy) modules until the requested symbol is found.
/// Returns Ok(true) if a module was loaded and may contain the symbol.
pub fn try_force_deferred_for(
    symbol_name: &str,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &mut Enums,
) -> Result<bool, CompileError> {
    // Take all deferred modules out (to avoid borrow conflict)
    let deferred: Vec<crate::interpreter::DeferredModule> =
        crate::interpreter::DEFERRED_MODULES.with(|cell| {
            std::mem::take(&mut *cell.borrow_mut())
        });

    if deferred.is_empty() {
        return Ok(false);
    }

    let mut remaining = Vec::new();
    let mut found = false;

    for dm in deferred {
        if found {
            // Already found the symbol, keep remaining modules deferred
            remaining.push(dm);
            continue;
        }

        // Force-load this module
        let module_path = dm.module_path.as_deref();
        let mut use_stmt = dm.use_stmt.clone();
        use_stmt.is_lazy = false; // prevent re-deferral

        match load_and_merge_module(&use_stmt, module_path, functions, classes, enums) {
            Ok(value) => {
                // Merge exports into env
                if let Value::Dict(exports) = &value {
                    for (name, export_value) in exports {
                        env.insert(name.clone(), export_value.clone());
                    }
                }

                let binding_name = match &use_stmt.target {
                    ImportTarget::Single(name) => name.clone(),
                    ImportTarget::Aliased { alias, .. } => alias.clone(),
                    ImportTarget::Glob | ImportTarget::Group(_) => use_stmt
                        .path
                        .segments
                        .last()
                        .cloned()
                        .unwrap_or_else(|| "module".to_string()),
                };

                match &use_stmt.target {
                    ImportTarget::Glob => {
                        if let Value::Dict(exports) = &value {
                            if !exports.contains_key(&binding_name) {
                                env.insert(binding_name, value);
                            }
                        }
                    }
                    _ => {
                        env.insert(binding_name, value);
                    }
                }

                // Check if we found the symbol
                if functions.contains_key(symbol_name) || classes.contains_key(symbol_name)
                    || env.get(symbol_name).is_some()
                {
                    found = true;
                }
            }
            Err(_) => {
                // Loading failed, discard this deferred entry
            }
        }
    }

    // Put back any remaining deferred modules
    if !remaining.is_empty() {
        crate::interpreter::DEFERRED_MODULES.with(|cell| {
            cell.borrow_mut().extend(remaining);
        });
    }

    Ok(found)
}
