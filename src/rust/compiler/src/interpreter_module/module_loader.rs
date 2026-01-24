//! Module loading functionality for the Simple interpreter.
//!
//! This module handles loading and parsing module files, managing circular imports,
//! and caching module exports.

use std::collections::HashMap;
use std::fs;
use std::path::Path;

use tracing::{debug, error, trace, warn, instrument};

use simple_parser::ast::{ClassDef, EnumDef, ImportTarget, UseStmt};

use crate::error::CompileError;
use crate::value::{Env, Value};

use super::module_cache::{
    cache_module_exports, decrement_load_depth, get_cached_module_exports, increment_load_depth, is_module_loading,
    mark_module_loading, unmark_module_loading, MAX_MODULE_DEPTH,
};
use super::module_evaluator::evaluate_module_exports;
use super::path_resolution::resolve_module_path;

type Enums = HashMap<String, EnumDef>;

/// Get the import alias from a UseStmt if it exists
pub fn get_import_alias(use_stmt: &UseStmt) -> Option<String> {
    match &use_stmt.target {
        ImportTarget::Aliased { alias, .. } => Some(alias.clone()),
        _ => None,
    }
}

/// Load a module file, evaluate it, and return exports with captured environment
/// This is needed so that module-level imports are accessible in exported functions
#[instrument(skip(use_stmt, current_file, functions, classes, enums), fields(path = ?use_stmt.path.segments))]
pub fn load_and_merge_module(
    use_stmt: &UseStmt,
    current_file: Option<&Path>,
    functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &mut Enums,
) -> Result<Value, CompileError> {
    // Check depth limit to prevent infinite recursion
    let depth = increment_load_depth();
    if depth > MAX_MODULE_DEPTH {
        decrement_load_depth();
        error!(depth, max = MAX_MODULE_DEPTH, "Module import depth exceeded");
        return Err(CompileError::Runtime(format!(
            "Maximum module import depth ({}) exceeded. Possible circular import or very deep module hierarchy.",
            MAX_MODULE_DEPTH
        )));
    }

    // Build module path from segments (path only, not the import target)
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    debug!(parts = ?parts, target = ?use_stmt.target, depth, "Loading module");

    // Handle the case where path is empty but target contains the module name
    // e.g., `import spec as sp` has path=[], target=Aliased { name: "spec", alias: "sp" }
    // In this case, "spec" is the module path, not an item to extract from a module
    let import_item_name: Option<String> = if parts.is_empty() {
        match &use_stmt.target {
            ImportTarget::Single(name) => {
                // `import spec` - name is the module path
                parts.push(name.clone());
                None // Import whole module
            }
            ImportTarget::Aliased { name, .. } => {
                // `import spec as sp` - name is the module path
                parts.push(name.clone());
                None // Import whole module (aliased)
            }
            ImportTarget::Glob => {
                // Glob with empty path is invalid - can't do `import *` with no module
                warn!("Glob import with empty path - skipping");
                decrement_load_depth();
                return Ok(Value::Dict(HashMap::new()));
            }
            ImportTarget::Group(items) => {
                // Group import with empty path: import {X, Y, Z}
                // This is invalid - need a module to import from
                warn!("Group import with empty path - skipping");
                decrement_load_depth();
                return Ok(Value::Dict(HashMap::new()));
            }
        }
    } else {
        // Path is not empty - the target 'name' is the final component of the module path
        match &use_stmt.target {
            ImportTarget::Single(name) => {
                // `import X.Y.Z` - import the whole module X.Y.Z, bind to "Z"
                // The target 'name' is the final component of the module path.
                // e.g., `import verification.lean.types`:
                //   - Parser produces: path=["verification", "lean"], name="types"
                //   - We need: parts=["verification", "lean", "types"], import_item_name=None
                parts.push(name.clone());
                None // Import whole module
            }
            ImportTarget::Aliased { name, .. } => {
                // `import X.Y.Z as alias` - import the whole module X.Y.Z, bind to alias
                // The target 'name' is the final component of the module path that was
                // separated by the parser. We need to add it back to get the full path.
                // e.g., `import verification.lean.types as types`:
                //   - Parser produces: path=["verification", "lean"], name="types"
                //   - We need: parts=["verification", "lean", "types"], import_item_name=None
                parts.push(name.clone());
                None // Import whole module
            }
            ImportTarget::Glob => None,
            ImportTarget::Group(_) => {
                // Group imports: `import module.{X, Y, Z}`
                // Load the module and extract the specified items
                None // Import whole module, then extract items
            }
        }
    };

    // Try to resolve the module path
    let base_dir = current_file.and_then(|p| p.parent()).unwrap_or(Path::new("."));
    eprintln!("DEBUG LOAD MODULE: Resolving {:?} from base {:?}", parts, base_dir);

    let module_path = match resolve_module_path(&parts, base_dir) {
        Ok(p) => {
            eprintln!("DEBUG LOAD MODULE: Resolved to {:?}", p);
            p
        },
        Err(e) => {
            eprintln!("DEBUG LOAD MODULE: Failed to resolve {:?}: {}", parts, e);
            decrement_load_depth();
            debug!(module = %parts.join("."), error = %e, "Failed to resolve module");
            return Err(e);
        }
    };
    debug!(module = %parts.join("."), path = ?module_path, "Resolved module path");

    // Check cache first - if we've already loaded this module, return cached exports
    if let Some(cached_exports) = get_cached_module_exports(&module_path) {
        eprintln!("DEBUG LOAD MODULE: Using cached exports for {:?}", module_path);
        decrement_load_depth();
        // If importing a specific item, extract it from cached exports
        if let Some(item_name) = import_item_name {
            if let Value::Dict(exports_dict) = &cached_exports {
                if let Some(value) = exports_dict.get(&item_name) {
                    return Ok(value.clone());
                }
            }
            return Err(CompileError::Runtime(format!("Module does not export '{}'", item_name)));
        }
        return Ok(cached_exports);
    }

    // Check for circular import - if this module is currently being loaded,
    // return an empty dict to break the cycle. The actual exports will be
    // available after the module finishes loading.
    if is_module_loading(&module_path) {
        warn!(path = ?module_path, "Circular import detected, returning empty dict");
        decrement_load_depth();
        // Circular import detected - return empty dict as placeholder
        // This allows the current load to complete, and the cache will be populated
        return Ok(Value::Dict(HashMap::new()));
    }

    // Mark this module as currently loading
    debug!(path = ?module_path, depth, "Loading module");
    mark_module_loading(&module_path);

    // Read and parse the module
    eprintln!("DEBUG LOAD MODULE: Reading module from {:?}", module_path);
    let source = match fs::read_to_string(&module_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("DEBUG LOAD MODULE: Failed to read {:?}: {}", module_path, e);
            unmark_module_loading(&module_path);
            decrement_load_depth();
            return Err(CompileError::Io(format!("Cannot read module {:?}: {}", module_path, e)));
        }
    };

    trace!(path = ?module_path, bytes = source.len(), "Parsing module");
    let mut parser = simple_parser::Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            unmark_module_loading(&module_path);
            decrement_load_depth();
            error!(path = ?module_path, error = %e, "Failed to parse module");
            return Err(CompileError::Parse(format!(
                "Cannot parse module {:?}: {}",
                module_path, e
            )));
        }
    };

    // Evaluate the module to get its environment (including imports)
    debug!(path = ?module_path, "Evaluating module exports");
    let (module_env, module_exports) =
        match evaluate_module_exports(&module.items, Some(&module_path), functions, classes, enums) {
            Ok(result) => result,
            Err(e) => {
                unmark_module_loading(&module_path);
                decrement_load_depth();
                return Err(e);
            }
        };

    // Create exports with the module's environment captured
    // IMPORTANT: Filter out Function values from captured_env to avoid exponential cloning.
    // Functions can call other module functions through the global `functions` HashMap,
    // so they don't need functions in their captured_env. Only capture non-function values
    // (variables, classes, enums, etc.) that functions might need to access.
    let filtered_env: Env = module_env
        .iter()
        .filter(|(_, v)| !matches!(v, Value::Function { .. }))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();

    let mut exports: HashMap<String, Value> = HashMap::new();
    for (name, value) in module_exports {
        match value {
            Value::Function { name: fn_name, def, .. } => {
                // Re-create function with filtered env (excludes function values to avoid cycles)
                exports.insert(
                    name,
                    Value::Function {
                        name: fn_name,
                        def,
                        captured_env: filtered_env.clone(),
                    },
                );
            }
            other => {
                exports.insert(name, other);
            }
        }
    }

    // Cache the full module exports for future use
    let exports_value = Value::Dict(exports.clone());
    cache_module_exports(&module_path, exports_value);

    // Mark module as done loading
    unmark_module_loading(&module_path);
    decrement_load_depth();
    debug!(path = ?module_path, exports = exports.len(), "Successfully loaded module");

    // If importing a specific item, extract it from exports
    if let Some(item_name) = import_item_name {
        // Look up the specific item in the module's exports
        if let Some(value) = exports.get(&item_name) {
            return Ok(value.clone());
        } else {
            return Err(CompileError::Runtime(format!(
                "Module {:?} does not export '{}'",
                module_path, item_name
            )));
        }
    }

    // Otherwise, return the full module dict (for glob imports or module-level imports)
    Ok(Value::Dict(exports))
}
