//! Module loading functionality for the Simple interpreter.
//!
//! This module handles loading and parsing module files, managing circular imports,
//! and caching module exports.
//!
//! ## Capability-Based Import Validation
//!
//! When a module declares `requires [capabilities]`, imports are validated:
//! - Imported functions' effects must be compatible with importer's capabilities
//! - If importer has `requires [io]`, it can import functions with @io
//! - If importer has no `requires`, it can import anything (unrestricted)
//! - Capability violations are reported at import time

use std::collections::HashMap;
use std::fs;
use std::path::Path;

use tracing::{debug, error, trace, warn, instrument};

use simple_parser::ast::{Capability, ClassDef, EnumDef, Effect, ImportTarget, Node, UseStmt};

use crate::error::CompileError;
use crate::value::{Env, Value};

use super::module_cache::{
    cache_module_definitions, cache_module_exports, clear_partial_module_exports, decrement_load_depth,
    get_cached_module_exports, get_partial_module_exports, increment_load_depth, is_module_loading,
    mark_module_loading, merge_cached_module_definitions, unmark_module_loading, MAX_MODULE_DEPTH,
};
use super::module_evaluator::evaluate_module_exports;
use super::path_resolution::resolve_module_path;

type Enums = HashMap<String, EnumDef>;

/// Validate that imported function effects are compatible with importer's capabilities.
///
/// If the importer has no `requires [capabilities]`, it's unrestricted and can import anything.
/// Otherwise, each imported function's effects must be covered by the importer's capabilities.
pub fn validate_import_capabilities(
    import_name: &str,
    func_effects: &[Effect],
    importer_capabilities: &[Capability],
) -> Result<(), CompileError> {
    // If importer has no capabilities declared, it's unrestricted
    if importer_capabilities.is_empty() {
        return Ok(());
    }

    // Check each effect of the imported function
    for effect in func_effects {
        // Map effect to required capability
        let required_cap = Capability::from_effect(effect);

        // Async is always allowed (execution model, not capability)
        if required_cap.is_none() {
            continue;
        }

        let required_cap = required_cap.unwrap();

        // Check if importer has the required capability
        if !importer_capabilities.contains(&required_cap) {
            return Err(CompileError::semantic(format!(
                "Cannot import '{}' with @{} effect: module requires [{}] capability",
                import_name,
                effect.decorator_name(),
                required_cap.name()
            )));
        }
    }

    Ok(())
}

/// Extract capabilities from a module's AST nodes
pub fn extract_module_capabilities(items: &[Node]) -> Vec<Capability> {
    for item in items {
        if let Node::RequiresCapabilities(stmt) = item {
            return stmt.capabilities.clone();
        }
    }
    Vec::new() // No capabilities = unrestricted
}

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

    let module_path = match resolve_module_path(&parts, base_dir) {
        Ok(p) => p,
        Err(e) => {
            // FALLBACK: If resolution fails and we're not already extracting an item,
            // try treating the last path component as an item name instead of a module name.
            // E.g., `use app.lsp.server.LspServer` fails to find app/lsp/server/LspServer.spl,
            // so try loading app/lsp/server.spl and extract "LspServer" from it.
            if import_item_name.is_none() && parts.len() > 1 {
                debug!(
                    "Module resolution failed for {:?}, trying fallback: treating last component as item name",
                    parts.join(".")
                );
                // Pop the last component and treat it as an item name
                let mut parent_parts = parts.clone();
                let item_name = parent_parts.pop().unwrap();

                // Try to resolve the parent path
                if let Ok(_parent_module_path) = resolve_module_path(&parent_parts, base_dir) {
                    // Successfully resolved parent module - recursively load it and extract the item
                    decrement_load_depth();

                    // Recursively call load_and_merge_module with the parent path
                    // IMPORTANT: We need to construct the use_stmt such that it loads the PARENT module
                    // without trying to extract an item, because we'll extract the item ourselves below.
                    let mut modified_use_stmt = use_stmt.clone();
                    // For parent_parts = ["app", "lsp"], we need the parser form where:
                    //   - path.segments contains all but the last part
                    //   - target contains the last part
                    // So if parent_parts = ["app", "lsp", "server"], we want:
                    //   - path.segments = ["app", "lsp"]
                    //   - target = Single("server")
                    if parent_parts.len() >= 2 {
                        modified_use_stmt.path.segments = parent_parts[..parent_parts.len() - 1].to_vec();
                        modified_use_stmt.target = ImportTarget::Single(parent_parts[parent_parts.len() - 1].clone());
                    } else if parent_parts.len() == 1 {
                        // Single component like ["spec"] - path is empty, target is the component
                        modified_use_stmt.path.segments = vec![];
                        modified_use_stmt.target = ImportTarget::Single(parent_parts[0].clone());
                    } else {
                        // Empty parent_parts - shouldn't happen but handle it
                        modified_use_stmt.path.segments = vec![];
                        modified_use_stmt.target = ImportTarget::Glob;
                    }

                    return load_and_merge_module(&modified_use_stmt, current_file, functions, classes, enums)
                        .and_then(|module_value| {
                            // Extract the specific item from the loaded module
                            if let Value::Dict(exports_dict) = &module_value {
                                if let Some(value) = exports_dict.get(&item_name) {
                                    return Ok(value.clone());
                                }
                            }
                            Err(CompileError::Runtime(format!(
                                "Module {:?} does not export '{}'",
                                parent_parts.join("."),
                                item_name
                            )))
                        });
                }
            }

            decrement_load_depth();
            debug!(module = %parts.join("."), error = %e, "Failed to resolve module");
            return Err(e);
        }
    };
    debug!(module = %parts.join("."), path = ?module_path, "Resolved module path");

    // Check cache first - if we've already loaded this module, return cached exports
    if let Some(cached_exports) = get_cached_module_exports(&module_path) {
        if let Value::Dict(d) = &cached_exports {}
        // Merge cached definitions (classes, functions, enums) into caller's HashMaps
        // This ensures that static method calls work on imported classes
        merge_cached_module_definitions(&module_path, classes, functions, enums);

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
    // return partial exports (type definitions) to break the cycle.
    // This allows Java-style forward references where types are available
    // even during circular imports.
    if is_module_loading(&module_path) {
        // Try to get partial exports (type definitions from register_definitions)
        if let Some(partial_exports) = get_partial_module_exports(&module_path) {
            debug!(path = ?module_path, "Circular import detected, returning partial exports (type definitions)");
            decrement_load_depth();
            return Ok(partial_exports);
        }
        // Fallback to empty dict if no partial exports yet (module hasn't completed register_definitions)
        warn!(path = ?module_path, "Circular import detected, returning empty dict (no partial exports yet)");
        decrement_load_depth();
        return Ok(Value::Dict(HashMap::new()));
    }

    // Mark this module as currently loading
    debug!(path = ?module_path, depth, "Loading module");
    mark_module_loading(&module_path);

    // Read and parse the module
    let source = match fs::read_to_string(&module_path) {
        Ok(s) => s,
        Err(e) => {
            unmark_module_loading(&module_path);
            decrement_load_depth();
            return Err(CompileError::Io(format!("Cannot read module {:?}: {}", module_path, e)));
        }
    };

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
    let (module_env, module_exports, module_functions, module_classes, module_enums) =
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
        .map(|(k, v): (&String, &Value)| (k.clone(), v.clone()))
        .collect();

    let mut exports: HashMap<String, Value> = HashMap::new();
    for (name, value) in module_exports {
        match value {
            Value::Function {
                name: fn_name,
                def,
                captured_env: existing_env,
            } => {
                // Merge: start with the function's existing captured_env (from its defining module),
                // then overlay with this module's filtered_env. This preserves variables from
                // sub-modules (e.g., group_stack from dsl.spl when re-exported via __init__.spl).
                let mut merged_env = existing_env;
                for (k, v) in filtered_env.iter() {
                    if !matches!(v, Value::Function { .. }) {
                        merged_env.entry(k.clone()).or_insert_with(|| v.clone());
                    }
                }
                exports.insert(
                    name,
                    Value::Function {
                        name: fn_name,
                        def,
                        captured_env: merged_env,
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

    // Also cache the module definitions (classes, functions, enums) for future imports
    cache_module_definitions(&module_path, &module_classes, &module_functions, &module_enums);

    // Merge freshly loaded definitions into caller's scope (same as cache case on line 264)
    // This ensures static method calls work on imported classes
    for (name, class_def) in &module_classes {
        classes.insert(name.clone(), class_def.clone());
    }
    for (name, func_def) in &module_functions {
        if name != "main" {
            // Don't add "main" from imported modules
            functions.insert(name.clone(), func_def.clone());
        }
    }
    for (name, enum_def) in &module_enums {
        enums.insert(name.clone(), enum_def.clone());
    }

    // Clear partial exports now that full exports are available
    clear_partial_module_exports(&module_path);

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
