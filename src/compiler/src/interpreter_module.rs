//! Module loading and resolution for the Simple interpreter.
//!
//! This module handles:
//! - Loading and parsing module files
//! - Resolving module paths (relative, stdlib, __init__.spl)
//! - Evaluating module exports
//! - Merging module definitions into global state

use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use simple_parser::ast::{
    ClassDef, EnumDef, Expr, ExportUseStmt, FunctionDef, ImportTarget, MacroDef, ModulePath, Node, Pattern, UseStmt,
};

use crate::error::CompileError;
use crate::value::{Env, Value};

type Enums = HashMap<String, EnumDef>;
type Macros = HashMap<String, MacroDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

// Import evaluate_expr from parent module
use super::evaluate_expr;

/// Maximum depth for recursive module loading to prevent infinite loops
const MAX_MODULE_DEPTH: usize = 50;

/// Check if debug logging is enabled (set SIMPLE_DEBUG_IMPORTS=1)
fn debug_imports_enabled() -> bool {
    std::env::var("SIMPLE_DEBUG_IMPORTS").map(|v| v == "1").unwrap_or(false)
}

macro_rules! debug_import {
    ($($arg:tt)*) => {
        if debug_imports_enabled() {
            eprintln!("[IMPORT] {}", format!($($arg)*));
        }
    };
}

// Thread-local cache for module exports to avoid re-parsing modules
// Key: normalized module path, Value: module exports dict
thread_local! {
    pub static MODULE_EXPORTS_CACHE: RefCell<HashMap<PathBuf, Value>> = RefCell::new(HashMap::new());
    // Track modules currently being loaded to prevent circular import infinite recursion
    pub static MODULES_LOADING: RefCell<std::collections::HashSet<PathBuf>> = RefCell::new(std::collections::HashSet::new());
    // Track current loading depth to prevent infinite recursion
    pub static MODULE_LOAD_DEPTH: RefCell<usize> = RefCell::new(0);
}

/// Clear the module exports cache (useful between test runs)
pub fn clear_module_cache() {
    MODULE_EXPORTS_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULES_LOADING.with(|loading| loading.borrow_mut().clear());
    MODULE_LOAD_DEPTH.with(|depth| *depth.borrow_mut() = 0);
}

/// Normalize a path to a consistent key for caching/tracking.
/// Uses canonicalize if the file exists, otherwise normalizes the path string.
fn normalize_path_key(path: &Path) -> PathBuf {
    // First try to canonicalize (works if file exists)
    if let Ok(canonical) = path.canonicalize() {
        return canonical;
    }

    // If file doesn't exist yet, normalize the path manually
    // This handles cases like "./foo/../bar" -> "./bar"
    let mut components: Vec<std::path::Component> = Vec::new();
    for component in path.components() {
        match component {
            std::path::Component::ParentDir => {
                // Go up one level if possible
                if !components.is_empty() {
                    if let Some(std::path::Component::Normal(_)) = components.last() {
                        components.pop();
                        continue;
                    }
                }
                components.push(component);
            }
            std::path::Component::CurDir => {
                // Skip "." components
            }
            _ => components.push(component),
        }
    }

    components.iter().collect()
}

/// Check if a module is currently being loaded (circular import detection)
fn is_module_loading(path: &Path) -> bool {
    let key = normalize_path_key(path);
    MODULES_LOADING.with(|loading| {
        let result = loading.borrow().contains(&key);
        debug_import!("is_module_loading({:?}) = {} (set size: {})", key, result, loading.borrow().len());
        result
    })
}

/// Mark a module as currently loading
fn mark_module_loading(path: &Path) {
    let key = normalize_path_key(path);
    debug_import!("mark_module_loading: {:?}", key);
    MODULES_LOADING.with(|loading| {
        loading.borrow_mut().insert(key);
    });
}

/// Unmark a module as loading (finished loading)
fn unmark_module_loading(path: &Path) {
    let key = normalize_path_key(path);
    debug_import!("unmark_module_loading: {:?}", key);
    MODULES_LOADING.with(|loading| {
        loading.borrow_mut().remove(&key);
    });
}

/// Increment the module load depth and return the new depth
fn increment_load_depth() -> usize {
    MODULE_LOAD_DEPTH.with(|depth| {
        let mut d = depth.borrow_mut();
        *d += 1;
        *d
    })
}

/// Decrement the module load depth
fn decrement_load_depth() {
    MODULE_LOAD_DEPTH.with(|depth| {
        let mut d = depth.borrow_mut();
        if *d > 0 {
            *d -= 1;
        }
    });
}

/// Get current module load depth
fn get_load_depth() -> usize {
    MODULE_LOAD_DEPTH.with(|depth| *depth.borrow())
}

/// Get cached module exports for a path, if available
pub fn get_cached_module_exports(path: &Path) -> Option<Value> {
    let key = normalize_path_key(path);
    MODULE_EXPORTS_CACHE.with(|cache| {
        let result = cache.borrow().get(&key).cloned();
        if result.is_some() {
            debug_import!("cache hit for: {:?}", key);
        }
        result
    })
}

/// Cache module exports for a path
pub fn cache_module_exports(path: &Path, exports: Value) {
    let key = normalize_path_key(path);
    debug_import!("caching exports for: {:?}", key);
    MODULE_EXPORTS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key, exports);
    });
}

/// Get the import alias from a UseStmt if it exists
pub(super) fn get_import_alias(use_stmt: &UseStmt) -> Option<String> {
    match &use_stmt.target {
        ImportTarget::Aliased { alias, .. } => Some(alias.clone()),
        _ => None,
    }
}

/// Load a module file, evaluate it, and return exports with captured environment
/// This is needed so that module-level imports are accessible in exported functions
pub(super) fn load_and_merge_module(
    use_stmt: &UseStmt,
    current_file: Option<&Path>,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &mut Enums,
) -> Result<Value, CompileError> {
    // Check depth limit to prevent infinite recursion
    let depth = increment_load_depth();
    if depth > MAX_MODULE_DEPTH {
        decrement_load_depth();
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

    debug_import!("load_and_merge_module: parts={:?}, target={:?}, depth={}", parts, use_stmt.target, depth);

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
                debug_import!("Glob import with empty path - skipping");
                decrement_load_depth();
                return Ok(Value::Dict(HashMap::new()));
            }
            ImportTarget::Group(_) => {
                decrement_load_depth();
                return Ok(Value::Dict(HashMap::new()));
            }
        }
    } else {
        // Path is not empty - check if target is extracting a specific item
        let last_path_segment = parts.last().cloned();
        match &use_stmt.target {
            ImportTarget::Single(name) => {
                // Check if this is just a module import (name == last segment)
                if last_path_segment.as_ref() == Some(name) {
                    None // Import whole module
                } else {
                    Some(name.clone())
                }
            }
            ImportTarget::Aliased { name, .. } => {
                // Check if this is a whole-module alias (name == last segment)
                // e.g., `import spec as sp` where path is ["spec"] and name is "spec"
                if last_path_segment.as_ref() == Some(name) {
                    None // Import whole module, just rename it
                } else {
                    Some(name.clone())
                }
            }
            ImportTarget::Glob => None,
            ImportTarget::Group(_) => {
                // Group imports need special handling
                decrement_load_depth();
                return Ok(Value::Dict(HashMap::new()));
            }
        }
    };

    // Try to resolve the module path
    let base_dir = current_file
        .and_then(|p| p.parent())
        .unwrap_or(Path::new("."));

    let module_path = match resolve_module_path(&parts, base_dir) {
        Ok(p) => p,
        Err(e) => {
            decrement_load_depth();
            debug_import!("Failed to resolve module: {:?} - {}", parts.join("."), e);
            return Err(e);
        }
    };
    debug_import!("Resolved module path: {:?} -> {:?}", parts.join("."), module_path);

    // Check cache first - if we've already loaded this module, return cached exports
    if let Some(cached_exports) = get_cached_module_exports(&module_path) {
        decrement_load_depth();
        // If importing a specific item, extract it from cached exports
        if let Some(item_name) = import_item_name {
            if let Value::Dict(exports_dict) = &cached_exports {
                if let Some(value) = exports_dict.get(&item_name) {
                    return Ok(value.clone());
                }
            }
            return Err(CompileError::Runtime(format!(
                "Module does not export '{}'",
                item_name
            )));
        }
        return Ok(cached_exports);
    }

    // Check for circular import - if this module is currently being loaded,
    // return an empty dict to break the cycle. The actual exports will be
    // available after the module finishes loading.
    if is_module_loading(&module_path) {
        debug_import!("Circular import detected for: {:?}, returning empty dict", module_path);
        decrement_load_depth();
        // Circular import detected - return empty dict as placeholder
        // This allows the current load to complete, and the cache will be populated
        return Ok(Value::Dict(HashMap::new()));
    }

    // Mark this module as currently loading
    debug_import!("Loading module: {:?} (depth={})", module_path, depth);
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

    debug_import!("Parsing module: {:?} ({} bytes)", module_path, source.len());
    let mut parser = simple_parser::Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            unmark_module_loading(&module_path);
            decrement_load_depth();
            return Err(CompileError::Parse(format!("Cannot parse module {:?}: {}", module_path, e)));
        }
    };

    // Evaluate the module to get its environment (including imports)
    debug_import!("Evaluating module exports: {:?}", module_path);
    let (module_env, module_exports) = match evaluate_module_exports(
        &module.items,
        Some(&module_path),
        functions,
        classes,
        enums,
    ) {
        Ok(result) => result,
        Err(e) => {
            unmark_module_loading(&module_path);
            decrement_load_depth();
            return Err(e);
        }
    };

    // Create exports with the module's environment captured
    let mut exports: HashMap<String, Value> = HashMap::new();
    for (name, value) in module_exports {
        match value {
            Value::Function { name: fn_name, def, .. } => {
                // Re-create function with module's env as captured_env
                exports.insert(name, Value::Function {
                    name: fn_name,
                    def,
                    captured_env: module_env.clone(),
                });
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
    debug_import!("Successfully loaded module: {:?} ({} exports)", module_path, exports.len());

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

/// Evaluate a module's statements and collect its environment and exports
pub(super) fn evaluate_module_exports(
    items: &[Node],
    module_path: Option<&Path>,
    global_functions: &mut HashMap<String, FunctionDef>,
    global_classes: &mut HashMap<String, ClassDef>,
    global_enums: &mut Enums,
) -> Result<(Env, HashMap<String, Value>), CompileError> {
    let mut env: Env = HashMap::new();
    let mut exports: HashMap<String, Value> = HashMap::new();
    let mut local_functions: HashMap<String, FunctionDef> = HashMap::new();
    let mut local_classes: HashMap<String, ClassDef> = HashMap::new();
    let mut local_enums: Enums = HashMap::new();
    let impl_methods: ImplMethods = HashMap::new();

    // Add builtin types to module environment so they're available in module code
    env.insert("Dict".to_string(), Value::Constructor { class_name: "Dict".to_string() });
    env.insert("List".to_string(), Value::Constructor { class_name: "List".to_string() });
    env.insert("Set".to_string(), Value::Constructor { class_name: "Set".to_string() });
    env.insert("Array".to_string(), Value::Constructor { class_name: "Array".to_string() });
    env.insert("Tuple".to_string(), Value::Constructor { class_name: "Tuple".to_string() });
    env.insert("Option".to_string(), Value::Constructor { class_name: "Option".to_string() });
    env.insert("Result".to_string(), Value::Constructor { class_name: "Result".to_string() });
    env.insert("Some".to_string(), Value::Constructor { class_name: "Some".to_string() });
    env.insert("None".to_string(), Value::Enum { enum_name: "Option".to_string(), variant: "None".to_string(), payload: None });
    env.insert("Ok".to_string(), Value::Constructor { class_name: "Ok".to_string() });
    env.insert("Err".to_string(), Value::Constructor { class_name: "Err".to_string() });

    // First pass: register functions and types
    for item in items {
        match item {
            Node::Function(f) => {
                local_functions.insert(f.name.clone(), f.clone());
                // Don't add "main" from imported modules to global functions
                // to prevent auto-execution when the main script finishes
                if f.name != "main" {
                    global_functions.insert(f.name.clone(), f.clone());
                }
            }
            Node::Class(c) => {
                local_classes.insert(c.name.clone(), c.clone());
                global_classes.insert(c.name.clone(), c.clone());
                exports.insert(c.name.clone(), Value::Constructor {
                    class_name: c.name.clone(),
                });
            }
            Node::Enum(e) => {
                local_enums.insert(e.name.clone(), e.clone());
                global_enums.insert(e.name.clone(), e.clone());
                // Export enum as EnumType so EnumName.VariantName syntax works
                exports.insert(e.name.clone(), Value::EnumType {
                    enum_name: e.name.clone(),
                });
            }
            Node::Macro(m) => {
                // Register macro in exports with special prefix
                exports.insert(format!("macro:{}", m.name), Value::Str(format!("macro:{}", m.name)));
                // Also register in the thread-local USER_MACROS
                super::USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));
            }
            _ => {}
        }
    }

    // Second pass: process imports and assignments to build the environment
    for item in items {
        match item {
            Node::UseStmt(use_stmt) => {
                // Recursively load imported modules
                let binding_name = match &use_stmt.target {
                    ImportTarget::Single(name) => name.clone(),
                    ImportTarget::Aliased { alias, .. } => alias.clone(),
                    ImportTarget::Glob | ImportTarget::Group(_) => {
                        use_stmt.path.segments.last().cloned().unwrap_or_else(|| "module".to_string())
                    }
                };

                match load_and_merge_module(use_stmt, module_path, global_functions, global_classes, global_enums) {
                    Ok(value) => {
                        env.insert(binding_name.clone(), value);
                    }
                    Err(_e) => {
                        // Module loading failed - use empty dict
                        env.insert(binding_name.clone(), Value::Dict(HashMap::new()));
                    }
                }
            }
            Node::Let(stmt) => {
                // Evaluate module-level let statements (for global variables)
                if let Some(init) = &stmt.value {
                    if let Ok(value) = evaluate_expr(init, &env, &mut local_functions, &mut local_classes, &local_enums, &impl_methods) {
                        // Only handle simple identifier patterns for now
                        if let Pattern::Identifier(name) = &stmt.pattern {
                            env.insert(name.clone(), value);
                        }
                    }
                }
            }
            Node::Assignment(stmt) => {
                // Evaluate module-level assignments
                if let Expr::Identifier(name) = &stmt.target {
                    if let Ok(value) = evaluate_expr(&stmt.value, &env, &mut local_functions, &mut local_classes, &local_enums, &impl_methods) {
                        env.insert(name.clone(), value);
                    }
                }
            }
            Node::ExportUseStmt(export_stmt) => {
                // Handle re-exports: export X, Y from module
                // Load the source module and add specified items to our exports
                if let Ok(source_exports) = load_export_source(export_stmt, module_path, global_functions, global_classes, global_enums) {
                    match &export_stmt.target {
                        ImportTarget::Single(name) => {
                            if let Some(value) = source_exports.get(name) {
                                exports.insert(name.clone(), value.clone());
                                env.insert(name.clone(), value.clone());
                            }
                        }
                        ImportTarget::Aliased { name, alias } => {
                            if let Some(value) = source_exports.get(name) {
                                exports.insert(alias.clone(), value.clone());
                                env.insert(alias.clone(), value.clone());
                            }
                        }
                        ImportTarget::Glob => {
                            // Export everything from the source module
                            for (name, value) in source_exports {
                                exports.insert(name.clone(), value.clone());
                                env.insert(name, value);
                            }
                        }
                        ImportTarget::Group(items) => {
                            // Export specific items
                            for item in items {
                                match item {
                                    ImportTarget::Single(name) => {
                                        if let Some(value) = source_exports.get(name) {
                                            exports.insert(name.clone(), value.clone());
                                            env.insert(name.clone(), value.clone());
                                        }
                                    }
                                    ImportTarget::Aliased { name, alias } => {
                                        if let Some(value) = source_exports.get(name) {
                                            exports.insert(alias.clone(), value.clone());
                                            env.insert(alias.clone(), value.clone());
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // First pass: Add all module functions to env with empty captured_env
    // This allows functions to reference each other
    debug_import!("First pass: adding {} functions to env", local_functions.len());
    for (name, f) in &local_functions {
        env.insert(name.clone(), Value::Function {
            name: name.clone(),
            def: Box::new(f.clone()),
            captured_env: Env::new(), // Temporary - will be replaced
        });
    }

    // Second pass: Export functions with COMPLETE module environment captured
    // The captured_env now includes globals AND all other functions
    debug_import!("Second pass: exporting {} functions (env has {} entries)", local_functions.len(), env.len());
    for (name, f) in &local_functions {
        let func_with_env = Value::Function {
            name: name.clone(),
            def: Box::new(f.clone()),
            captured_env: env.clone(), // Capture complete environment
        };
        exports.insert(name.clone(), func_with_env.clone());

        // Update env with the function that has the complete captured_env
        // so inter-function calls work correctly
        env.insert(name.clone(), func_with_env);
    }
    debug_import!("Finished exporting, {} total exports", exports.len());

    Ok((env, exports))
}

/// Load a module for re-export (export X from Y)
fn load_export_source(
    export_stmt: &ExportUseStmt,
    current_file: Option<&Path>,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &mut Enums,
) -> Result<HashMap<String, Value>, CompileError> {
    debug_import!("load_export_source: path={:?}, target={:?}", export_stmt.path.segments, export_stmt.target);

    // Skip if path is empty - this happens with bare exports like `export X`
    // which mark local symbols for export, not re-exports from other modules
    if export_stmt.path.segments.is_empty() {
        debug_import!("Skipping export with empty path (bare export)");
        return Ok(HashMap::new());
    }

    // Build a UseStmt to load the source module
    let use_stmt = UseStmt {
        span: export_stmt.span.clone(),
        path: export_stmt.path.clone(),
        target: ImportTarget::Glob, // Load entire module to get all exports
    };

    match load_and_merge_module(&use_stmt, current_file, functions, classes, enums) {
        Ok(Value::Dict(dict)) => Ok(dict),
        Ok(_) => Ok(HashMap::new()),
        Err(e) => {
            debug_import!("load_export_source error: {}", e);
            Ok(HashMap::new())
        }
    }
}

/// Resolve module path from segments
pub(super) fn resolve_module_path(parts: &[String], base_dir: &Path) -> Result<PathBuf, CompileError> {
    // Try resolving from base directory first (sibling files)
    let mut resolved = base_dir.to_path_buf();
    for part in parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() {
        return Ok(resolved);
    }

    // Try __init__.spl in directory
    let mut init_resolved = base_dir.to_path_buf();
    for part in parts {
        init_resolved = init_resolved.join(part);
    }
    init_resolved = init_resolved.join("__init__");
    init_resolved.set_extension("spl");
    if init_resolved.exists() {
        return Ok(init_resolved);
    }

    // Try stdlib location - walk up directory tree
    let mut current = base_dir.to_path_buf();
    for _ in 0..10 {
        // Try both "simple/std_lib/src" and "std_lib/src" (in case we're already in simple/)
        for stdlib_subpath in &["simple/std_lib/src", "std_lib/src"] {
            let stdlib_candidate = current.join(stdlib_subpath);
            if stdlib_candidate.exists() {
            // Try resolving from stdlib
            let mut stdlib_path = stdlib_candidate.clone();
            for part in parts {
                stdlib_path = stdlib_path.join(part);
            }
            stdlib_path.set_extension("spl");
            if stdlib_path.exists() {
                return Ok(stdlib_path);
            }

            // Also try __init__.spl in stdlib
            let mut stdlib_init_path = stdlib_candidate.clone();
            for part in parts {
                stdlib_init_path = stdlib_init_path.join(part);
            }
            stdlib_init_path = stdlib_init_path.join("__init__");
            stdlib_init_path.set_extension("spl");
            if stdlib_init_path.exists() {
                return Ok(stdlib_init_path);
            }
            }  // End of if stdlib_candidate.exists()
        }  // End of for stdlib_subpath
        if let Some(parent) = current.parent() {
            current = parent.to_path_buf();
        } else {
            break;
        }
    }

    Err(CompileError::Semantic(format!(
        "Cannot resolve module: {}",
        parts.join(".")
    )))
}

/// Merge module definitions into global state and collect exports
pub(super) fn merge_module_definitions(
    items: &[Node],
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &mut Enums,
) -> Result<HashMap<String, Value>, CompileError> {
    let mut exports: HashMap<String, Value> = HashMap::new();

    // First pass: collect all definitions into global maps
    for item in items {
        match item {
            Node::Function(f) => {
                // Add to global functions map
                functions.insert(f.name.clone(), f.clone());

                // Add to exports dict
                let func_value = Value::Function {
                    name: f.name.clone(),
                    def: Box::new(f.clone()),
                    captured_env: Env::new(),
                };
                exports.insert(f.name.clone(), func_value);
            }
            Node::Class(c) => {
                // Add to global classes map
                classes.insert(c.name.clone(), c.clone());

                // Add to exports dict
                exports.insert(c.name.clone(), Value::Constructor {
                    class_name: c.name.clone(),
                });
            }
            Node::Enum(e) => {
                // Add to global enums map - this is critical for enum variant access
                enums.insert(e.name.clone(), e.clone());

                // Export the enum as EnumType for variant construction (EnumName.Variant)
                exports.insert(e.name.clone(), Value::EnumType {
                    enum_name: e.name.clone(),
                });
            }
            _ => {}
        }
    }

    Ok(exports)
}
