//! Module caching and loading state management
//!
//! This module provides thread-local caching for loaded modules and tracking
//! of modules currently being loaded (for circular import detection).

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tracing::trace;

use crate::value::Value;
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef};

/// Maximum depth for recursive module loading to prevent infinite loops
pub const MAX_MODULE_DEPTH: usize = 50;

// Thread-local cache for module exports to avoid re-parsing modules
// Key: normalized module path, Value: module exports dict
thread_local! {
    pub static MODULE_EXPORTS_CACHE: RefCell<HashMap<PathBuf, Value>> = RefCell::new(HashMap::new());
    // Cache for ClassDef objects - needed for static method calls on imported classes
    pub static MODULE_CLASSES_CACHE: RefCell<HashMap<PathBuf, HashMap<String, ClassDef>>> = RefCell::new(HashMap::new());
    // Cache for FunctionDef objects
    pub static MODULE_FUNCTIONS_CACHE: RefCell<HashMap<PathBuf, HashMap<String, FunctionDef>>> = RefCell::new(HashMap::new());
    // Cache for EnumDef objects
    pub static MODULE_ENUMS_CACHE: RefCell<HashMap<PathBuf, HashMap<String, EnumDef>>> = RefCell::new(HashMap::new());
    // Track modules currently being loaded to prevent circular import infinite recursion
    pub static MODULES_LOADING: RefCell<std::collections::HashSet<PathBuf>> = RefCell::new(std::collections::HashSet::new());
    // Track current loading depth to prevent infinite recursion
    pub static MODULE_LOAD_DEPTH: RefCell<usize> = RefCell::new(0);
    // Cache for partial exports (type definitions only) - used for circular import resolution
    // This contains exports after register_definitions but before process_imports_and_assignments
    pub static PARTIAL_MODULE_EXPORTS_CACHE: RefCell<HashMap<PathBuf, Value>> = RefCell::new(HashMap::new());
}

/// Clear the module exports cache (useful between test runs)
pub fn clear_module_cache() {
    MODULE_EXPORTS_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULE_CLASSES_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULE_FUNCTIONS_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULE_ENUMS_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULES_LOADING.with(|loading| loading.borrow_mut().clear());
    MODULE_LOAD_DEPTH.with(|depth| *depth.borrow_mut() = 0);
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Normalize a path to a consistent key for caching/tracking.
/// Uses canonicalize if the file exists, otherwise normalizes the path string.
pub fn normalize_path_key(path: &Path) -> PathBuf {
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
pub fn is_module_loading(path: &Path) -> bool {
    let key = normalize_path_key(path);
    MODULES_LOADING.with(|loading| {
        let result = loading.borrow().contains(&key);
        trace!(path = ?key, is_loading = result, set_size = loading.borrow().len(), "Checking if module is loading");
        result
    })
}

/// Mark a module as currently loading
pub fn mark_module_loading(path: &Path) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Marking module as loading");
    MODULES_LOADING.with(|loading| {
        loading.borrow_mut().insert(key);
    });
}

/// Unmark a module as loading (finished loading)
pub fn unmark_module_loading(path: &Path) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Unmarking module as loading");
    MODULES_LOADING.with(|loading| {
        loading.borrow_mut().remove(&key);
    });
}

/// Increment the module load depth and return the new depth
pub fn increment_load_depth() -> usize {
    MODULE_LOAD_DEPTH.with(|depth| {
        let mut d = depth.borrow_mut();
        *d += 1;
        *d
    })
}

/// Decrement the module load depth
pub fn decrement_load_depth() {
    MODULE_LOAD_DEPTH.with(|depth| {
        let mut d = depth.borrow_mut();
        if *d > 0 {
            *d -= 1;
        }
    });
}

/// Get current module load depth
#[allow(dead_code)]
pub fn get_load_depth() -> usize {
    MODULE_LOAD_DEPTH.with(|depth| *depth.borrow())
}

/// Get cached module exports for a path, if available
pub fn get_cached_module_exports(path: &Path) -> Option<Value> {
    let key = normalize_path_key(path);
    MODULE_EXPORTS_CACHE.with(|cache| {
        let result = cache.borrow().get(&key).cloned();
        if result.is_some() {
            trace!(path = ?key, "Module cache hit");
        }
        result
    })
}

/// Cache module exports for a path
pub fn cache_module_exports(path: &Path, exports: Value) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Caching module exports");
    MODULE_EXPORTS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key, exports);
    });
}

/// Cache module definitions (classes, functions, enums) for a path
pub fn cache_module_definitions(
    path: &Path,
    classes: &HashMap<String, ClassDef>,
    functions: &HashMap<String, FunctionDef>,
    enums: &HashMap<String, EnumDef>,
) {
    let key = normalize_path_key(path);
    trace!(path = ?key, classes = classes.len(), functions = functions.len(), enums = enums.len(), "Caching module definitions");
    MODULE_CLASSES_CACHE.with(|cache| {
        cache.borrow_mut().insert(key.clone(), classes.clone());
    });
    MODULE_FUNCTIONS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key.clone(), functions.clone());
    });
    MODULE_ENUMS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key, enums.clone());
    });
}

/// Get cached module definitions and merge them into the provided HashMaps
/// Returns true if definitions were found and merged, false otherwise
pub fn merge_cached_module_definitions(
    path: &Path,
    classes: &mut HashMap<String, ClassDef>,
    functions: &mut HashMap<String, FunctionDef>,
    enums: &mut HashMap<String, EnumDef>,
) -> bool {
    let key = normalize_path_key(path);
    let mut found = false;

    MODULE_CLASSES_CACHE.with(|cache| {
        if let Some(cached_classes) = cache.borrow().get(&key) {
            for (name, class_def) in cached_classes {
                classes.insert(name.clone(), class_def.clone());
            }
            found = true;
        }
    });

    MODULE_FUNCTIONS_CACHE.with(|cache| {
        if let Some(cached_functions) = cache.borrow().get(&key) {
            for (name, func_def) in cached_functions {
                if name != "main" {  // Don't add "main" from imported modules
                    functions.insert(name.clone(), func_def.clone());
                }
            }
        }
    });

    MODULE_ENUMS_CACHE.with(|cache| {
        if let Some(cached_enums) = cache.borrow().get(&key) {
            for (name, enum_def) in cached_enums {
                enums.insert(name.clone(), enum_def.clone());
            }
        }
    });

    if found {
        trace!(path = ?key, "Merged cached module definitions");
    }
    found
}

/// Get partial module exports (type definitions only) for circular import resolution
pub fn get_partial_module_exports(path: &Path) -> Option<Value> {
    let key = normalize_path_key(path);
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| {
        let result = cache.borrow().get(&key).cloned();
        if result.is_some() {
            trace!(path = ?key, "Partial module exports cache hit");
        }
        result
    })
}

/// Cache partial module exports (type definitions only)
/// Called after register_definitions but before process_imports_and_assignments
pub fn cache_partial_module_exports(path: &Path, exports: Value) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Caching partial module exports");
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key, exports);
    });
}

/// Clear partial module exports for a path (after full loading completes)
pub fn clear_partial_module_exports(path: &Path) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Clearing partial module exports");
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| {
        cache.borrow_mut().remove(&key);
    });
}

/// Recursively filter out Function values from a Value.
/// This is used to prevent exponential memory growth when building captured environments.
/// For Dict values (imported modules), we recursively filter their contents.
/// For other values, we return them as-is unless they are functions.
pub fn filter_functions_from_value(value: &Value) -> Value {
    match value {
        Value::Function { .. } => {
            // Return a placeholder for functions to indicate they exist but without the heavy captured_env
            Value::Str("__function__".to_string())
        }
        Value::Dict(dict) => {
            // Recursively filter functions from dict values (imported modules)
            let filtered: HashMap<String, Value> = dict
                .iter()
                .filter(|(_, v)| !matches!(v, Value::Function { .. }))
                .map(|(k, v)| (k.clone(), filter_functions_from_value(v)))
                .collect();
            Value::Dict(filtered)
        }
        // For all other values, clone them as-is
        other => other.clone(),
    }
}
