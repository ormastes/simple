//! Module loading and resolution for the Simple interpreter.
//!
//! This module handles:
//! - Loading and parsing module files
//! - Resolving module paths (relative, stdlib, __init__.spl)
//! - Evaluating module exports
//! - Merging module definitions into global state

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use simple_parser::ast::{
    ClassDef, EnumDef, Expr, FunctionDef, ImportTarget, Node, Pattern, UseStmt,
};

use crate::error::CompileError;
use crate::value::{Env, Value};

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

// Import evaluate_expr from parent module
use super::evaluate_expr;

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
    // Build module path from segments (path only, not the import target)
    let parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    // Track what to extract from the module (if anything)
    let import_item_name: Option<String> = match &use_stmt.target {
        ImportTarget::Single(name) => Some(name.clone()),
        ImportTarget::Aliased { name, .. } => Some(name.clone()),
        ImportTarget::Glob => None,
        ImportTarget::Group(_) => {
            // Group imports need special handling
            return Ok(Value::Dict(HashMap::new()));
        }
    };

    // Try to resolve the module path
    let base_dir = current_file
        .and_then(|p| p.parent())
        .unwrap_or(Path::new("."));

    let module_path = resolve_module_path(&parts, base_dir)?;

    // Read and parse the module
    let source = fs::read_to_string(&module_path)
        .map_err(|e| CompileError::Io(format!("Cannot read module: {}", e)))?;

    let mut parser = simple_parser::Parser::new(&source);
    let module = parser.parse()
        .map_err(|e| CompileError::Parse(format!("Cannot parse module: {}", e)))?;

    // Evaluate the module to get its environment (including imports)
    let (module_env, module_exports) = evaluate_module_exports(
        &module.items,
        Some(&module_path),
        functions,
        classes,
        enums,
    )?;

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

    // If importing a specific item, extract it from exports
    if let Some(item_name) = import_item_name {
        // Look up the specific item in the module's exports
        if let Some(value) = exports.get(&item_name) {
            return Ok(value.clone());
        } else {
            return Err(CompileError::Runtime(format!(
                "Module does not export '{}'",
                item_name
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
                exports.insert(e.name.clone(), Value::Str(format!("enum:{}", e.name)));
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
            _ => {}
        }
    }

    // First pass: Add all module functions to env with empty captured_env
    // This allows functions to reference each other
    for (name, f) in &local_functions {
        env.insert(name.clone(), Value::Function {
            name: name.clone(),
            def: Box::new(f.clone()),
            captured_env: Env::new(), // Temporary - will be replaced
        });
    }

    // Second pass: Export functions with COMPLETE module environment captured
    // The captured_env now includes globals AND all other functions
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

    Ok((env, exports))
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

                // Export the enum type name as well (for type access)
                exports.insert(e.name.clone(), Value::Str(format!("enum:{}", e.name)));
            }
            _ => {}
        }
    }

    Ok(exports)
}
