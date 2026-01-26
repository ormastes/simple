//! Module evaluation and export collection for the Simple interpreter.
//!
//! This module handles evaluating module statements to collect definitions,
//! process imports, and build the module's environment and exports.

use std::collections::HashMap;
use std::path::Path;

use simple_parser::ast::{ClassDef, EnumDef, Node};

use crate::error::CompileError;
use crate::value::{Env, Value};

use super::module_cache::cache_partial_module_exports;

mod evaluation_helpers;
use evaluation_helpers::{
    add_builtin_types, create_filtered_env, export_functions, process_bare_exports, process_imports_and_assignments,
    register_definitions,
};

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<simple_parser::ast::FunctionDef>>;

/// Evaluate a module's statements and collect its environment and exports
pub fn evaluate_module_exports(
    items: &[Node],
    module_path: Option<&Path>,
    global_functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    global_classes: &mut HashMap<String, ClassDef>,
    global_enums: &mut Enums,
) -> Result<(Env, HashMap<String, Value>), CompileError> {
    let mut env: Env = HashMap::new();
    let mut exports: HashMap<String, Value> = HashMap::new();
    let mut local_functions: HashMap<String, simple_parser::ast::FunctionDef> = HashMap::new();
    let mut local_classes: HashMap<String, ClassDef> = HashMap::new();
    let mut local_enums: Enums = HashMap::new();
    let impl_methods: ImplMethods = HashMap::new();

    // Collect bare export statements (export X, Y) to process after all definitions are available
    let mut bare_exports: Vec<Vec<String>> = Vec::new();

    // Add builtin types to module environment
    add_builtin_types(&mut env);

    // First pass: register functions and types
    register_definitions(
        items,
        &mut local_functions,
        global_functions,
        &mut local_classes,
        global_classes,
        &mut local_enums,
        global_enums,
        &mut exports,
        &mut env,
    );

    // Cache partial exports (type definitions) for circular import resolution
    // This allows other modules that import this one to access types even during circular imports
    if let Some(path) = module_path {
        cache_partial_module_exports(path, Value::Dict(exports.clone()));
    }

    // Second pass: process imports and assignments to build the environment
    process_imports_and_assignments(
        items,
        module_path,
        &mut env,
        &mut local_functions,
        &mut local_classes,
        &local_enums,
        &impl_methods,
        global_functions,
        global_classes,
        global_enums,
        &mut exports,
        &mut bare_exports,
    )?;

    // Create filtered environment and export functions
    let filtered_env = create_filtered_env(&env);
    export_functions(&local_functions, &filtered_env, &mut exports, &mut env);

    // Process bare export statements
    process_bare_exports(&bare_exports, &env, &mut exports);

    Ok((env, exports))
}
