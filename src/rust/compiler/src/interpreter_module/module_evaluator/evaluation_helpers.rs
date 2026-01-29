//! Helper functions for module evaluation.
//!
//! This module contains helper functions used during module evaluation,
//! including type registration, import processing, and export handling.

use std::collections::HashMap;
use std::path::Path;

use tracing::{trace, warn};

use simple_parser::ast::{ClassDef, Expr, ImportTarget, Node, Pattern};

use crate::error::CompileError;
use crate::value::{Env, Value};

use crate::interpreter::interpreter_module::export_handler::load_export_source;
use crate::interpreter::module_cache::filter_functions_from_value;

type Enums = HashMap<String, simple_parser::ast::EnumDef>;
type ImplMethods = HashMap<String, Vec<simple_parser::ast::FunctionDef>>;

use crate::interpreter::evaluate_expr;

/// Add builtin types to the module environment
pub(super) fn add_builtin_types(env: &mut Env) {
    let builtin_types = [
        "Dict", "List", "Set", "Array", "Tuple", "Option", "Result", "Some", "Ok", "Err",
    ];

    for type_name in &builtin_types {
        env.insert(
            type_name.to_string(),
            Value::Constructor {
                class_name: type_name.to_string(),
            },
        );
    }

    // None is a special case - it's an enum variant, not a constructor
    env.insert(
        "None".to_string(),
        Value::Enum {
            enum_name: "Option".to_string(),
            variant: "None".to_string(),
            payload: None,
        },
    );
}

/// First pass: register functions and types
#[allow(clippy::too_many_arguments)]
pub(super) fn register_definitions(
    items: &[Node],
    local_functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    global_functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    local_classes: &mut HashMap<String, ClassDef>,
    global_classes: &mut HashMap<String, ClassDef>,
    local_enums: &mut Enums,
    global_enums: &mut Enums,
    exports: &mut HashMap<String, Value>,
    env: &mut Env,
) {
    for item in items.iter() {
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
                eprintln!("[DEBUG] Added class '{}' to global_classes (now {} classes)", c.name, global_classes.len());
                exports.insert(
                    c.name.clone(),
                    Value::Constructor {
                        class_name: c.name.clone(),
                    },
                );
            }
            Node::Struct(s) => {
                // Treat structs like classes for export purposes
                // Include struct methods so they're available for method calls
                let class_def = ClassDef {
                    span: s.span.clone(),
                    name: s.name.clone(),
                    generic_params: s.generic_params.clone(),
                    where_clause: s.where_clause.clone(),
                    fields: s.fields.clone(),
                    methods: s.methods.clone(), // Include struct methods!
                    parent: None,
                    visibility: s.visibility.clone(),
                    effects: vec![],
                    attributes: s.attributes.clone(),
                    doc_comment: s.doc_comment.clone(),
                    invariant: s.invariant.clone(),
                    macro_invocations: vec![],
                    mixins: vec![],
                    is_generic_template: s.is_generic_template,
                    specialization_of: s.specialization_of.clone(),
                    type_bindings: s.type_bindings.clone(),
                };
                local_classes.insert(s.name.clone(), class_def.clone());
                global_classes.insert(s.name.clone(), class_def);
                exports.insert(
                    s.name.clone(),
                    Value::Constructor {
                        class_name: s.name.clone(),
                    },
                );
            }
            Node::Impl(impl_block) => {
                // Add impl block methods to the corresponding class/struct/enum
                let type_name = match &impl_block.target_type {
                    simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                    simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                    _ => None,
                };
                if let Some(type_name) = type_name {
                    // Handle classes
                    if let Some(class_def) = local_classes.get_mut(&type_name) {
                        class_def.methods.extend(impl_block.methods.clone());
                    }
                    if let Some(class_def) = global_classes.get_mut(&type_name) {
                        class_def.methods.extend(impl_block.methods.clone());
                    }
                    // Handle enums - add impl methods to enum definition
                    if let Some(enum_def) = local_enums.get_mut(&type_name) {
                        enum_def.methods.extend(impl_block.methods.clone());
                    }
                    if let Some(enum_def) = global_enums.get_mut(&type_name) {
                        enum_def.methods.extend(impl_block.methods.clone());
                    }
                }
            }
            Node::Enum(e) => {
                local_enums.insert(e.name.clone(), e.clone());
                global_enums.insert(e.name.clone(), e.clone());
                // Export enum as EnumType so EnumName.VariantName syntax works
                let enum_type = Value::EnumType {
                    enum_name: e.name.clone(),
                };
                exports.insert(e.name.clone(), enum_type.clone());
                // CRITICAL FIX: Also add to env so it's available in closures
                env.insert(e.name.clone(), enum_type);
            }
            Node::Macro(m) => {
                // Register macro in exports with special prefix
                exports.insert(format!("macro:{}", m.name), Value::Str(format!("macro:{}", m.name)));
                // Also register in the thread-local USER_MACROS
                crate::interpreter::USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));
            }
            Node::Extern(ext) => {
                // Register extern function declarations in the global EXTERN_FUNCTIONS
                crate::interpreter::EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().insert(ext.name.clone()));
            }
            Node::Trait(t) => {
                // Export trait as TraitType so trait exports work
                let trait_type = Value::TraitType {
                    trait_name: t.name.clone(),
                };
                exports.insert(t.name.clone(), trait_type.clone());
                // Also add to env so it's available in the module
                env.insert(t.name.clone(), trait_type);
            }
            _ => {}
        }
    }
}

/// Second pass: process imports and assignments to build the environment
#[allow(clippy::too_many_arguments)]
pub(super) fn process_imports_and_assignments(
    items: &[Node],
    module_path: Option<&Path>,
    env: &mut Env,
    local_functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    local_classes: &mut HashMap<String, ClassDef>,
    local_enums: &Enums,
    impl_methods: &ImplMethods,
    global_functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    global_classes: &mut HashMap<String, ClassDef>,
    global_enums: &mut Enums,
    exports: &mut HashMap<String, Value>,
    bare_exports: &mut Vec<Vec<String>>,
) -> Result<(), CompileError> {
    for item in items.iter() {
        match item {
            Node::UseStmt(use_stmt) => {
                process_use_stmt(
                    use_stmt,
                    module_path,
                    env,
                    global_functions,
                    global_classes,
                    global_enums,
                )?;
            }
            Node::Let(stmt) => {
                // Evaluate module-level let statements (for global variables)
                if let Some(init) = &stmt.value {
                    if let Ok(value) =
                        evaluate_expr(init, env, local_functions, local_classes, local_enums, impl_methods)
                    {
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
                    if let Ok(value) = evaluate_expr(
                        &stmt.value,
                        env,
                        local_functions,
                        local_classes,
                        local_enums,
                        impl_methods,
                    ) {
                        env.insert(name.clone(), value);
                    }
                }
            }
            Node::ExportUseStmt(export_stmt) => {
                process_export_stmt(
                    export_stmt,
                    module_path,
                    env,
                    global_functions,
                    global_classes,
                    global_enums,
                    exports,
                    bare_exports,
                )?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// Process a use statement (import)
fn process_use_stmt(
    use_stmt: &simple_parser::ast::UseStmt,
    module_path: Option<&Path>,
    env: &mut Env,
    global_functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    global_classes: &mut HashMap<String, ClassDef>,
    global_enums: &mut Enums,
) -> Result<(), CompileError> {
    // Skip type-only imports at runtime - they're only for compile-time type checking
    if use_stmt.is_type_only {
        trace!("Skipping type-only import: {:?}", use_stmt.path);
        return Ok(());
    }

    // Recursively load imported modules
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

    match crate::interpreter::interpreter_module::module_loader::load_and_merge_module(
        use_stmt,
        module_path,
        global_functions,
        global_classes,
        global_enums,
    ) {
        Ok(value) => {
            // Unpack module exports into current namespace
            if let Value::Dict(exports) = &value {
                for (name, export_value) in exports {
                    env.insert(name.clone(), export_value.clone());
                }
            }
            // For glob imports, don't overwrite the unpacked exports with the module dict
            // This prevents a class named "shell" from being overwritten by the "shell" module dict
            match &use_stmt.target {
                ImportTarget::Glob => {
                    // For glob imports, only insert the module dict if there's no export with the same name
                    if let Value::Dict(exports) = &value {
                        if !exports.contains_key(&binding_name) {
                            env.insert(binding_name.clone(), value);
                        }
                    }
                }
                _ => {
                    // For non-glob imports, keep the module dict under its name for qualified access
                    env.insert(binding_name.clone(), value);
                }
            }
        }
        Err(_e) => {
            // Module loading failed - use empty dict
            env.insert(binding_name.clone(), Value::Dict(HashMap::new()));
        }
    }
    Ok(())
}

/// Process an export statement
#[allow(clippy::too_many_arguments)]
fn process_export_stmt(
    export_stmt: &simple_parser::ast::ExportUseStmt,
    module_path: Option<&Path>,
    env: &mut Env,
    global_functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    global_classes: &mut HashMap<String, ClassDef>,
    global_enums: &mut Enums,
    exports: &mut HashMap<String, Value>,
    bare_exports: &mut Vec<Vec<String>>,
) -> Result<(), CompileError> {
    // Check if this is a bare export (export X, Y) or re-export (export X from Y)
    if export_stmt.path.segments.is_empty() {
        // Bare export: export X, Y, Z
        let names_to_export = match &export_stmt.target {
            ImportTarget::Single(name) => vec![name.clone()],
            ImportTarget::Aliased { name, .. } => vec![name.clone()],
            ImportTarget::Group(items) => items
                .iter()
                .filter_map(|item| match item {
                    ImportTarget::Single(name) => Some(name.clone()),
                    ImportTarget::Aliased { name, .. } => Some(name.clone()),
                    _ => None,
                })
                .collect(),
            _ => vec![],
        };
        bare_exports.push(names_to_export);
    } else {
        // Re-export: export X, Y from module
        if let Ok(source_exports) =
            load_export_source(export_stmt, module_path, global_functions, global_classes, global_enums)
        {
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
    Ok(())
}

/// Create a filtered environment that excludes Function values
pub(super) fn create_filtered_env(env: &Env) -> Env {
    env.iter()
        .filter(|(_, v)| !matches!(v, Value::Function { .. }))
        .map(|(k, v)| {
            let filtered_value = filter_functions_from_value(v);
            (k.clone(), filtered_value)
        })
        .collect()
}

/// Export functions with filtered environment captured
pub(super) fn export_functions(
    local_functions: &HashMap<String, simple_parser::ast::FunctionDef>,
    filtered_env: &Env,
    exports: &mut HashMap<String, Value>,
    env: &mut Env,
) {
    // First pass: Add all module functions to env with empty captured_env
    trace!(functions = local_functions.len(), "First pass: adding functions to env");
    for (name, f) in local_functions {
        env.insert(
            name.clone(),
            Value::Function {
                name: name.clone(),
                def: Box::new(f.clone()),
                captured_env: Env::new(),
            },
        );
    }

    // Second pass: Export functions with filtered environment captured
    trace!(
        functions = local_functions.len(),
        env_size = filtered_env.len(),
        "Second pass: exporting functions"
    );
    for (name, f) in local_functions {
        let func_with_env = Value::Function {
            name: name.clone(),
            def: Box::new(f.clone()),
            captured_env: filtered_env.clone(),
        };
        exports.insert(name.clone(), func_with_env.clone());
        env.insert(name.clone(), func_with_env);
    }
    trace!(exports = exports.len(), "Finished exporting functions");
}

/// Process bare export statements
pub(super) fn process_bare_exports(bare_exports: &[Vec<String>], env: &Env, exports: &mut HashMap<String, Value>) {
    for export_names in bare_exports {
        for name in export_names {
            if let Some(value) = env.get(name) {
                // Don't override if already exported
                if !exports.contains_key(name) {
                    trace!(name = %name, "Adding bare export");
                    exports.insert(name.clone(), value.clone());
                }
            } else {
                // Check if it's already in exports (e.g., enums are auto-exported)
                if exports.contains_key(name) {
                    trace!(name = %name, "Bare export already in exports, skipping");
                } else {
                    // Warn if exported name doesn't exist
                    warn!(name = %name, "Export statement references undefined symbol");
                }
            }
        }
    }
    trace!(total_exports = exports.len(), "Finished processing bare exports");
}
