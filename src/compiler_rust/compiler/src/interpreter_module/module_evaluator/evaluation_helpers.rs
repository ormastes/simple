//! Helper functions for module evaluation.
//!
//! This module contains helper functions used during module evaluation,
//! including type registration, import processing, and export handling.

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use tracing::{trace, warn};

use simple_parser::ast::{ClassDef, Expr, ImportTarget, Node, Pattern, Visibility};

use crate::error::CompileError;
use crate::value::{Env, Value};

use crate::interpreter::interpreter_module::export_handler::load_export_source;
use crate::interpreter::module_cache::filter_functions_from_value;

type Enums = HashMap<String, Arc<simple_parser::ast::EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<simple_parser::ast::FunctionDef>>>;

use crate::interpreter::evaluate_expr;
use crate::interpreter::MODULE_GLOBALS;
use crate::interpreter::GLOBAL_IMPL_METHODS;
use crate::interpreter::module_cache::MODULE_CLASSES_CACHE;
use crate::interpreter::core_types::get_pattern_name;

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
    local_functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    global_functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    local_classes: &mut HashMap<String, Arc<ClassDef>>,
    global_classes: &mut HashMap<String, Arc<ClassDef>>,
    local_enums: &mut Enums,
    global_enums: &mut Enums,
    exports: &mut HashMap<String, Value>,
    env: &mut Env,
) {
    for item in items.iter() {
        match item {
            Node::Function(f) => {
                let arc_f = Arc::new(f.clone());
                local_functions.insert(f.name.clone(), Arc::clone(&arc_f));
                // Don't add "main" from imported modules to global functions
                // to prevent auto-execution when the main script finishes
                if f.name != "main" {
                    global_functions.insert(f.name.clone(), arc_f);
                }
            }
            Node::Class(c) => {
                let arc_c = Arc::new(c.clone());
                local_classes.insert(c.name.clone(), Arc::clone(&arc_c));
                global_classes.insert(c.name.clone(), arc_c);
                exports.insert(
                    c.name.clone(),
                    Value::Constructor {
                        class_name: c.name.clone(),
                    },
                );
                // Register static methods as mangled free functions (ClassName__method)
                for method in &c.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", c.name, method.name);
                        let arc_method = Arc::new(method.clone());
                        local_functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        global_functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        exports.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(HashMap::new()),
                            },
                        );
                    }
                }
            }
            Node::Struct(s) => {
                // Treat structs like classes for export purposes
                // Include struct methods so they're available for method calls
                let class_def = ClassDef {
                    span: s.span,
                    name: s.name.clone(),
                    generic_params: s.generic_params.clone(),
                    where_clause: s.where_clause.clone(),
                    fields: s.fields.clone(),
                    methods: s.methods.clone(), // Include struct methods!
                    parent: None,
                    visibility: s.visibility,
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
                let arc_class_def = Arc::new(class_def);
                local_classes.insert(s.name.clone(), Arc::clone(&arc_class_def));
                global_classes.insert(s.name.clone(), arc_class_def);
                exports.insert(
                    s.name.clone(),
                    Value::Constructor {
                        class_name: s.name.clone(),
                    },
                );
                // Register static methods as mangled free functions (StructName__method)
                for method in &s.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", s.name, method.name);
                        let arc_method = Arc::new(method.clone());
                        local_functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        global_functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        exports.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(HashMap::new()),
                            },
                        );
                    }
                }
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
                        Arc::make_mut(class_def).methods.extend(impl_block.methods.clone());
                    }
                    if let Some(class_def) = global_classes.get_mut(&type_name) {
                        Arc::make_mut(class_def).methods.extend(impl_block.methods.clone());
                    }
                    // Handle enums - add impl methods to enum definition
                    if let Some(enum_def) = local_enums.get_mut(&type_name) {
                        Arc::make_mut(enum_def).methods.extend(impl_block.methods.clone());
                    }
                    if let Some(enum_def) = global_enums.get_mut(&type_name) {
                        Arc::make_mut(enum_def).methods.extend(impl_block.methods.clone());
                    }
                    // Register static methods from impl blocks as mangled free functions
                    for method in &impl_block.methods {
                        let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                        if is_static {
                            let mangled = format!("{}__{}", type_name, method.name);
                            let arc_method = Arc::new(method.clone());
                            local_functions.insert(mangled.clone(), Arc::clone(&arc_method));
                            global_functions.insert(mangled.clone(), Arc::clone(&arc_method));
                            exports.insert(
                                mangled.clone(),
                                Value::Function {
                                    name: mangled,
                                    def: arc_method,
                                    captured_env: Arc::new(HashMap::new()),
                                },
                            );
                        }
                    }
                    // Populate GLOBAL_IMPL_METHODS for cross-module fallback
                    // (mirrors GLOBAL_ENUMS pattern for enum definitions)
                    GLOBAL_IMPL_METHODS.with(|cell| {
                        let mut global_impls = cell.borrow_mut();
                        let methods = global_impls.entry(type_name.clone()).or_default();
                        methods.extend(impl_block.methods.iter().map(|m| Arc::new(m.clone())));
                    });
                    // Update MODULE_CLASSES_CACHE with the enriched class definition
                    // so cross-module fallback lookups find impl-added methods
                    if let Some(enriched_class) = global_classes.get(&type_name) {
                        let enriched_clone = enriched_class.clone();
                        MODULE_CLASSES_CACHE.with(|cache| {
                            let mut cache = cache.borrow_mut();
                            for (_path, module_classes) in cache.iter_mut() {
                                if module_classes.contains_key(&type_name) {
                                    module_classes.insert(type_name.clone(), enriched_clone.clone());
                                }
                            }
                        });
                    }
                }
            }
            Node::Enum(e) => {
                let arc_e = Arc::new(e.clone());
                local_enums.insert(e.name.clone(), Arc::clone(&arc_e));
                global_enums.insert(e.name.clone(), arc_e);
                // Export enum as EnumType so EnumName.VariantName syntax works
                let enum_type = Value::EnumType {
                    enum_name: e.name.clone(),
                };
                exports.insert(e.name.clone(), enum_type.clone());
                // CRITICAL FIX: Also add to env so it's available in closures
                env.insert(e.name.clone(), enum_type);
                // Register enum static methods as mangled free functions
                for method in &e.methods {
                    let is_static = method.is_static || !method.params.iter().any(|p| p.name == "self");
                    if is_static {
                        let mangled = format!("{}__{}", e.name, method.name);
                        let arc_method = Arc::new(method.clone());
                        local_functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        global_functions.insert(mangled.clone(), Arc::clone(&arc_method));
                        exports.insert(
                            mangled.clone(),
                            Value::Function {
                                name: mangled,
                                def: arc_method,
                                captured_env: Arc::new(HashMap::new()),
                            },
                        );
                    }
                }
                // Register enum variant constructors as EnumName__VariantName
                for variant in &e.variants {
                    let mangled = format!("{}__{}", e.name, variant.name);
                    // Export variant as an enum value (unit variant) or constructor
                    let variant_value =
                        if variant.fields.is_none() || variant.fields.as_ref().is_none_or(|f| f.is_empty()) {
                            // Unit variant - export as enum value
                            Value::Enum {
                                enum_name: e.name.clone(),
                                variant: variant.name.clone(),
                                payload: None,
                            }
                        } else {
                            // Variant with fields - export as constructor
                            Value::Constructor {
                                class_name: mangled.clone(),
                            }
                        };
                    exports.insert(mangled.clone(), variant_value.clone());
                    env.insert(mangled, variant_value);
                }
            }
            Node::Macro(m) => {
                // Register macro in exports with special prefix
                exports.insert(format!("macro:{}", m.name), Value::Str(format!("macro:{}", m.name)));
                // Also register in the thread-local USER_MACROS
                crate::interpreter::USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));
            }
            Node::Extern(ext) => {
                // Register extern function declarations in the global EXTERN_FUNCTIONS
                crate::interpreter::EXTERN_FUNCTIONS.with(|cell| {
                    let mut externs = cell.borrow_mut();
                    externs.insert(ext.name.clone());
                    if crate::is_debug_mode() && std::env::var("SIMPLE_DEBUG_EXTERN_REGISTRATION").is_ok() {
                        eprintln!(
                            "[DEBUG] Registered extern function from module: {} (total: {})",
                            ext.name,
                            externs.len()
                        );
                    }
                });
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
    local_functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    local_classes: &mut HashMap<String, Arc<ClassDef>>,
    local_enums: &Enums,
    impl_methods: &ImplMethods,
    global_functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    global_classes: &mut HashMap<String, Arc<ClassDef>>,
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
                    exports,
                )?;
            }
            Node::Let(stmt) => {
                // Evaluate module-level let statements (for global variables)
                if let Some(init) = &stmt.value {
                    if let Ok(value) =
                        evaluate_expr(init, env, local_functions, local_classes, local_enums, impl_methods)
                    {
                        // Handle all pattern types (Identifier, MutIdentifier, Typed)
                        if let Some(name) = get_pattern_name(&stmt.pattern) {
                            env.insert(name.clone(), value.clone());
                            // Export constants so they're visible after import
                            exports.insert(name.clone(), value.clone());
                            // Sync module-level vars to MODULE_GLOBALS so that functions
                            // within this module can read/write them even when called from
                            // other modules (where the function's captured_env may not be used).
                            MODULE_GLOBALS.with(|cell| {
                                cell.borrow_mut().insert(name.clone(), value);
                            });
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
                        env.insert(name.clone(), value.clone());
                        // Export vars so they're visible after import
                        exports.insert(name.clone(), value.clone());
                        // Sync to MODULE_GLOBALS for the same reason as Node::Let above
                        MODULE_GLOBALS.with(|cell| {
                            cell.borrow_mut().insert(name.clone(), value);
                        });
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
    global_functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    global_classes: &mut HashMap<String, Arc<ClassDef>>,
    global_enums: &mut Enums,
    exports: &mut HashMap<String, Value>,
) -> Result<(), CompileError> {
    // Skip type-only imports at runtime - they're only for compile-time type checking
    if use_stmt.is_type_only {
        trace!("Skipping type-only import: {:?}", use_stmt.path);
        return Ok(());
    }

    // Note: `use lazy` is parsed but loaded eagerly in the Rust bootstrap interpreter.
    // Actual lazy/deferred loading is implemented in the Simple interpreter
    // (src/compiler/10.frontend/core/interpreter/eval_stmts.spl).
    if use_stmt.is_lazy {
        trace!("Loading lazy import eagerly (Rust bootstrap): {:?}", use_stmt.path);
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
            if let Value::Dict(module_exports) = &value {
                for (name, export_value) in module_exports {
                    if let Value::Function { def, .. } = export_value {
                        global_functions.insert(name.clone(), Arc::clone(def));
                    }
                    env.insert(name.clone(), export_value.clone());
                    exports.insert(name.clone(), export_value.clone());
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
    global_functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    global_classes: &mut HashMap<String, Arc<ClassDef>>,
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

/// Export functions with filtered environment captured.
/// Returns the `Arc<FunctionDef>` map so the caller can reuse the same Arc instances
/// for caching (avoids creating duplicate Arc wrappers).
pub(super) fn export_functions(
    local_functions: &HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    filtered_env: &Env,
    exports: &mut HashMap<String, Value>,
    env: &mut Env,
) -> HashMap<String, Arc<simple_parser::ast::FunctionDef>> {
    // First pass: Add all module functions to env with empty captured_env
    // We pre-build shared Arc<FunctionDef> per function so both passes share the same allocation.
    trace!(functions = local_functions.len(), "First pass: adding functions to env");
    let shared_defs: HashMap<String, Arc<simple_parser::ast::FunctionDef>> = local_functions
        .iter()
        .map(|(name, f)| (name.clone(), Arc::clone(f)))
        .collect();
    for (name, shared_def) in &shared_defs {
        env.insert(
            name.clone(),
            Value::Function {
                name: name.clone(),
                def: shared_def.clone(),
                captured_env: Arc::new(Env::new()),
            },
        );
    }

    // Second pass: Export public functions with filtered environment captured
    // Only export functions marked as 'pub' - others need explicit export statements
    trace!(
        functions = local_functions.len(),
        env_size = filtered_env.len(),
        "Second pass: exporting public functions"
    );
    let shared_env = Arc::new(filtered_env.clone());
    let mut exported_count = 0;
    for (name, shared_def) in &shared_defs {
        let func_with_env = Value::Function {
            name: name.clone(),
            def: shared_def.clone(),
            captured_env: shared_env.clone(),
        };
        // Always add to env (for internal module use)
        env.insert(name.clone(), func_with_env.clone());

        // Export all top-level functions by default (Simple convention: all functions are public unless private)
        // This matches the Simple compiler's behavior where functions don't need `pub` keyword
        exports.insert(name.clone(), func_with_env);
        exported_count += 1;
    }
    trace!(
        total_functions = local_functions.len(),
        exported = exported_count,
        "Finished exporting public functions"
    );

    // Return the shared Arc defs so the caller can reuse them for caching
    shared_defs
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
