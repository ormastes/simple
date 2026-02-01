//! Core module evaluation logic for the Simple interpreter.
//!
//! This module handles:
//! - Decorator application
//! - Top-level item registration (functions, classes, enums, traits, etc.)
//! - Module initialization and execution
//! - Main function discovery and execution

use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::{ClassDef, EnumDef, Expr, FunctionDef, ImportTarget, Node, UnitDef};

use crate::aop_config::AopConfig;
use crate::di::DiConfig;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{Env, Value};

use super::{
    await_value, bind_pattern_value, check_enum_exhaustiveness, control_to_value, create_range_object,
    dispatch_context_method, enter_class_scope, evaluate_expr, evaluate_macro_invocation,
    evaluate_method_call_with_self_update, exec_block, exec_context, exec_for, exec_function, exec_if, exec_loop,
    exec_match, exec_node, exec_while, exec_with, exit_class_scope, find_and_exec_method, get_di_config,
    get_import_alias, get_pattern_name, get_type_name, handle_functional_update, handle_method_call_with_self_update,
    is_unit_type, iter_to_vec, load_and_merge_module, message_to_value, normalize_index, pattern_matches,
    preprocess_macro_contract_at_definition, register_trait_impl, slice_collection, spawn_actor_with_expr,
    spawn_future_with_callable, spawn_future_with_callable_and_env, spawn_future_with_expr,
    take_macro_introduced_symbols, try_method_missing, type_to_family_name, validate_unit_constraints,
    validate_unit_type, with_effect_context, Dimension, ExternFunctions, ImplMethods, Macros, TraitImplRegistry,
    TraitImpls, Traits, UnitArithmeticRules, UnitFamilies, UnitFamilyInfo, Units, BASE_UNIT_DIMENSIONS, BDD_AFTER_EACH,
    BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_COUNTS, BDD_INDENT, BDD_LAZY_VALUES, BDD_SHARED_EXAMPLES,
    BLANKET_IMPL_METHODS, COMPOUND_UNIT_DIMENSIONS, CONST_NAMES, EXTERN_FUNCTIONS, MACRO_DEFINITION_ORDER, MIXINS,
    TRAIT_IMPLS, MODULE_GLOBALS, SI_BASE_UNITS, UNIT_FAMILY_ARITHMETIC, UNIT_FAMILY_CONVERSIONS, UNIT_SUFFIX_TO_FAMILY,
    USER_MACROS,
};

type Enums = HashMap<String, EnumDef>;

/// Call a value (function or lambda) with evaluated arguments.
/// Used for decorator application where we have Value arguments, not AST Arguments.
pub(super) fn call_value_with_args(
    callee: &Value,
    args: Vec<Value>,
    _env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match callee {
        Value::Lambda {
            params,
            body,
            env: captured,
        } => {
            // Execute lambda with given args
            let mut local_env = captured.clone();
            for (i, param) in params.iter().enumerate() {
                if let Some(arg) = args.get(i) {
                    local_env.insert(param.clone(), arg.clone());
                }
            }
            evaluate_expr(body, &mut local_env, functions, classes, enums, impl_methods)
        }
        Value::Function { def, captured_env, .. } => {
            // Execute function with given args, using the captured environment for closure
            let mut local_env = captured_env.clone();
            for (i, param) in def.params.iter().enumerate() {
                if let Some(arg) = args.get(i) {
                    local_env.insert(param.name.clone(), arg.clone());
                }
            }
            // Execute the function body
            let result = exec_block(&def.body, &mut local_env, functions, classes, enums, impl_methods);
            control_to_value(result)
        }
        _ => Err(crate::error::factory::not_callable(callee.type_name())),
    }
}

/// Built-in extern functions that are always available without explicit declaration.
/// These are the "prelude" functions - print, math, and conversion utilities.
pub const PRELUDE_EXTERN_FUNCTIONS: &[&str] = &[
    // I/O functions (print now adds newline by default, like Python)
    "print",      // prints with newline (new behavior)
    "print_raw",  // prints without newline (for old print behavior)
    "eprint",     // stderr with newline (new behavior)
    "eprint_raw", // stderr without newline (for old eprint behavior)
    "dprint",     // debug print (only outputs when --debug flag is set)
    "input",
    // Deprecated (show error messages)
    "println",  // deprecated: use print instead
    "eprintln", // deprecated: use eprint instead
    // Math functions
    "abs",
    "min",
    "max",
    "sqrt",
    "floor",
    "ceil",
    "pow",
    // Conversion functions
    "to_string",
    "to_int",
    // Process control
    "exit",
    "panic",
    // Memory functions
    "memory_usage",
    "memory_limit",
    "memory_usage_percent",
    "is_memory_limited",
    "default_memory_limit",
    "format_bytes",
    "parse_memory_size",
];

/// Main module evaluation implementation.
/// Processes all top-level items and executes the main function if present.
pub(super) fn evaluate_module_impl(items: &[Node]) -> Result<i32, CompileError> {
    // Clear const names, extern functions, and moved variables from previous runs
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());
    super::clear_moved_vars();
    EXTERN_FUNCTIONS.with(|cell| {
        let mut externs = cell.borrow_mut();
        externs.clear();
        // Pre-populate with prelude functions (always available)
        for &name in PRELUDE_EXTERN_FUNCTIONS {
            externs.insert(name.to_string());
        }
    });
    // Clear macro definition order from previous runs
    MACRO_DEFINITION_ORDER.with(|cell| cell.borrow_mut().clear());
    // Clear unit family info from previous runs
    UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow_mut().clear());
    UNIT_FAMILY_CONVERSIONS.with(|cell| cell.borrow_mut().clear());
    UNIT_FAMILY_ARITHMETIC.with(|cell| cell.borrow_mut().clear());
    COMPOUND_UNIT_DIMENSIONS.with(|cell| cell.borrow_mut().clear());
    BASE_UNIT_DIMENSIONS.with(|cell| cell.borrow_mut().clear());
    SI_BASE_UNITS.with(|cell| cell.borrow_mut().clear());
    // Clear module-level globals from previous runs
    MODULE_GLOBALS.with(|cell| cell.borrow_mut().clear());

    let mut env = Env::new();
    let mut functions: HashMap<String, FunctionDef> = HashMap::new();
    let mut classes: HashMap<String, ClassDef> = HashMap::new();
    let mut enums: Enums = HashMap::new();
    let mut impl_methods: ImplMethods = HashMap::new();
    let mut extern_functions: ExternFunctions = HashMap::new();
    let mut macros: Macros = HashMap::new();
    let mut units: Units = HashMap::new();
    let mut unit_families: UnitFamilies = HashMap::new();
    let mut traits: Traits = HashMap::new();
    let mut trait_impls: TraitImpls = HashMap::new();
    let mut trait_impl_registry: HashMap<String, TraitImplRegistry> = HashMap::new();

    // First pass: register all functions (needed for decorator lookup)
    for item in items {
        match item {
            Node::Function(f) => {
                functions.insert(f.name.clone(), f.clone());
            }
            _ => {}
        }
    }

    // Second pass: apply decorators and register other items
    for item in items {
        match item {
            Node::Function(f) => {
                // If function has decorators, apply them
                if !f.decorators.is_empty() {
                    // Create a function value from the original function
                    // For top-level functions, captured_env is empty (they don't capture anything)
                    let func_value = Value::Function {
                        name: f.name.clone(),
                        def: Box::new(f.clone()),
                        captured_env: Env::new(),
                    };

                    // Apply decorators in reverse order (bottom-to-top, outermost last)
                    let mut decorated = func_value;
                    for decorator in f.decorators.iter().rev() {
                        // Skip compiler-directive decorators that aren't evaluated at runtime
                        // @extern is a codegen directive, not a runtime decorator
                        // @deprecated is handled at compile time via HIR lowering
                        if let Expr::Identifier(name) = &decorator.name {
                            if name == "extern" || name == "deprecated" {
                                continue;
                            }
                        }

                        // Evaluate the decorator expression
                        let decorator_fn = evaluate_expr(
                            &decorator.name,
                            &mut env,
                            &mut functions,
                            &mut classes,
                            &enums,
                            &impl_methods,
                        )?;

                        // If decorator has arguments, call it first to get the actual decorator
                        let actual_decorator = if let Some(args) = &decorator.args {
                            let mut arg_values = vec![];
                            for arg in args {
                                arg_values.push(evaluate_expr(
                                    &arg.value,
                                    &mut env,
                                    &mut functions,
                                    &mut classes,
                                    &enums,
                                    &impl_methods,
                                )?);
                            }
                            call_value_with_args(
                                &decorator_fn,
                                arg_values,
                                &env,
                                &mut functions,
                                &mut classes,
                                &enums,
                                &impl_methods,
                            )?
                        } else {
                            decorator_fn
                        };

                        // Call the decorator with the current function value
                        decorated = call_value_with_args(
                            &actual_decorator,
                            vec![decorated],
                            &env,
                            &mut functions,
                            &mut classes,
                            &enums,
                            &impl_methods,
                        )?;
                    }

                    // Store the decorated result in the env
                    env.insert(f.name.clone(), decorated);
                }
            }
            Node::Struct(s) => {
                // Register struct as a constructor-like callable
                // Store in env as Constructor value so it can be called like Point(x, y)
                env.insert(
                    s.name.clone(),
                    Value::Constructor {
                        class_name: s.name.clone(),
                    },
                );
                // Also register as a class so instantiation works
                classes.insert(
                    s.name.clone(),
                    ClassDef {
                        span: s.span,
                        name: s.name.clone(),
                        generic_params: Vec::new(),
                        where_clause: vec![],
                        fields: s.fields.clone(),
                        methods: s.methods.clone(),
                        parent: None,
                        visibility: s.visibility,
                        effects: Vec::new(),
                        attributes: Vec::new(),
                        doc_comment: None,
                        invariant: None,
                        macro_invocations: Vec::new(),
                        mixins: vec![],
                        is_generic_template: false,
                        specialization_of: None,
                        type_bindings: std::collections::HashMap::new(),
                    },
                );
            }
            Node::Enum(e) => {
                enums.insert(e.name.clone(), e.clone());
                // Also register in env so EnumName.VariantName syntax works
                env.insert(
                    e.name.clone(),
                    Value::EnumType {
                        enum_name: e.name.clone(),
                    },
                );
            }
            Node::Class(c) => {
                // Enter class scope for field introduction tracking
                enter_class_scope(c.name.clone());

                // Process macro invocations in class body to get introduced fields
                let mut additional_fields = Vec::new();
                for macro_invoc in &c.macro_invocations {
                    // Evaluate the macro invocation
                    let _result = evaluate_macro_invocation(
                        &macro_invoc.name,
                        &macro_invoc.args,
                        &mut env,
                        &mut functions,
                        &mut classes,
                        &enums,
                        &impl_methods,
                    )?;

                    // Check for introduced fields from macro contract
                    if let Some(contract_result) = take_macro_introduced_symbols() {
                        additional_fields.extend(contract_result.introduced_fields);
                    }
                }

                // Exit class scope
                exit_class_scope();

                // Inject mixin fields and methods into class (with transitive resolution)
                let mut mixin_fields = Vec::new();
                let mut mixin_methods = Vec::new();
                if !c.mixins.is_empty() {
                    let existing_method_names: std::collections::HashSet<_> =
                        c.methods.iter().map(|m| m.name.clone()).collect();
                    let mut seen_field_names: std::collections::HashSet<String> =
                        c.fields.iter().map(|f| f.name.clone()).collect();
                    let mut seen_method_names = existing_method_names;
                    MIXINS.with(|cell| {
                        let mixins_registry = cell.borrow();
                        // Transitive resolution: BFS through mixin dependencies
                        let mut seen_mixins = std::collections::HashSet::new();
                        let mut queue: std::collections::VecDeque<String> =
                            c.mixins.iter().map(|m| m.name.clone()).collect();
                        while let Some(mixin_name) = queue.pop_front() {
                            if !seen_mixins.insert(mixin_name.clone()) {
                                continue; // Diamond dedup
                            }
                            if let Some(mixin_def) = mixins_registry.get(&mixin_name) {
                                // Queue transitive dependencies
                                for req in &mixin_def.required_mixins {
                                    queue.push_back(req.clone());
                                }
                                // Collect fields (dedup by name)
                                for field in &mixin_def.fields {
                                    if seen_field_names.insert(field.name.clone()) {
                                        mixin_fields.push(field.clone());
                                    }
                                }
                                // Collect methods (skip if already defined)
                                for method in &mixin_def.methods {
                                    if seen_method_names.insert(method.name.clone()) {
                                        mixin_methods.push(method.clone());
                                    }
                                }
                            }
                        }
                    });
                }

                // Create class with additional fields/methods from macros and mixins
                let has_additions = !additional_fields.is_empty() || !mixin_fields.is_empty() || !mixin_methods.is_empty();
                let final_class = if !has_additions {
                    c.clone()
                } else {
                    let mut updated = c.clone();
                    // Prepend mixin fields before class fields
                    let mut all_extra_fields = mixin_fields;
                    all_extra_fields.extend(additional_fields);
                    updated.fields.splice(0..0, all_extra_fields);
                    updated.methods.extend(mixin_methods);
                    updated
                };

                classes.insert(final_class.name.clone(), final_class.clone());
                // Store in env as Constructor value so it can be called like MyClass()
                env.insert(
                    final_class.name.clone(),
                    Value::Constructor {
                        class_name: final_class.name.clone(),
                    },
                );
            }
            Node::Impl(impl_block) => {
                // Check if this is a blanket impl: has #[default] attribute AND generic params
                // Blanket impls apply to any type that doesn't have a concrete impl
                let is_default_impl = impl_block.attributes.iter().any(|attr| attr.name == "default");
                let has_generic_params = !impl_block.generic_params.is_empty();
                let is_blanket_impl = is_default_impl && has_generic_params;

                if is_blanket_impl {
                    // Register as blanket impl - keyed by trait name
                    if let Some(ref trait_name) = impl_block.trait_name {
                        BLANKET_IMPL_METHODS.with(|cell| {
                            let mut blanket_impls = cell.borrow_mut();
                            let methods = blanket_impls.entry(trait_name.clone()).or_insert_with(Vec::new);
                            methods.extend(impl_block.methods.clone());
                        });
                    }
                } else {
                    // Regular impl - register as before
                    register_trait_impl(&mut trait_impl_registry, impl_block)?;
                    let type_name = get_type_name(&impl_block.target_type);
                    let methods = impl_methods.entry(type_name.clone()).or_insert_with(Vec::new);
                    for method in &impl_block.methods {
                        methods.push(method.clone());
                    }

                    // Also add impl methods to class/struct definition for Constructor method dispatch
                    if let Some(class_def) = classes.get_mut(&type_name) {
                        class_def.methods.extend(impl_block.methods.clone());
                    }

                    // If this is a trait implementation, verify and register it
                    if let Some(ref trait_name) = impl_block.trait_name {
                        // Verify trait exists
                        if let Some(trait_def) = traits.get(trait_name) {
                            // Check all abstract trait methods are implemented
                            let impl_method_names: std::collections::HashSet<_> =
                                impl_block.methods.iter().map(|m| m.name.clone()).collect();

                            for trait_method in &trait_def.methods {
                                // Only require implementation of abstract methods
                                // Note: method may exist in another impl block, so we warn via tracing
                                // instead of returning an error
                                if trait_method.is_abstract && !impl_method_names.contains(&trait_method.name) {
                                    tracing::debug!("type `{}` missing method `{}` from trait `{}`", type_name, trait_method.name, trait_name);
                                }
                            }

                            // Build combined methods: impl methods + default trait methods
                            let mut combined_methods = impl_block.methods.clone();
                            for trait_method in &trait_def.methods {
                                // Add default implementations that weren't overridden
                                if !trait_method.is_abstract && !impl_method_names.contains(&trait_method.name) {
                                    combined_methods.push(trait_method.clone());
                                    // Also add to impl_methods so method dispatch can find it
                                    methods.push(trait_method.clone());
                                }
                            }

                            // Store the trait implementation with combined methods
                            trait_impls.insert((trait_name.clone(), type_name.clone()), combined_methods.clone());

                            // Also store in thread-local registry for method dispatch
                            TRAIT_IMPLS.with(|cell| {
                                cell.borrow_mut().insert((trait_name.clone(), type_name.clone()), combined_methods);
                            });
                        }
                        // Note: If trait not found, it might be defined in another module
                        // For now, we silently allow this for forward compatibility
                    }
                }
            }
            Node::Extern(ext) => {
                extern_functions.insert(ext.name.clone(), ext.clone());
                EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().insert(ext.name.clone()));
            }
            Node::ExternClass(ec) => {
                // Register extern class as a type for FFI object creation
                // In the interpreter, extern classes are handled via runtime FFI calls
                env.insert(ec.name.clone(), Value::Nil);
            }
            Node::Macro(m) => {
                macros.insert(m.name.clone(), m.clone());
                USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));

                // Track macro definition order for one-pass LL(1) validation (#1304)
                MACRO_DEFINITION_ORDER.with(|cell| cell.borrow_mut().push(m.name.clone()));

                // Process macro contracts at definition time for parameterless macros (#1303)
                // For macros without const parameters, we can process the contract once
                // and cache it, avoiding redundant processing on each invocation.
                // Macros with const params still require invocation-time processing.
                if let Err(e) = preprocess_macro_contract_at_definition(m, &mut env, &functions, &classes) {
                    // Log the error but don't fail - contract will be processed at invocation time
                    // This can happen if the contract references types not yet defined
                    eprintln!("Warning: Could not pre-process contract for macro '{}': {}", m.name, e);
                }
            }
            Node::Trait(t) => {
                // Register trait definition for use in impl checking
                traits.insert(t.name.clone(), t.clone());
                env.insert(t.name.clone(), Value::Nil);
            }
            Node::Mixin(mixin_def) => {
                // Register mixin definition in thread-local registry
                MIXINS.with(|cell| {
                    cell.borrow_mut().insert(mixin_def.name.clone(), mixin_def.clone());
                });
            }
            Node::Actor(a) => {
                // Register actor as a class-like type for instantiation
                // Actors have fields (state) and methods like classes
                classes.insert(
                    a.name.clone(),
                    ClassDef {
                        span: a.span,
                        name: a.name.clone(),
                        generic_params: Vec::new(),
                        where_clause: vec![],
                        fields: a.fields.clone(),
                        methods: a.methods.clone(),
                        parent: None,
                        visibility: a.visibility,
                        effects: Vec::new(),
                        attributes: vec![],
                        doc_comment: None,
                        invariant: None,
                        macro_invocations: Vec::new(),
                        mixins: vec![],
                        is_generic_template: false,
                        specialization_of: None,
                        type_bindings: std::collections::HashMap::new(),
                    },
                );
                env.insert(
                    a.name.clone(),
                    Value::Object {
                        class: a.name.clone(),
                        fields: Arc::new(HashMap::new()),
                    },
                );
            }
            Node::TypeAlias(t) => {
                // Type aliases are handled at type-check time
                // Store the alias name for reference
                env.insert(t.name.clone(), Value::Nil);
            }
            Node::Unit(u) => {
                // Unit types define a newtype wrapper with a literal suffix
                // Register the unit type name and its suffix for later use
                units.insert(u.suffix.clone(), u.clone());
                env.insert(u.name.clone(), Value::Nil);
            }
            Node::UnitFamily(uf) => {
                // Unit family defines multiple related units with conversion factors
                // Register each variant as a standalone unit
                let mut conversions = HashMap::new();
                for variant in &uf.variants {
                    // Create a synthetic UnitDef for each variant
                    // Unit families have a single base type
                    let unit_def = UnitDef {
                        span: uf.span,
                        name: format!("{}_{}", uf.name, variant.suffix),
                        base_types: vec![uf.base_type.clone()],
                        suffix: variant.suffix.clone(),
                        visibility: uf.visibility,
                    };
                    units.insert(variant.suffix.clone(), unit_def);
                    // Store conversion factor for to_X() methods
                    conversions.insert(variant.suffix.clone(), variant.factor);
                    // Register suffix -> family mapping in thread-local for expression evaluation
                    UNIT_SUFFIX_TO_FAMILY.with(|cell| {
                        cell.borrow_mut().insert(variant.suffix.clone(), uf.name.clone());
                    });
                }
                // Store the family with all conversion factors
                unit_families.insert(
                    uf.name.clone(),
                    UnitFamilyInfo {
                        base_type: uf.base_type.clone(),
                        conversions: conversions.clone(),
                    },
                );
                // Register family conversions in thread-local for method dispatch
                UNIT_FAMILY_CONVERSIONS.with(|cell| {
                    cell.borrow_mut().insert(uf.name.clone(), conversions);
                });
                // Store arithmetic rules if present
                if let Some(arith) = &uf.arithmetic {
                    let rules = UnitArithmeticRules {
                        binary_rules: arith
                            .binary_rules
                            .iter()
                            .map(|r| {
                                (
                                    r.op,
                                    type_to_family_name(&r.operand_type),
                                    type_to_family_name(&r.result_type),
                                )
                            })
                            .collect(),
                        unary_rules: arith
                            .unary_rules
                            .iter()
                            .map(|r| (r.op, type_to_family_name(&r.result_type)))
                            .collect(),
                    };
                    UNIT_FAMILY_ARITHMETIC.with(|cell| {
                        cell.borrow_mut().insert(uf.name.clone(), rules);
                    });
                }
                // Store the family name for reference
                env.insert(uf.name.clone(), Value::Nil);
                // Register this as a base dimension (self-referential)
                // e.g., "length" has dimension {length: 1}
                BASE_UNIT_DIMENSIONS.with(|cell| {
                    cell.borrow_mut().insert(uf.name.clone(), Dimension::base(&uf.name));
                });
                // Register the base unit (factor = 1.0) for SI prefix support
                // e.g., for length: "m" -> "length", so "km" can be parsed as "k" + "m"
                for variant in &uf.variants {
                    if (variant.factor - 1.0).abs() < f64::EPSILON {
                        SI_BASE_UNITS.with(|cell| {
                            cell.borrow_mut().insert(variant.suffix.clone(), uf.name.clone());
                        });
                        break; // Only one base unit per family
                    }
                }
            }
            Node::CompoundUnit(cu) => {
                // Compound unit defines a derived unit (e.g., velocity = length / time)
                // Register the compound unit name in the environment
                env.insert(cu.name.clone(), Value::Nil);
                // Store arithmetic rules if present
                if let Some(arith) = &cu.arithmetic {
                    let rules = UnitArithmeticRules {
                        binary_rules: arith
                            .binary_rules
                            .iter()
                            .map(|r| {
                                (
                                    r.op,
                                    type_to_family_name(&r.operand_type),
                                    type_to_family_name(&r.result_type),
                                )
                            })
                            .collect(),
                        unary_rules: arith
                            .unary_rules
                            .iter()
                            .map(|r| (r.op, type_to_family_name(&r.result_type)))
                            .collect(),
                    };
                    UNIT_FAMILY_ARITHMETIC.with(|cell| {
                        cell.borrow_mut().insert(cu.name.clone(), rules);
                    });
                }
                // Convert the UnitExpr to a Dimension and store it
                let dimension = Dimension::from_unit_expr(&cu.expr);
                COMPOUND_UNIT_DIMENSIONS.with(|cell| {
                    cell.borrow_mut().insert(cu.name.clone(), dimension);
                });
            }
            Node::Let(let_stmt) => {
                use super::Control;
                if let Control::Return(val) =
                    exec_node(item, &mut env, &mut functions, &mut classes, &enums, &impl_methods)?
                {
                    return val.as_int().map(|v| v as i32);
                }
                // Sync module-level variables to MODULE_GLOBALS for function/method access
                // Both mutable (var) and immutable (val) need to be accessible
                {
                    if let Some(name) = get_pattern_name(&let_stmt.pattern) {
                        if let Some(value) = env.get(&name) {
                            MODULE_GLOBALS.with(|cell| {
                                cell.borrow_mut().insert(name, value.clone());
                            });
                        }
                    }
                }
            }
            Node::Const(_)
            | Node::Static(_)
            | Node::Assignment(_)
            | Node::If(_)
            | Node::For(_)
            | Node::While(_)
            | Node::Loop(_)
            | Node::Match(_)
            | Node::Context(_)
            | Node::With(_) => {
                use super::Control;
                if let Control::Return(val) =
                    exec_node(item, &mut env, &mut functions, &mut classes, &enums, &impl_methods)?
                {
                    return val.as_int().map(|v| v as i32);
                }
            }
            Node::Return(ret) => {
                if let Some(expr) = &ret.value {
                    let val = evaluate_expr(expr, &mut env, &mut functions, &mut classes, &enums, &impl_methods)?;
                    return val.as_int().map(|v| v as i32);
                }
                return Ok(0);
            }
            Node::Expression(expr) => {
                if let Expr::FunctionalUpdate { target, method, args } = expr {
                    if let Some((name, new_value)) = handle_functional_update(
                        target,
                        method,
                        args,
                        &mut env,
                        &mut functions,
                        &mut classes,
                        &enums,
                        &impl_methods,
                    )? {
                        env.insert(name, new_value);
                        continue;
                    }
                }
                // Handle method calls on objects - need to persist mutations to self
                let (_, update) = handle_method_call_with_self_update(
                    expr,
                    &mut env,
                    &mut functions,
                    &mut classes,
                    &enums,
                    &impl_methods,
                )?;
                if let Some((name, new_self)) = update {
                    env.insert(name, new_self);
                }

                // Register macro-introduced symbols (#1303)
                // After macro invocation, check if any symbols were introduced
                if let Some(contract_result) = take_macro_introduced_symbols() {
                    // Register introduced functions
                    for (name, func_def) in contract_result.introduced_functions {
                        functions.insert(name.clone(), func_def);
                        // Also add to env as a callable
                        env.insert(
                            name.clone(),
                            Value::Function {
                                name: name.clone(),
                                def: Box::new(functions.get(&name).unwrap().clone()),
                                captured_env: Env::new(),
                            },
                        );
                    }

                    // Register introduced classes
                    for (name, class_def) in contract_result.introduced_classes {
                        classes.insert(name.clone(), class_def);
                        // Add to env as a constructor
                        env.insert(name.clone(), Value::Constructor { class_name: name });
                    }

                    // Register introduced types (stored as Nil for now)
                    for (name, _ty) in contract_result.introduced_types {
                        env.insert(name, Value::Nil);
                    }

                    // Register introduced variables
                    for (name, _ty, _is_const) in contract_result.introduced_vars {
                        // Initialize with Nil placeholder
                        // The macro's emit block should assign the actual value
                        env.insert(name, Value::Nil);
                    }
                }
            }
            Node::Break(_) => {
                let ctx = ErrorContext::new()
                    .with_code(codes::BREAK_OUTSIDE_LOOP)
                    .with_help("break statement can only be used inside a loop");
                return Err(CompileError::semantic_with_context(
                    "break outside of loop".to_string(),
                    ctx,
                ));
            }
            Node::Continue(_) => {
                let ctx = ErrorContext::new()
                    .with_code(codes::CONTINUE_OUTSIDE_LOOP)
                    .with_help("continue statement can only be used inside a loop");
                return Err(CompileError::semantic_with_context(
                    "continue outside of loop".to_string(),
                    ctx,
                ));
            }
            Node::Assert(assert_stmt) => {
                // Evaluate the condition
                let condition_value = evaluate_expr(
                    &assert_stmt.condition,
                    &mut env,
                    &mut functions,
                    &mut classes,
                    &enums,
                    &impl_methods,
                )?;
                match condition_value {
                    Value::Bool(true) => {
                        // Assertion passed, continue
                    }
                    Value::Bool(false) => {
                        // Assertion failed - panic with message
                        let base_msg = "Assertion violation: condition failed";
                        let msg = if let Some(ref custom_msg) = assert_stmt.message {
                            format!("{} ({})", base_msg, custom_msg)
                        } else {
                            base_msg.to_string()
                        };
                        panic!("{}", msg);
                    }
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::TYPE_MISMATCH)
                            .with_help("assert condition must be a boolean");
                        return Err(CompileError::semantic_with_context(
                            "assert condition must be a boolean".to_string(),
                            ctx,
                        ));
                    }
                }
            }
            // Module system nodes
            Node::UseStmt(use_stmt) => {
                // Handle runtime module loading
                // Determine the binding name (alias or imported item name)
                let binding_name = match &use_stmt.target {
                    ImportTarget::Single(name) => name.clone(),
                    ImportTarget::Aliased { alias, .. } => alias.clone(),
                    ImportTarget::Glob | ImportTarget::Group(_) => {
                        // For glob/group imports, use module name
                        use_stmt
                            .path
                            .segments
                            .last()
                            .cloned()
                            .unwrap_or_else(|| "module".to_string())
                    }
                };

                // Try to load the module and merge its definitions into global state
                // Use the current file path from thread-local storage for module resolution
                let current_file = super::get_current_file();
                match load_and_merge_module(
                    use_stmt,
                    current_file.as_deref(),
                    &mut functions,
                    &mut classes,
                    &mut enums,
                ) {
                    Ok(value) => {
                        // Unpack module exports into current namespace
                        // For Group imports, only import specified items
                        // For Glob imports, import everything
                        // For Single/Aliased imports, don't unpack (just bind the module)
                        match &use_stmt.target {
                            ImportTarget::Group(items) => {
                                // Group import: use module.{Item1, Item2}
                                // Only add the specified items to env
                                if let Value::Dict(exports) = &value {
                                    for item_target in items {
                                        let item_name = match item_target {
                                            ImportTarget::Single(name) => name.clone(),
                                            ImportTarget::Aliased { name, alias } => {
                                                // Import with alias: {Item as alias}
                                                if let Some(export_value) = exports.get(name) {
                                                    env.insert(alias.clone(), export_value.clone());
                                                    MODULE_GLOBALS.with(|cell| {
                                                        cell.borrow_mut().insert(alias.clone(), export_value.clone());
                                                    });
                                                }
                                                continue;
                                            }
                                            _ => continue, // Nested groups not supported
                                        };
                                        if let Some(export_value) = exports.get(&item_name) {
                                            env.insert(item_name.clone(), export_value.clone());
                                            MODULE_GLOBALS.with(|cell| {
                                                cell.borrow_mut().insert(item_name.clone(), export_value.clone());
                                            });
                                        }
                                    }
                                }
                            }
                            ImportTarget::Glob => {
                                // Glob import: use module.*
                                // Add all exports to env
                                if let Value::Dict(exports) = &value {
                                    for (name, export_value) in exports {
                                        env.insert(name.clone(), export_value.clone());
                                        MODULE_GLOBALS.with(|cell| {
                                            cell.borrow_mut().insert(name.clone(), export_value.clone());
                                        });
                                    }
                                }
                            }
                            ImportTarget::Single(_) | ImportTarget::Aliased { .. } => {
                                // Single/Aliased import: use module or use module as alias
                                // Don't unpack - just bind the module dict
                            }
                        }
                        // Also keep the module dict under its name for qualified access
                        env.insert(binding_name.clone(), value.clone());
                        // Sync module binding to MODULE_GLOBALS so functions can access it
                        MODULE_GLOBALS.with(|cell| {
                            cell.borrow_mut().insert(binding_name.clone(), value);
                        });
                    }
                    Err(e) => {
                        // Module loading failed - log and use empty dict as fallback
                        tracing::debug!("Module loading failed for '{}': {:?}", binding_name, e);
                        let empty = Value::Dict(HashMap::new());
                        env.insert(binding_name.clone(), empty.clone());
                        MODULE_GLOBALS.with(|cell| {
                            cell.borrow_mut().insert(binding_name.clone(), empty);
                        });
                    }
                }
            }
            Node::InterfaceBinding(binding) => {
                // Store interface binding for static polymorphism dispatch
                // bind Interface = ImplType
                use crate::interpreter::INTERFACE_BINDINGS;
                let impl_type_name = match &binding.impl_type {
                    simple_parser::ast::Type::Simple(name) => name.clone(),
                    simple_parser::ast::Type::Generic { name, .. } => name.clone(),
                    _ => format!("{:?}", binding.impl_type),
                };
                INTERFACE_BINDINGS.with(|bindings| {
                    bindings
                        .borrow_mut()
                        .insert(binding.interface_name.clone(), impl_type_name);
                });
            }
            Node::LiteralFunction(lit_fn) => {
                // Register literal function for custom string suffix handling
                use super::interpreter_state::{LITERAL_FUNCTIONS, LiteralFunctionInfo};
                LITERAL_FUNCTIONS.with(
                    |cell: &std::cell::RefCell<std::collections::HashMap<String, LiteralFunctionInfo>>| {
                        cell.borrow_mut().insert(
                            lit_fn.suffix.clone(),
                            LiteralFunctionInfo {
                                suffix: lit_fn.suffix.clone(),
                                return_type: lit_fn.return_type.clone(),
                                param_name: lit_fn.param_name.clone(),
                                body: lit_fn.body.clone(),
                            },
                        );
                    },
                );
            }
            Node::ModDecl(mod_decl) => {
                // Handle inline modules with a body
                if let Some(body_items) = &mod_decl.body {
                    // Create a module dict to hold the module's exports
                    let mut module_dict: HashMap<String, Value> = HashMap::new();

                    // Process items in the inline module body
                    for item in body_items {
                        match item {
                            Node::Function(f) => {
                                // Register function in parent scope with module prefix for internal use
                                let prefixed_name = format!("{}.{}", mod_decl.name, f.name);
                                functions.insert(prefixed_name, f.clone());

                                // Also add to module dict for module.func() calls
                                let func_value = Value::Function {
                                    name: f.name.clone(),
                                    def: Box::new(f.clone()),
                                    captured_env: Env::new(),
                                };
                                module_dict.insert(f.name.clone(), func_value);
                            }
                            Node::Class(c) => {
                                // Register class in parent scope with module prefix
                                let prefixed_name = format!("{}.{}", mod_decl.name, c.name);
                                classes.insert(prefixed_name, c.clone());
                                classes.insert(c.name.clone(), c.clone()); // Also register unqualified for internal use

                                // Add constructor to module dict
                                module_dict.insert(
                                    c.name.clone(),
                                    Value::Constructor {
                                        class_name: c.name.clone(),
                                    },
                                );
                            }
                            Node::Struct(s) => {
                                // Convert struct to class-like for simple handling
                                let class_def = ClassDef {
                                    span: s.span,
                                    name: s.name.clone(),
                                    generic_params: s.generic_params.clone(),
                                    where_clause: s.where_clause.clone(),
                                    fields: s.fields.clone(),
                                    methods: s.methods.clone(),
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
                                let prefixed_name = format!("{}.{}", mod_decl.name, s.name);
                                classes.insert(prefixed_name, class_def.clone());
                                classes.insert(s.name.clone(), class_def);

                                module_dict.insert(
                                    s.name.clone(),
                                    Value::Constructor {
                                        class_name: s.name.clone(),
                                    },
                                );
                            }
                            Node::Enum(e) => {
                                let prefixed_name = format!("{}.{}", mod_decl.name, e.name);
                                enums.insert(prefixed_name, e.clone());
                                enums.insert(e.name.clone(), e.clone());

                                // Add enum variants to module dict as constructors
                                for variant in &e.variants {
                                    module_dict.insert(
                                        variant.name.clone(),
                                        Value::EnumVariantConstructor {
                                            enum_name: e.name.clone(),
                                            variant_name: variant.name.clone(),
                                        },
                                    );
                                }
                            }
                            Node::Const(c) => {
                                // Evaluate const value and add to module dict
                                if let Ok(val) = evaluate_expr(
                                    &c.value,
                                    &mut env,
                                    &mut functions,
                                    &mut classes,
                                    &enums,
                                    &impl_methods,
                                ) {
                                    module_dict.insert(c.name.clone(), val);
                                }
                            }
                            _ => {
                                // Other items are not yet supported in inline modules
                            }
                        }
                    }

                    // Store module dict in environment
                    env.insert(mod_decl.name.clone(), Value::Dict(module_dict));
                }
                // External module declarations (no body) are handled by the module resolver
            }
            Node::MultiUse(_)
            | Node::CommonUseStmt(_)
            | Node::ExportUseStmt(_)
            | Node::StructuredExportStmt(_)
            | Node::AutoImportStmt(_)
            | Node::RequiresCapabilities(_)
            | Node::HandlePool(_)
            | Node::Bitfield(_)
            | Node::AopAdvice(_)
            | Node::DiBinding(_)
            | Node::ArchitectureRule(_)
            | Node::MockDecl(_)
            | Node::LeanBlock(_)
            | Node::Assume(_)
            | Node::Admit(_)
            | Node::ProofHint(_)
            | Node::Calc(_)
            | Node::ClassAlias(_)
            | Node::FunctionAlias(_)
            | Node::Pass(_)
            | Node::Skip(_)
            | Node::Guard(_)
            | Node::Defer(_)
            | Node::Mixin(_) => {
                // Module system is handled by the module resolver
                // HandlePool is processed at compile time for allocation
                // Bitfield is processed at compile time for bit-level field access
                // AOP nodes are declarative configuration handled at compile time
                // Mixin composition is handled at compile time
                // LeanBlock is embedded Lean code for verification (not runtime)
                // Assume/Admit are verification statements (similar to assert)
                // ProofHint is a tactic hint for Lean (not runtime)
                // Calc is a calculational proof block for Lean (not runtime)
                // ClassAlias/FunctionAlias are compile-time declarations
                // Pass is a no-op statement
                // Defer at module level is a no-op (only meaningful inside function bodies)
                // These are no-ops in the interpreter
            }
        }
    }

    // Check if main is defined as a function and call it
    if let Some(main_func) = functions.get("main").cloned() {
        let result = exec_function(
            &main_func,
            &[], // No arguments
            &mut env,
            &mut functions,
            &mut classes,
            &enums,
            &impl_methods,
            None, // No self context
        )?;
        // Await the result if it's a Promise (async function)
        let result = await_value(result)?;
        // If main returns unit/tuple (void), treat it as exit code 0
        return match &result {
            Value::Tuple(t) if t.is_empty() => Ok(0),
            Value::Nil => Ok(0),
            _ => result.as_int().map(|v| v as i32),
        };
    }

    // Fall back to checking for `main = <value>` binding
    let main_val = env.get("main").cloned().unwrap_or(Value::Int(0));
    // Await the value if it's a Promise (async expression result)
    let main_val = await_value(main_val)?;
    let main_val = main_val.as_int()? as i32;
    Ok(main_val)
}
