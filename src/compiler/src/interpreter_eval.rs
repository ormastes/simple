//! Core module evaluation logic for the Simple interpreter.
//!
//! This module handles:
//! - Decorator application
//! - Top-level item registration (functions, classes, enums, traits, etc.)
//! - Module initialization and execution
//! - Main function discovery and execution

use std::collections::HashMap;

use simple_parser::ast::{
    ClassDef, EnumDef, Expr, FunctionDef, ImportTarget, Node, UnitDef,
};

use crate::aop_config::AopConfig;
use crate::di::DiConfig;
use crate::error::CompileError;
use crate::value::{Env, Value};

use super::{
    bind_pattern_value, check_enum_exhaustiveness, control_to_value, create_range_object,
    dispatch_context_method, evaluate_expr, evaluate_method_call_with_self_update,
    exec_block, exec_context, exec_for, exec_function, exec_if, exec_loop, exec_match,
    exec_node, exec_while, exec_with, find_and_exec_method, get_di_config, get_import_alias,
    get_pattern_name, get_type_name, handle_functional_update,
    handle_method_call_with_self_update, is_unit_type, iter_to_vec, load_and_merge_module,
    message_to_value, normalize_index, pattern_matches, register_trait_impl, slice_collection,
    spawn_actor_with_expr, spawn_future_with_callable, spawn_future_with_callable_and_env,
    spawn_future_with_expr, take_macro_introduced_symbols, try_method_missing, type_to_family_name,
    validate_unit_constraints, validate_unit_type, with_effect_context, Dimension,
    ExternFunctions, ImplMethods, Macros, TraitImplRegistry, TraitImpls, Traits,
    UnitArithmeticRules, UnitFamilies, UnitFamilyInfo, Units, BASE_UNIT_DIMENSIONS,
    BDD_AFTER_EACH, BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_COUNTS, BDD_INDENT, BDD_LAZY_VALUES,
    BDD_SHARED_EXAMPLES, COMPOUND_UNIT_DIMENSIONS, CONST_NAMES, EXTERN_FUNCTIONS,
    MACRO_DEFINITION_ORDER, MODULE_GLOBALS, SI_BASE_UNITS, UNIT_FAMILY_ARITHMETIC,
    UNIT_FAMILY_CONVERSIONS, UNIT_SUFFIX_TO_FAMILY, USER_MACROS,
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
            evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)
        }
        Value::Function {
            def, captured_env, ..
        } => {
            // Execute function with given args, using the captured environment for closure
            let mut local_env = captured_env.clone();
            for (i, param) in def.params.iter().enumerate() {
                if let Some(arg) = args.get(i) {
                    local_env.insert(param.name.clone(), arg.clone());
                }
            }
            // Execute the function body
            let result = exec_block(
                &def.body,
                &mut local_env,
                functions,
                classes,
                enums,
                impl_methods,
            );
            control_to_value(result)
        }
        _ => Err(CompileError::Semantic(format!(
            "cannot call value of type {}",
            callee.type_name()
        ))),
    }
}

/// Built-in extern functions that are always available without explicit declaration.
/// These are the "prelude" functions - print, math, and conversion utilities.
pub const PRELUDE_EXTERN_FUNCTIONS: &[&str] = &[
    // I/O functions
    "print",
    "println",
    "eprint",
    "eprintln",
    "input",
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
                        // Evaluate the decorator expression
                        let decorator_fn = evaluate_expr(
                            &decorator.name,
                            &env,
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
                                    &env,
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
                        attributes: Vec::new(),
                        doc_comment: None,
                        invariant: None,
                    },
                );
            }
            Node::Enum(e) => {
                enums.insert(e.name.clone(), e.clone());
            }
            Node::Class(c) => {
                classes.insert(c.name.clone(), c.clone());
                // Store in env as Constructor value so it can be called like MyClass()
                env.insert(
                    c.name.clone(),
                    Value::Constructor {
                        class_name: c.name.clone(),
                    },
                );
            }
            Node::Impl(impl_block) => {
                register_trait_impl(&mut trait_impl_registry, impl_block)?;
                let type_name = get_type_name(&impl_block.target_type);
                let methods = impl_methods.entry(type_name.clone()).or_insert_with(Vec::new);
                for method in &impl_block.methods {
                    methods.push(method.clone());
                }

                // If this is a trait implementation, verify and register it
                if let Some(ref trait_name) = impl_block.trait_name {
                    // Verify trait exists
                    if let Some(trait_def) = traits.get(trait_name) {
                        // Check all abstract trait methods are implemented
                        let impl_method_names: std::collections::HashSet<_> = impl_block
                            .methods
                            .iter()
                            .map(|m| m.name.clone())
                            .collect();

                        for trait_method in &trait_def.methods {
                            // Only require implementation of abstract methods
                            if trait_method.is_abstract
                                && !impl_method_names.contains(&trait_method.name)
                            {
                                return Err(CompileError::Semantic(format!(
                                    "type `{}` does not implement required method `{}` from trait `{}`",
                                    type_name, trait_method.name, trait_name
                                )));
                            }
                        }

                        // Build combined methods: impl methods + default trait methods
                        let mut combined_methods = impl_block.methods.clone();
                        for trait_method in &trait_def.methods {
                            // Add default implementations that weren't overridden
                            if !trait_method.is_abstract
                                && !impl_method_names.contains(&trait_method.name)
                            {
                                combined_methods.push(trait_method.clone());
                                // Also add to impl_methods so method dispatch can find it
                                methods.push(trait_method.clone());
                            }
                        }

                        // Store the trait implementation with combined methods
                        trait_impls.insert(
                            (trait_name.clone(), type_name.clone()),
                            combined_methods,
                        );
                    }
                    // Note: If trait not found, it might be defined in another module
                    // For now, we silently allow this for forward compatibility
                }
            }
            Node::Extern(ext) => {
                extern_functions.insert(ext.name.clone(), ext.clone());
                EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().insert(ext.name.clone()));
            }
            Node::Macro(m) => {
                macros.insert(m.name.clone(), m.clone());
                USER_MACROS.with(|cell| cell.borrow_mut().insert(m.name.clone(), m.clone()));

                // Track macro definition order for one-pass LL(1) validation (#1304)
                MACRO_DEFINITION_ORDER.with(|cell| cell.borrow_mut().push(m.name.clone()));

                // Process macro contracts to register introduced symbols (#1303)
                // Note: For now, contracts with const params need invocation-time processing
                // But we can process non-parameterized contracts at definition time
                // TODO: Full integration requires invocation-time symbol registration
            }
            Node::Trait(t) => {
                // Register trait definition for use in impl checking
                traits.insert(t.name.clone(), t.clone());
                env.insert(t.name.clone(), Value::Nil);
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
                        attributes: vec![],
                        doc_comment: None,
                        invariant: None,
                    },
                );
                env.insert(
                    a.name.clone(),
                    Value::Object {
                        class: a.name.clone(),
                        fields: HashMap::new(),
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
                        binary_rules: arith.binary_rules.iter().map(|r| {
                            (r.op, type_to_family_name(&r.operand_type), type_to_family_name(&r.result_type))
                        }).collect(),
                        unary_rules: arith.unary_rules.iter().map(|r| {
                            (r.op, type_to_family_name(&r.result_type))
                        }).collect(),
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
                        binary_rules: arith.binary_rules.iter().map(|r| {
                            (r.op, type_to_family_name(&r.operand_type), type_to_family_name(&r.result_type))
                        }).collect(),
                        unary_rules: arith.unary_rules.iter().map(|r| {
                            (r.op, type_to_family_name(&r.result_type))
                        }).collect(),
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
                // Sync mutable module-level variables to MODULE_GLOBALS for function access
                if let_stmt.mutability.is_mutable() {
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
                    let val =
                        evaluate_expr(expr, &env, &mut functions, &mut classes, &enums, &impl_methods)?;
                    return val.as_int().map(|v| v as i32);
                }
                return Ok(0);
            }
            Node::Expression(expr) => {
                if let Expr::FunctionalUpdate {
                    target,
                    method,
                    args,
                } = expr
                {
                    if let Some((name, new_value)) = handle_functional_update(
                        target,
                        method,
                        args,
                        &env,
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
                    &env,
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
                        env.insert(
                            name.clone(),
                            Value::Constructor {
                                class_name: name,
                            },
                        );
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
                return Err(CompileError::Semantic("break outside of loop".into()));
            }
            Node::Continue(_) => {
                return Err(CompileError::Semantic("continue outside of loop".into()));
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
                        use_stmt.path.segments.last().cloned().unwrap_or_else(|| "module".to_string())
                    }
                };

                // Try to load the module and merge its definitions into global state
                match load_and_merge_module(use_stmt, None, &mut functions, &mut classes, &mut enums) {
                    Ok(value) => {
                        env.insert(binding_name.clone(), value);
                    }
                    Err(_e) => {
                        // Module loading failed - use empty dict as fallback
                        // This allows the program to continue, with errors appearing
                        // when the module members are accessed
                        env.insert(binding_name.clone(), Value::Dict(HashMap::new()));
                    }
                }
            }
            Node::ModDecl(_)
            | Node::CommonUseStmt(_)
            | Node::ExportUseStmt(_)
            | Node::AutoImportStmt(_)
            | Node::RequiresCapabilities(_)
            | Node::HandlePool(_)
            | Node::Bitfield(_)
            | Node::AopAdvice(_)
            | Node::DiBinding(_)
            | Node::ArchitectureRule(_)
            | Node::MockDecl(_) => {
                // Module system is handled by the module resolver
                // HandlePool is processed at compile time for allocation
                // Bitfield is processed at compile time for bit-level field access
                // AOP nodes are declarative configuration handled at compile time
                // These are no-ops in the interpreter
            }
        }
    }

    // Check if main is defined as a function and call it
    if let Some(main_func) = functions.get("main").cloned() {
        let result = exec_function(
            &main_func,
            &[],  // No arguments
            &env,
            &mut functions,
            &mut classes,
            &enums,
            &impl_methods,
            None,  // No self context
        )?;
        return result.as_int().map(|v| v as i32);
    }

    // Fall back to checking for `main = <value>` binding
    let main_val = env.get("main").cloned().unwrap_or(Value::Int(0)).as_int()? as i32;
    Ok(main_val)
}
