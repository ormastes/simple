// Tree-walking interpreter for the Simple language.
//
// This module provides runtime interpretation of AST nodes, including:
// - Expression evaluation
// - Statement execution
// - Control flow handling
// - Built-in methods for arrays, dicts, strings, etc.
// - User-defined function and lambda execution
// - Actor/future/generator support

use std::collections::HashMap;

use simple_parser::ast::{AssignOp, Block, ClassDef, EnumDef, Expr, FunctionDef, Node, Type, UnitDef};
use tracing::instrument;

use crate::aop_config::AopConfig;
use crate::di::DiConfig;
pub use crate::effects::check_effect_violations;
use crate::error::CompileError;
pub use crate::value::BUILTIN_CHANNEL;
use crate::value::{Env, Value};

// Unit system support (SI prefixes, dimensional analysis, constraints)
pub(crate) use crate::interpreter_unit::*;

// State management (thread-local state, execution mode, signal handling)
#[path = "interpreter_state.rs"]
mod interpreter_state;
pub(crate) use interpreter_state::{
    clear_moved_vars, get_aop_config, get_di_config, mark_as_moved, set_aop_config, set_di_config, ExecutionMode,
};
pub use interpreter_state::{
    get_current_file, get_interpreter_args, init_signal_handlers, is_debug_mode, is_interrupted, reset_interrupt,
    set_current_file, set_debug_mode, set_interpreter_args,
};
pub(crate) use interpreter_state::{
    ACTOR_INBOX, ACTOR_OUTBOX, ACTOR_SPAWNER, AOP_CONFIG, BASE_UNIT_DIMENSIONS, COMPOUND_UNIT_DIMENSIONS, CONST_NAMES,
    CONTEXT_OBJECT, CONTEXT_VAR_NAME, CURRENT_FILE, DI_CONFIG, DI_SINGLETONS, EXECUTION_MODE, EXTERN_FUNCTIONS,
    GENERATOR_YIELDS, IMMUTABLE_VARS, INTERFACE_BINDINGS, INTERPRETER_ARGS, INTERRUPT_REQUESTED,
    MACRO_DEFINITION_ORDER, MODULE_GLOBALS, MOVED_VARS, SI_BASE_UNITS, UNIT_FAMILY_ARITHMETIC, UNIT_FAMILY_CONVERSIONS,
    UNIT_SUFFIX_TO_FAMILY, USER_MACROS,
};

/// Check if an expression is a simple identifier (for move tracking)
fn get_identifier_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Identifier(name) => Some(name.as_str()),
        _ => None,
    }
}

/// Extract the variable name from a pattern (for module-level global tracking)
fn get_pattern_name(pattern: &simple_parser::ast::Pattern) -> Option<String> {
    match pattern {
        simple_parser::ast::Pattern::Identifier(name) => Some(name.clone()),
        simple_parser::ast::Pattern::MutIdentifier(name) => Some(name.clone()),
        simple_parser::ast::Pattern::Typed { pattern, .. } => get_pattern_name(pattern),
        _ => None,
    }
}

/// Check if a variable name indicates immutability by naming pattern
/// Returns true if immutable (lowercase), false if mutable (ends with _)
pub(crate) fn is_immutable_by_pattern(name: &str) -> bool {
    if name.is_empty() {
        return true;
    }
    // Mutable if ends with underscore
    if name.ends_with('_') {
        return false;
    }
    // Otherwise immutable
    true
}

/// Stores enum definitions: name -> EnumDef
pub(crate) type Enums = HashMap<String, EnumDef>;

/// Stores impl block methods: type_name -> list of methods
pub(crate) type ImplMethods = HashMap<String, Vec<FunctionDef>>;

/// Stores extern function declarations: name -> definition
pub(crate) type ExternFunctions = HashMap<String, simple_parser::ast::ExternDef>;

/// Stores macro definitions: name -> definition
pub(crate) type Macros = HashMap<String, simple_parser::ast::MacroDef>;

/// Stores unit type definitions: suffix -> UnitDef
pub(crate) type Units = HashMap<String, UnitDef>;

/// Stores unit family definitions: family_name -> (base_type, variants with factors)
/// Used for to_X() conversion methods between related units
pub(crate) type UnitFamilies = HashMap<String, UnitFamilyInfo>;

/// Information about a unit family for conversion support
#[derive(Debug, Clone)]
#[allow(dead_code)] // Fields used when to_X() method dispatch is implemented
pub(crate) struct UnitFamilyInfo {
    /// Base type (e.g., f64)
    pub base_type: Type,
    /// Map of suffix -> conversion factor to base unit
    pub conversions: HashMap<String, f64>,
}

/// Stores trait definitions: trait_name -> TraitDef
pub(crate) type Traits = HashMap<String, simple_parser::ast::TraitDef>;

/// Stores trait implementations: (trait_name, type_name) -> list of methods
/// Used to track which types implement which traits
pub(crate) type TraitImpls = HashMap<(String, String), Vec<FunctionDef>>;

/// Control flow for statement execution.
pub(crate) enum Control {
    Next,
    Return(Value),
    #[allow(dead_code)]
    Break(Option<Value>),
    Continue,
}

/// Evaluate the module and return the `main` binding as an i32.
#[instrument(skip(items))]
pub fn evaluate_module(items: &[Node]) -> Result<i32, CompileError> {
    evaluate_module_with_di_and_aop(items, None, None)
}

pub fn evaluate_module_with_di(items: &[Node], di_config: Option<&DiConfig>) -> Result<i32, CompileError> {
    evaluate_module_with_di_and_aop(items, di_config, None)
}

pub fn evaluate_module_with_di_and_aop(
    items: &[Node],
    di_config: Option<&DiConfig>,
    aop_config: Option<&AopConfig>,
) -> Result<i32, CompileError> {
    set_di_config(di_config.cloned());
    set_aop_config(aop_config.cloned());
    let result = interpreter_eval::evaluate_module_impl(items);
    set_di_config(None);
    set_aop_config(None);
    result
}

pub(crate) fn exec_node(
    node: &Node,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    match node {
        Node::Let(let_stmt) => {
            if let Some(value_expr) = &let_stmt.value {
                // Handle method calls on objects - need to persist mutations to self
                let (value, update) =
                    handle_method_call_with_self_update(value_expr, env, functions, classes, enums, impl_methods)?;
                if let Some((obj_name, new_self)) = update {
                    env.insert(obj_name, new_self);
                }

                // Move semantics for unique pointers:
                // If binding a unique pointer from a simple identifier, mark source as moved
                if matches!(value, Value::Unique(_)) {
                    if let Some(source_name) = get_identifier_name(value_expr) {
                        mark_as_moved(source_name);
                    }
                }

                // Validate unit type annotation if present
                // Type can come from either let_stmt.ty OR from a typed pattern (x: Type)
                let type_annotation = if let_stmt.ty.is_some() {
                    let_stmt.ty.clone()
                } else if let simple_parser::ast::Pattern::Typed { ty, .. } = &let_stmt.pattern {
                    Some(ty.clone())
                } else {
                    None
                };

                // Helper to extract variable name for error messages
                let get_var_name = |pattern: &simple_parser::ast::Pattern| -> String {
                    match pattern {
                        simple_parser::ast::Pattern::Identifier(name) => name.clone(),
                        simple_parser::ast::Pattern::MutIdentifier(name) => name.clone(),
                        simple_parser::ast::Pattern::Typed { pattern, .. } => match pattern.as_ref() {
                            simple_parser::ast::Pattern::Identifier(name) => name.clone(),
                            simple_parser::ast::Pattern::MutIdentifier(name) => name.clone(),
                            _ => "<pattern>".to_string(),
                        },
                        _ => "<pattern>".to_string(),
                    }
                };

                // Validate and constrain value based on type annotation
                let value = match &type_annotation {
                    Some(Type::Simple(type_name)) if is_unit_type(type_name) => {
                        if let Err(e) = validate_unit_type(&value, type_name) {
                            let var_name = get_var_name(&let_stmt.pattern);
                            return Err(CompileError::Semantic(format!("let binding '{}': {}", var_name, e)));
                        }
                        value
                    }
                    Some(Type::UnitWithRepr { name, constraints, .. }) => {
                        // Validate and apply unit type constraints (range, overflow behavior)
                        match validate_unit_constraints(value, name, constraints) {
                            Ok(constrained_value) => constrained_value,
                            Err(e) => {
                                let var_name = get_var_name(&let_stmt.pattern);
                                return Err(CompileError::Semantic(format!("let binding '{}': {}", var_name, e)));
                            }
                        }
                    }
                    _ => value,
                };

                // Coerce to TraitObject if type annotation is `dyn Trait`
                let value = if let Some(Type::DynTrait(trait_name)) = &let_stmt.ty {
                    Value::TraitObject {
                        trait_name: trait_name.clone(),
                        inner: Box::new(value),
                    }
                } else {
                    value
                };
                let is_mutable = let_stmt.mutability.is_mutable();
                bind_pattern_value(&let_stmt.pattern, value, is_mutable, env);
            }
            Ok(Control::Next)
        }
        Node::Const(const_stmt) => {
            let value = evaluate_expr(&const_stmt.value, env, functions, classes, enums, impl_methods)?;
            env.insert(const_stmt.name.clone(), value);
            CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
            Ok(Control::Next)
        }
        Node::Static(static_stmt) => {
            let value = evaluate_expr(&static_stmt.value, env, functions, classes, enums, impl_methods)?;
            env.insert(static_stmt.name.clone(), value);
            if !static_stmt.mutability.is_mutable() {
                CONST_NAMES.with(|cell| cell.borrow_mut().insert(static_stmt.name.clone()));
            }
            Ok(Control::Next)
        }
        Node::Assignment(assign) if assign.op == AssignOp::Assign => {
            if let Expr::Identifier(name) = &assign.target {
                // Check if this is a first-time assignment (implicit declaration)
                let is_first_assignment = !env.contains_key(name);

                let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                if is_const {
                    return Err(CompileError::Semantic(format!("cannot assign to const '{name}'")));
                }

                // Check immutability for reassignments (not first assignment)
                if !is_first_assignment {
                    let is_immutable = IMMUTABLE_VARS.with(|cell| cell.borrow().contains(name));
                    if is_immutable && !name.ends_with('_') {
                        return Err(CompileError::Semantic(format!(
                            "cannot reassign to immutable variable '{name}'\n\
                             help: consider using '{name}_' for a mutable variable, \
                             or use '{name}->method()' for functional updates"
                        )));
                    }
                }

                // Handle method calls on objects - need to persist mutations to self
                let (value, update) =
                    handle_method_call_with_self_update(&assign.value, env, functions, classes, enums, impl_methods)?;
                // If the mutating method returned an updated object with the same name as target,
                // the update already set the variable, so skip the normal assignment
                let skip_assignment = if let Some((ref obj_name, ref new_self)) = update {
                    env.insert(obj_name.clone(), new_self.clone());
                    obj_name == name
                } else {
                    false
                };
                if !skip_assignment {
                    // Check if this is a module-level global variable (for function access)
                    let is_global = MODULE_GLOBALS.with(|cell| cell.borrow().contains_key(name));
                    if is_global && !env.contains_key(name) {
                        // Update module-level global
                        MODULE_GLOBALS.with(|cell| {
                            cell.borrow_mut().insert(name.clone(), value);
                        });
                    } else {
                        env.insert(name.clone(), value);

                        // If this is a first-time assignment (implicit declaration),
                        // track its mutability based on naming pattern
                        if is_first_assignment {
                            let immutable_by_pattern = is_immutable_by_pattern(name);
                            let is_all_caps = name.chars().all(|c| c.is_uppercase() || c.is_numeric() || c == '_')
                                && name.chars().any(|c| c.is_alphabetic());

                            if immutable_by_pattern {
                                if is_all_caps {
                                    // ALL_CAPS = constant
                                    CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                                } else {
                                    // Lowercase = immutable (supports functional updates)
                                    IMMUTABLE_VARS.with(|cell| cell.borrow_mut().insert(name.clone()));
                                }
                            }
                            // else: ends with _ = mutable, no tracking needed
                        }

                        // Also sync to MODULE_GLOBALS if it exists there (for module-level assignments)
                        MODULE_GLOBALS.with(|cell| {
                            let mut globals = cell.borrow_mut();
                            if globals.contains_key(name) {
                                globals.insert(name.clone(), env.get(name).unwrap().clone());
                            }
                        });
                    }
                }
                Ok(Control::Next)
            } else if let Expr::FieldAccess { receiver, field } = &assign.target {
                // Handle field assignment: obj.field = value
                let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                // Get the object name (must be an identifier for now)
                if let Expr::Identifier(obj_name) = receiver.as_ref() {
                    if let Some(obj_val) = env.get(obj_name).cloned() {
                        match obj_val {
                            Value::Object { class, mut fields } => {
                                fields.insert(field.clone(), value);
                                env.insert(obj_name.clone(), Value::Object { class, fields });
                            }
                            _ => {
                                return Err(CompileError::Semantic(format!(
                                    "cannot assign field on non-object value"
                                )))
                            }
                        }
                        Ok(Control::Next)
                    } else {
                        // Collect all known names for typo suggestion
                        let known_names: Vec<&str> = env
                            .keys()
                            .map(|s| s.as_str())
                            .chain(functions.keys().map(|s| s.as_str()))
                            .chain(classes.keys().map(|s| s.as_str()))
                            .collect();
                        let mut msg = format!("undefined variable '{obj_name}'");
                        if let Some(suggestion) = crate::error::typo::format_suggestion(obj_name, known_names) {
                            msg.push_str(&format!("; {}", suggestion));
                        }
                        Err(CompileError::Semantic(msg))
                    }
                } else {
                    Err(CompileError::Semantic(
                        "field assignment requires identifier as object".into(),
                    ))
                }
            } else if let Expr::Tuple(targets) = &assign.target {
                // Handle tuple unpacking: (a, b) = (x, y)
                let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                let values: Vec<Value> = match value {
                    Value::Tuple(v) => v,
                    Value::Array(v) => v,
                    _ => {
                        return Err(CompileError::Semantic(
                            "tuple unpacking requires tuple or array on right side".into(),
                        ))
                    }
                };
                if targets.len() != values.len() {
                    return Err(CompileError::Semantic(format!(
                        "tuple unpacking length mismatch: expected {}, got {}",
                        targets.len(),
                        values.len()
                    )));
                }
                for (target_expr, val) in targets.iter().zip(values.into_iter()) {
                    if let Expr::Identifier(name) = target_expr {
                        env.insert(name.clone(), val);
                    } else {
                        return Err(CompileError::Semantic(
                            "tuple unpacking target must be identifier".into(),
                        ));
                    }
                }
                Ok(Control::Next)
            } else {
                Err(CompileError::Semantic("unsupported assignment target".into()))
            }
        }
        Node::If(if_stmt) => exec_if(if_stmt, env, functions, classes, enums, impl_methods),
        Node::While(while_stmt) => exec_while(while_stmt, env, functions, classes, enums, impl_methods),
        Node::Loop(loop_stmt) => exec_loop(loop_stmt, env, functions, classes, enums, impl_methods),
        Node::For(for_stmt) => exec_for(for_stmt, env, functions, classes, enums, impl_methods),
        Node::Return(ret) => {
            let value = if let Some(expr) = &ret.value {
                // Handle method calls on objects - need to persist mutations to self
                let (val, update) =
                    handle_method_call_with_self_update(expr, env, functions, classes, enums, impl_methods)?;
                if let Some((name, new_self)) = update {
                    env.insert(name, new_self);
                }
                val
            } else {
                Value::Nil
            };
            Ok(Control::Return(value))
        }
        Node::Break(b) => {
            let value = if let Some(expr) = &b.value {
                Some(evaluate_expr(expr, env, functions, classes, enums, impl_methods)?)
            } else {
                None
            };
            Ok(Control::Break(value))
        }
        Node::Continue(_) => Ok(Control::Continue),
        Node::Match(match_stmt) => exec_match(match_stmt, env, functions, classes, enums, impl_methods),
        Node::Context(ctx_stmt) => exec_context(ctx_stmt, env, functions, classes, enums, impl_methods),
        Node::With(with_stmt) => exec_with(with_stmt, env, functions, classes, enums, impl_methods),
        Node::Expression(expr) => {
            if let Expr::FunctionalUpdate { target, method, args } = expr {
                if let Some((name, new_value)) =
                    handle_functional_update(target, method, args, env, functions, classes, enums, impl_methods)?
                {
                    env.insert(name, new_value);
                    return Ok(Control::Next);
                }
            }
            // Handle method calls on objects - need to persist mutations to self
            let (_, update) = handle_method_call_with_self_update(expr, env, functions, classes, enums, impl_methods)?;
            if let Some((name, new_self)) = update {
                env.insert(name, new_self);
            }
            Ok(Control::Next)
        }
        Node::Function(f) => {
            // Nested function definition - treat as a closure that captures the current scope
            // Store as a Function with the captured env embedded for closure semantics
            env.insert(
                f.name.clone(),
                Value::Function {
                    name: f.name.clone(),
                    def: Box::new(f.clone()),
                    captured_env: env.clone(), // Capture current scope
                },
            );
            Ok(Control::Next)
        }
        _ => Ok(Control::Next),
    }
}

pub(crate) fn exec_block(
    block: &Block,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Enter block scope for tail injection tracking
    let _scope_depth = enter_block_scope();

    for stmt in &block.statements {
        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(_) | Control::Continue) => {
                // Execute pending tail injections before exiting the block
                let tail_blocks = exit_block_scope();
                for tail_block in tail_blocks {
                    exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                }
                return Ok(flow);
            }
        }
    }

    // Execute pending tail injections at normal block exit
    let tail_blocks = exit_block_scope();
    for tail_block in tail_blocks {
        exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
    }

    Ok(Control::Next)
}

/// Execute a block in a function context, supporting implicit return.
/// If the last statement is an expression, its value is captured and returned.
pub(crate) fn exec_block_fn(
    block: &Block,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<(Control, Option<Value>), CompileError> {
    // Enter block scope for tail injection tracking
    let _scope_depth = enter_block_scope();

    let len = block.statements.len();
    let mut last_expr_value: Option<Value> = None;

    for (i, stmt) in block.statements.iter().enumerate() {
        // For the last statement, if it's an expression, capture its value
        let is_last = i == len - 1;
        if is_last {
            if let Node::Expression(expr) = stmt {
                // Evaluate and capture the value for implicit return
                let val = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
                last_expr_value = Some(val);
                continue;
            }
        }

        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(_) | Control::Continue) => {
                // Execute pending tail injections before exiting the block
                let tail_blocks = exit_block_scope();
                for tail_block in tail_blocks {
                    exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
                }
                return Ok((flow, None));
            }
        }
    }

    // Execute pending tail injections at normal block exit
    let tail_blocks = exit_block_scope();
    for tail_block in tail_blocks {
        exec_block(&tail_block, env, functions, classes, enums, impl_methods)?;
    }

    Ok((Control::Next, last_expr_value))
}

//==============================================================================
// Error handling macros to reduce boilerplate
//==============================================================================

// These macros are defined for potential future use
#[allow(unused_macros)]
/// Create a runtime error with message
macro_rules! runtime_err {
    ($msg:expr) => {
        crate::error::CompileError::Runtime($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Runtime(format!($fmt, $($arg)*))
    };
}

/// Create a semantic error with message
macro_rules! semantic_err {
    ($msg:expr) => {
        crate::error::CompileError::Semantic($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Semantic(format!($fmt, $($arg)*))
    };
}

#[allow(unused_macros)]
/// Create a codegen error with message
macro_rules! codegen_err {
    ($msg:expr) => {
        crate::error::CompileError::Codegen($msg.to_string())
    };
    ($fmt:expr, $($arg:tt)*) => {
        crate::error::CompileError::Codegen(format!($fmt, $($arg)*))
    };
}

#[allow(unused_macros)]
/// Return early with a runtime error
macro_rules! bail_runtime {
    ($msg:expr) => {
        return Err(runtime_err!($msg))
    };
    ($fmt:expr, $($arg:tt)*) => {
        return Err(runtime_err!($fmt, $($arg)*))
    };
}

/// Return early with a semantic error
macro_rules! bail_semantic {
    ($msg:expr) => {
        return Err(semantic_err!($msg))
    };
    ($fmt:expr, $($arg:tt)*) => {
        return Err(semantic_err!($fmt, $($arg)*))
    };
}

/// Return early with unknown method error (with typo suggestions)
macro_rules! bail_unknown_method {
    ($method:expr, $type_name:expr, $available:expr) => {{
        let mut msg = format!("unknown method {} on {}", $method, $type_name);
        if let Some(suggestion) = crate::error::typo::format_suggestion($method, $available.iter().copied()) {
            msg.push_str(&format!("; {}", suggestion));
        }
        return Err(semantic_err!("{}", msg));
    }};
}

// Pattern matching functions for match expressions
#[path = "interpreter_patterns.rs"]
mod interpreter_patterns;
pub(crate) use interpreter_patterns::{
    check_enum_exhaustiveness, collect_covered_variants, is_catch_all_pattern, pattern_matches,
};

// Control flow functions (if, while, loop, for, match)
#[path = "interpreter_control.rs"]
mod interpreter_control;
use interpreter_control::{exec_context, exec_for, exec_if, exec_loop, exec_match, exec_while, exec_with};

/// Helper to execute a method function with self context (for auto-forwarding properties)
fn exec_method_function(
    method: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    self_val: &Value,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Value::Object { class, fields } = self_val {
        exec_function(
            method,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
            Some((class.as_str(), fields)),
        )
    } else {
        Err(CompileError::Semantic(
            "exec_method_function called with non-object self".into(),
        ))
    }
}

mod expr;
pub(crate) use expr::evaluate_expr;

// Helper functions (method dispatch, array/dict ops, pattern binding, slicing)
#[path = "interpreter_helpers/mod.rs"]
mod interpreter_helpers;
pub(crate) use interpreter_helpers::{
    bind_pattern, bind_pattern_value, comprehension_iterate, control_to_value, create_range_object, eval_arg,
    eval_arg_int, eval_arg_usize, eval_array_all, eval_array_any, eval_array_filter, eval_array_find, eval_array_map,
    eval_array_reduce, eval_dict_filter, eval_dict_map_values, eval_option_and_then, eval_option_filter,
    eval_option_map, eval_option_or_else, eval_result_and_then, eval_result_map, eval_result_map_err,
    eval_result_or_else, find_and_exec_method, handle_functional_update, handle_method_call_with_self_update,
    iter_to_vec, message_to_value, normalize_index, slice_collection, spawn_actor_with_expr,
    spawn_future_with_callable, spawn_future_with_callable_and_env, spawn_future_with_expr, try_method_missing,
    with_effect_context,
};

// Include the rest of the interpreter functions
#[path = "interpreter_call/mod.rs"]
mod interpreter_call;
pub(crate) use interpreter_call::IN_NEW_METHOD;
use interpreter_call::{
    bind_args, bind_args_with_injected, evaluate_call, exec_block_value, exec_function,
    exec_function_with_captured_env, exec_function_with_values, exec_lambda, instantiate_class, BDD_AFTER_EACH,
    BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_COUNTS, BDD_INDENT, BDD_LAZY_VALUES, BDD_SHARED_EXAMPLES,
};

// Module caching and loading state
#[path = "module_cache.rs"]
mod module_cache;
pub use module_cache::clear_module_cache;

// Module loading and resolution
#[path = "interpreter_module.rs"]
mod interpreter_module;
use interpreter_module::{
    evaluate_module_exports, get_import_alias, load_and_merge_module, merge_module_definitions, resolve_module_path,
};

// Type-related utilities
#[path = "interpreter_types.rs"]
mod interpreter_types;
use interpreter_types::{get_type_name, register_trait_impl, TraitImplRegistry};

// Core module evaluation logic
#[path = "interpreter_eval.rs"]
mod interpreter_eval;

#[path = "interpreter_method/mod.rs"]
mod interpreter_method;
use interpreter_method::{evaluate_method_call, evaluate_method_call_with_self_update};
mod macros;
pub use macros::set_macro_trace;
pub(crate) use macros::{
    enter_block_scope, evaluate_macro_invocation, exit_block_scope, queue_tail_injection, take_macro_introduced_symbols,
};
// Native I/O helper utilities
#[path = "interpreter_native_io.rs"]
mod interpreter_native_io;
#[path = "native_io_helpers.rs"]
mod native_io_helpers;
// Re-export all native I/O functions
pub use interpreter_native_io::*;
#[path = "interpreter_native_net.rs"]
mod interpreter_native_net;
// Re-export all native networking functions
pub use interpreter_native_net::*;
#[path = "interpreter_context.rs"]
mod interpreter_context;
use interpreter_context::dispatch_context_method;
#[path = "interpreter_extern.rs"]
mod interpreter_extern;
pub(crate) use interpreter_extern::call_extern_function;
