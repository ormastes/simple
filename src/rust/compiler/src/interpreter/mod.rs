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

use simple_parser::ast::{ClassDef, FunctionDef};

use crate::aop_config::AopConfig;
use crate::di::DiConfig;
pub use crate::effects::check_effect_violations;
use crate::error::CompileError;
pub use crate::value::BUILTIN_CHANNEL;
use crate::value::{Env, Value};

// Unit system support (SI prefixes, dimensional analysis, constraints)
pub(crate) use crate::interpreter_unit::*;

// State management (thread-local state, execution mode, signal handling)
#[path = "../interpreter_state.rs"]
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

// Core types and utilities
mod core_types;
pub(crate) use core_types::{
    get_identifier_name, get_pattern_name, is_immutable_by_pattern, Control, Enums, ExternFunctions, ImplMethods,
    Macros, Traits, TraitImpls, UnitFamilies, UnitFamilyInfo, Units,
};

// Async/await support
mod async_support;
pub(crate) use async_support::await_value;

// Error handling macros
#[macro_use]
mod error_macros;

// Coverage instrumentation helpers
mod coverage_helpers;
pub(crate) use coverage_helpers::{
    extract_node_location, record_node_coverage, record_decision_coverage_ffi, record_condition_coverage,
    decision_id_from_span, is_coverage_enabled,
};

// Node execution
mod node_exec;
pub(crate) use node_exec::exec_node;

// Block execution
mod block_exec;
pub(crate) use block_exec::{exec_block, exec_block_fn};

// Public API
mod public_api;
pub use public_api::{evaluate_module, evaluate_module_with_di, evaluate_module_with_di_and_aop};
pub(crate) use public_api::exec_method_function;

// Pattern matching functions for match expressions
#[path = "../interpreter_patterns.rs"]
mod interpreter_patterns;
pub(crate) use interpreter_patterns::{
    check_enum_exhaustiveness, collect_covered_variants, is_catch_all_pattern, pattern_matches,
};

// Control flow functions (if, while, loop, for, match)
#[path = "../interpreter_control.rs"]
mod interpreter_control;
use interpreter_control::{exec_context, exec_for, exec_if, exec_loop, exec_match, exec_match_expr, exec_while, exec_with};

mod expr;
pub(crate) use expr::evaluate_expr;

// Helper functions (method dispatch, array/dict ops, pattern binding, slicing)
#[path = "../interpreter_helpers/mod.rs"]
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
#[path = "../interpreter_call/mod.rs"]
mod interpreter_call;
pub(crate) use interpreter_call::IN_NEW_METHOD;
use interpreter_call::{
    bind_args, bind_args_with_injected, evaluate_call, exec_block_value, exec_function,
    exec_function_with_captured_env, exec_function_with_values, exec_lambda, instantiate_class, BDD_AFTER_EACH,
    BDD_BEFORE_EACH, BDD_CONTEXT_DEFS, BDD_COUNTS, BDD_INDENT, BDD_LAZY_VALUES, BDD_SHARED_EXAMPLES,
};

// Module caching and loading state
#[path = "../module_cache.rs"]
mod module_cache;
pub use module_cache::clear_module_cache;

// Module loading and resolution
#[path = "../interpreter_module/mod.rs"]
mod interpreter_module;
use interpreter_module::{
    evaluate_module_exports, get_import_alias, load_and_merge_module, merge_module_definitions, resolve_module_path,
};

// Type-related utilities
#[path = "../interpreter_types.rs"]
mod interpreter_types;
use interpreter_types::{get_type_name, register_trait_impl, TraitImplRegistry};

// Core module evaluation logic
#[path = "../interpreter_eval.rs"]
mod interpreter_eval;

#[path = "../interpreter_method/mod.rs"]
mod interpreter_method;
use interpreter_method::{evaluate_method_call, evaluate_method_call_with_self_update};
mod macros;
pub use macros::set_macro_trace;
pub(crate) use macros::{
    enter_block_scope, enter_class_scope, evaluate_macro_invocation, exit_block_scope, exit_class_scope,
    preprocess_macro_contract_at_definition, queue_tail_injection, take_macro_introduced_symbols,
};
// Native I/O helper utilities
#[path = "../interpreter_native_io.rs"]
mod interpreter_native_io;
#[path = "../native_io_helpers.rs"]
mod native_io_helpers;
// Re-export all native I/O functions
pub use interpreter_native_io::*;
#[path = "../interpreter_native_net.rs"]
mod interpreter_native_net;
// Re-export all native networking functions
pub use interpreter_native_net::*;
#[path = "../interpreter_context.rs"]
mod interpreter_context;
use interpreter_context::dispatch_context_method;
#[path = "../interpreter_extern/mod.rs"]
mod interpreter_extern;
pub(crate) use interpreter_extern::call_extern_function;
