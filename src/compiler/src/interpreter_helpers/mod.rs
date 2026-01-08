//! Helper functions to reduce duplication across interpreter modules
//!
//! This module provides utility functions for:
//! - Method dispatch and method_missing hooks
//! - Range object creation
//! - Actor spawning
//! - Lambda and functional programming utilities
//! - Pattern matching and binding
//! - Collection operations (map, filter, reduce, etc.)

pub mod method_dispatch;
pub mod objects;
pub mod args;
pub mod collections;
pub mod patterns;
pub mod utilities;

// Re-export public API
pub(crate) use method_dispatch::{
    call_method_on_value,
    build_method_missing_args,
    find_and_exec_method,
    try_method_missing,
};

pub(crate) use objects::{
    create_range_object,
    spawn_actor_with_expr,
};

pub(crate) use args::{
    eval_arg,
    eval_arg_int,
    eval_arg_usize,
};

pub(crate) use collections::{
    eval_array_map,
    eval_array_filter,
    eval_array_reduce,
    eval_array_find,
    eval_array_any,
    eval_array_all,
    eval_dict_map_values,
    eval_dict_filter,
    iter_to_vec,
    eval_option_map,
    eval_option_and_then,
    eval_option_or_else,
    eval_option_filter,
    eval_result_map,
    eval_result_map_err,
    eval_result_and_then,
    eval_result_or_else,
    message_to_value,
};

pub(crate) use patterns::{
    bind_pattern,
    handle_functional_update,
    handle_method_call_with_self_update,
    bind_pattern_value,
};

pub(crate) use utilities::{
    normalize_index,
    slice_collection,
    control_to_value,
    comprehension_iterate,
    with_effect_context,
    spawn_future_with_callable,
    spawn_future_with_callable_and_env,
    spawn_future_with_expr,
};
