//! Extern function dispatcher for the Simple language interpreter
//!
//! This module provides the central dispatch mechanism for all extern functions
//! callable from Simple code. Functions are organized into focused modules by category.
//!
//! ## Module Organization
//!
//! ### Common Utilities
//! - `common`: Shared utilities (effect checking, argument extraction, error handling)
//!
//! ### Simple Operations
//! - `conversion`: Type conversions (to_string, to_int)
//! - `process`: Process control (exit)
//! - `time`: Time operations (rt_time_now_seconds)
//! - `math`: Math operations (abs, min, max, sqrt, pow, etc.)
//! - `layout`: Layout profiling (simple_layout_mark)
//! - `system`: System operations (sys_get_args, sys_exit)
//!
//! ### I/O Operations
//! - `io`: Input/output (print, eprint, input, stdin/stdout/stderr operations)
//!
//! ### Network Operations
//! - `network`: TCP, UDP, HTTP operations
//!
//! ### Filesystem Operations
//! - `filesystem`: File and directory operations
//! - `terminal`: Terminal I/O operations
//!
//! ### FFI Operations
//! - `atomic`: Atomic operations (AtomicBool, AtomicInt, AtomicFlag)
//! - `tui`: Ratatui TUI bindings
//! - `repl`: REPL runner integration
//! - `gpu`: Vulkan GPU compute operations (feature-gated)

use crate::error::CompileError;
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef};
use std::collections::HashMap;

// Module declarations
pub mod common;
pub mod conversion;
pub mod process;
pub mod time;
pub mod math;
pub mod random;
pub mod layout;
pub mod system;
pub mod io;
pub mod network;
pub mod filesystem;
pub mod file_io;
pub mod terminal;
pub mod atomic;
pub mod concurrency;
#[cfg(feature = "tui")]
pub mod tui;
pub mod repl;
pub mod gpu;
pub mod diagram;
pub mod memory;
pub mod cli;
pub mod cargo;
pub mod sdn;
pub mod coverage;
pub mod cranelift;
pub mod sandbox;
pub mod mock_policy;
pub mod ffi_value;
pub mod ffi_array;
pub mod ffi_dict;
pub mod ffi_string;
pub mod collections;
pub mod lexer_ffi;
pub mod i18n;
pub mod native_ffi;
pub mod package;
pub mod regex;
pub mod ast_ffi;
pub mod env_ffi;
pub mod error_ffi;
pub mod span_ffi;
pub mod rc;
pub mod json;

// Import parent interpreter types
type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

// Import shared functions from parent module
use super::{evaluate_expr, is_debug_mode};

// Import diagram tracing
use simple_runtime::value::diagram_ffi;

/// Resolve fmt() methods on Object values for print functions.
/// Converts Objects with fmt() methods to their string representation.
fn resolve_fmt_for_print(
    values: &[Value],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Vec<Value> {
    use super::interpreter_control::call_method_if_exists;
    values
        .iter()
        .map(|v| {
            if let Value::Object { .. } = v {
                if let Ok(Some(result)) =
                    call_method_if_exists(v, "fmt", &[], env, functions, classes, enums, impl_methods)
                {
                    return result;
                }
            }
            v.clone()
        })
        .collect()
}

/// Central extern function dispatcher
///
/// Routes extern function calls to the appropriate module based on function name.
/// All 134 extern functions are dispatched from this central location.
///
/// # Arguments
/// * `name` - The extern function name
/// * `args` - Unevaluated argument expressions
/// * `env` - Current environment
/// * `functions` - Function definitions
/// * `classes` - Class definitions
/// * `enums` - Enum definitions
/// * `impl_methods` - Implementation methods
///
/// # Returns
/// * `Ok(Value)` - Function result
/// * `Err(CompileError)` - Error during execution
pub(crate) fn call_extern_function(
    name: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Diagram tracing for extern function calls
    if diagram_ffi::is_diagram_enabled() {
        diagram_ffi::trace_call(name);
    }

    // Evaluate all arguments upfront
    let evaluated: Vec<Value> = args
        .iter()
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .collect::<Result<Vec<_>, _>>()?;

    // Dispatch to appropriate module
    match name {
        // ====================================================================
        // I/O Operations (7 print + 2 input + 4 MCP stdio = 13 functions)
        // ====================================================================
        "print" => {
            let resolved = resolve_fmt_for_print(&evaluated, env, functions, classes, enums, impl_methods);
            io::print::print(&resolved)
        }
        "print_raw" => {
            let resolved = resolve_fmt_for_print(&evaluated, env, functions, classes, enums, impl_methods);
            io::print::print_raw(&resolved)
        }
        "println" => io::print::println(&evaluated),
        "eprint" => {
            let resolved = resolve_fmt_for_print(&evaluated, env, functions, classes, enums, impl_methods);
            io::print::eprint(&resolved)
        }
        "eprint_raw" => {
            let resolved = resolve_fmt_for_print(&evaluated, env, functions, classes, enums, impl_methods);
            io::print::eprint_raw(&resolved)
        }
        "eprintln" => io::print::eprintln(&evaluated),
        "dprint" => io::print::dprint(&evaluated),
        "dbg" => {
            // Try debug_fmt() on Objects before falling back to to_debug_string()
            use super::interpreter_control::call_method_if_exists;
            let resolved: Vec<Value> = evaluated
                .iter()
                .map(|v| {
                    if let Value::Object { .. } = v {
                        if let Ok(Some(result)) =
                            call_method_if_exists(v, "debug_fmt", &[], env, functions, classes, enums, impl_methods)
                        {
                            return result;
                        }
                    }
                    v.clone()
                })
                .collect();
            io::print::dbg(&resolved)
        }
        "input" => io::input::input(&evaluated),
        "stdin_read_char" => io::input::stdin_read_char(&evaluated),
        "stdout_write" => io::stdout_write(&evaluated),
        "stdout_flush" => io::stdout_flush(&evaluated),
        "stderr_write" => io::stderr_write(&evaluated),
        "stderr_flush" => io::stderr_flush(&evaluated),

        // ====================================================================
        // Math Operations (7 integer + 18 float FFI + 5 special = 30 functions)
        // ====================================================================
        // Integer math operations
        "abs" => math::abs(&evaluated),
        "min" => math::min(&evaluated),
        "max" => math::max(&evaluated),
        "sqrt" => math::sqrt(&evaluated),
        "floor" => math::floor(&evaluated),
        "ceil" => math::ceil(&evaluated),
        "pow" => math::pow(&evaluated),

        // Float math FFI operations
        "rt_math_pow" => math::rt_math_pow_fn(&evaluated),
        "rt_math_log" => math::rt_math_log_fn(&evaluated),
        "rt_math_log10" => math::rt_math_log10_fn(&evaluated),
        "rt_math_log2" => math::rt_math_log2_fn(&evaluated),
        "rt_math_exp" => math::rt_math_exp_fn(&evaluated),
        "rt_math_sqrt" => math::rt_math_sqrt_fn(&evaluated),
        "rt_math_cbrt" => math::rt_math_cbrt_fn(&evaluated),
        "rt_math_sin" => math::rt_math_sin_fn(&evaluated),
        "rt_math_cos" => math::rt_math_cos_fn(&evaluated),
        "rt_math_tan" => math::rt_math_tan_fn(&evaluated),
        "rt_math_asin" => math::rt_math_asin_fn(&evaluated),
        "rt_math_acos" => math::rt_math_acos_fn(&evaluated),
        "rt_math_atan" => math::rt_math_atan_fn(&evaluated),
        "rt_math_atan2" => math::rt_math_atan2_fn(&evaluated),
        "rt_math_sinh" => math::rt_math_sinh_fn(&evaluated),
        "rt_math_cosh" => math::rt_math_cosh_fn(&evaluated),
        "rt_math_tanh" => math::rt_math_tanh_fn(&evaluated),
        "rt_math_floor" => math::rt_math_floor_fn(&evaluated),
        "rt_math_ceil" => math::rt_math_ceil_fn(&evaluated),

        // Special value operations
        "rt_math_nan" => math::rt_math_nan_fn(&evaluated),
        "rt_math_inf" => math::rt_math_inf_fn(&evaluated),
        "rt_math_is_nan" => math::rt_math_is_nan_fn(&evaluated),
        "rt_math_is_inf" => math::rt_math_is_inf_fn(&evaluated),
        "rt_math_is_finite" => math::rt_math_is_finite_fn(&evaluated),

        // ====================================================================
        // Time Operations (3 functions)
        // ====================================================================
        "rt_time_now_seconds" => time::rt_time_now_seconds(&evaluated),
        "_current_time_unix" => time::_current_time_unix(&evaluated),
        "rt_current_time_ms" => time::rt_current_time_ms(&evaluated),

        // ====================================================================
        // DateTime Operations (11 functions)
        // ====================================================================
        "rt_time_now_unix_micros" => time::rt_time_now_unix_micros(&evaluated),
        "rt_timestamp_get_year" => time::rt_timestamp_get_year(&evaluated),
        "rt_timestamp_get_month" => time::rt_timestamp_get_month(&evaluated),
        "rt_timestamp_get_day" => time::rt_timestamp_get_day(&evaluated),
        "rt_timestamp_get_hour" => time::rt_timestamp_get_hour(&evaluated),
        "rt_timestamp_get_minute" => time::rt_timestamp_get_minute(&evaluated),
        "rt_timestamp_get_second" => time::rt_timestamp_get_second(&evaluated),
        "rt_timestamp_get_microsecond" => time::rt_timestamp_get_microsecond(&evaluated),
        "rt_timestamp_from_components" => time::rt_timestamp_from_components(&evaluated),
        "rt_timestamp_add_days" => time::rt_timestamp_add_days(&evaluated),
        "rt_timestamp_diff_days" => time::rt_timestamp_diff_days(&evaluated),

        // ====================================================================
        // Progress Timing (3 functions)
        // ====================================================================
        "rt_progress_init" => time::rt_progress_init(&evaluated),
        "rt_progress_reset" => time::rt_progress_reset(&evaluated),
        "rt_progress_get_elapsed_seconds" => time::rt_progress_get_elapsed_seconds(&evaluated),

        // ====================================================================
        // Random Number Generation (7 functions)
        // ====================================================================
        "rt_random_seed" => random::rt_random_seed_fn(&evaluated),
        "rt_random_getstate" => random::rt_random_getstate_fn(&evaluated),
        "rt_random_setstate" => random::rt_random_setstate_fn(&evaluated),
        "rt_random_next" => random::rt_random_next_fn(&evaluated),
        "rt_random_randint" => random::rt_random_randint_fn(&evaluated),
        "rt_random_random" => random::rt_random_random_fn(&evaluated),
        "rt_random_uniform" => random::rt_random_uniform_fn(&evaluated),

        // ====================================================================
        // Atomic Operations (15 functions)
        // ====================================================================
        // Atomic Bool (5 functions)
        "rt_atomic_bool_new" => atomic::rt_atomic_bool_new(&evaluated),
        "rt_atomic_bool_load" => atomic::rt_atomic_bool_load(&evaluated),
        "rt_atomic_bool_store" => atomic::rt_atomic_bool_store(&evaluated),
        "rt_atomic_bool_swap" => atomic::rt_atomic_bool_swap(&evaluated),
        "rt_atomic_bool_free" => atomic::rt_atomic_bool_free(&evaluated),

        // Atomic Int (11 functions)
        "rt_atomic_int_new" => atomic::rt_atomic_int_new(&evaluated),
        "rt_atomic_int_load" => atomic::rt_atomic_int_load(&evaluated),
        "rt_atomic_int_store" => atomic::rt_atomic_int_store(&evaluated),
        "rt_atomic_int_swap" => atomic::rt_atomic_int_swap(&evaluated),
        "rt_atomic_int_compare_exchange" => atomic::rt_atomic_int_compare_exchange(&evaluated),
        "rt_atomic_int_fetch_add" => atomic::rt_atomic_int_fetch_add(&evaluated),
        "rt_atomic_int_fetch_sub" => atomic::rt_atomic_int_fetch_sub(&evaluated),
        "rt_atomic_int_fetch_and" => atomic::rt_atomic_int_fetch_and(&evaluated),
        "rt_atomic_int_fetch_or" => atomic::rt_atomic_int_fetch_or(&evaluated),
        "rt_atomic_int_fetch_xor" => atomic::rt_atomic_int_fetch_xor(&evaluated),
        "rt_atomic_int_free" => atomic::rt_atomic_int_free(&evaluated),

        // Atomic Flag (4 functions)
        "rt_atomic_flag_new" => atomic::rt_atomic_flag_new(&evaluated),
        "rt_atomic_flag_test_and_set" => atomic::rt_atomic_flag_test_and_set(&evaluated),
        "rt_atomic_flag_clear" => atomic::rt_atomic_flag_clear(&evaluated),
        "rt_atomic_flag_free" => atomic::rt_atomic_flag_free(&evaluated),

        // ====================================================================
        // Synchronization Primitives (28 functions)
        // ====================================================================
        // Atomic (10 functions)
        "rt_atomic_new" => atomic::rt_atomic_new_fn(&evaluated),
        "rt_atomic_load" => atomic::rt_atomic_load_fn(&evaluated),
        "rt_atomic_store" => atomic::rt_atomic_store_fn(&evaluated),
        "rt_atomic_swap" => atomic::rt_atomic_swap_fn(&evaluated),
        "rt_atomic_compare_exchange" => atomic::rt_atomic_compare_exchange_fn(&evaluated),
        "rt_atomic_fetch_add" => atomic::rt_atomic_fetch_add_fn(&evaluated),
        "rt_atomic_fetch_sub" => atomic::rt_atomic_fetch_sub_fn(&evaluated),
        "rt_atomic_fetch_and" => atomic::rt_atomic_fetch_and_fn(&evaluated),
        "rt_atomic_fetch_or" => atomic::rt_atomic_fetch_or_fn(&evaluated),

        // Mutex (4 functions)
        "rt_mutex_new" => atomic::rt_mutex_new_fn(&evaluated),
        "rt_mutex_lock" => atomic::rt_mutex_lock_fn(&evaluated),
        "rt_mutex_try_lock" => atomic::rt_mutex_try_lock_fn(&evaluated),
        "rt_mutex_unlock" => atomic::rt_mutex_unlock_fn(&evaluated),

        // RwLock (6 functions)
        "rt_rwlock_new" => atomic::rt_rwlock_new_fn(&evaluated),
        "rt_rwlock_read" => atomic::rt_rwlock_read_fn(&evaluated),
        "rt_rwlock_write" => atomic::rt_rwlock_write_fn(&evaluated),
        "rt_rwlock_try_read" => atomic::rt_rwlock_try_read_fn(&evaluated),
        "rt_rwlock_try_write" => atomic::rt_rwlock_try_write_fn(&evaluated),
        "rt_rwlock_set" => atomic::rt_rwlock_set_fn(&evaluated),

        // ====================================================================
        // Conversion Functions (2 functions)
        // ====================================================================
        "to_string" => conversion::to_string(&evaluated),
        "to_int" => conversion::to_int(&evaluated),

        // ====================================================================
        // Process Control (3 functions)
        // ====================================================================
        "exit" => process::exit(&evaluated),
        "panic" => process::panic(&evaluated),
        "rt_process_run" => system::rt_process_run(&evaluated),
        "rt_process_run_timeout" => system::rt_process_run_timeout(&evaluated),

        // ====================================================================
        // Filesystem Operations (18 fs_* + 6 file_* = 24 functions)
        // ====================================================================
        "native_fs_exists" => filesystem::native_fs_exists(&evaluated),
        "native_fs_read" => filesystem::native_fs_read(&evaluated),
        "native_fs_read_string" => filesystem::native_fs_read_string(&evaluated),
        "native_fs_write" => filesystem::native_fs_write(&evaluated),
        "native_fs_write_string" => filesystem::native_fs_write_string(&evaluated),
        "native_fs_append" => filesystem::native_fs_append(&evaluated),
        "native_fs_create_dir" => filesystem::native_fs_create_dir(&evaluated),
        "native_fs_remove_file" => filesystem::native_fs_remove_file(&evaluated),
        "native_fs_remove_dir" => filesystem::native_fs_remove_dir(&evaluated),
        "native_fs_rename" => filesystem::native_fs_rename(&evaluated),
        "native_fs_copy" => filesystem::native_fs_copy(&evaluated),
        "native_fs_metadata" => filesystem::native_fs_metadata(&evaluated),
        "native_fs_read_dir" => filesystem::native_fs_read_dir(&evaluated),
        "native_fs_open" => filesystem::native_fs_open(&evaluated),
        "native_file_read" => filesystem::native_file_read(&evaluated),
        "native_file_write" => filesystem::native_file_write(&evaluated),
        "native_file_flush" => filesystem::native_file_flush(&evaluated),
        "native_file_seek" => filesystem::native_file_seek(&evaluated),
        "native_file_sync" => filesystem::native_file_sync(&evaluated),
        "native_file_close" => filesystem::native_file_close(&evaluated),

        // ====================================================================
        // Terminal Operations (12 functions)
        // ====================================================================
        "native_stdin" => terminal::native_stdin(&evaluated),
        "native_stdout" => terminal::native_stdout(&evaluated),
        "native_stderr" => terminal::native_stderr(&evaluated),
        "native_is_tty" => terminal::native_is_tty(&evaluated),
        "native_enable_raw_mode" => terminal::native_enable_raw_mode(&evaluated),
        "native_disable_raw_mode" => terminal::native_disable_raw_mode(&evaluated),
        "native_get_term_size" => terminal::native_get_term_size(&evaluated),
        "native_term_write" => terminal::native_term_write(&evaluated),
        "native_term_read" => terminal::native_term_read(&evaluated),
        "native_term_read_timeout" => terminal::native_term_read_timeout(&evaluated),
        "native_term_flush" => terminal::native_term_flush(&evaluated),
        "native_term_poll" => terminal::native_term_poll(&evaluated),

        // ====================================================================
        // TCP Operations (16 functions)
        // ====================================================================
        "native_tcp_bind" => network::native_tcp_bind(&evaluated),
        "native_tcp_accept" => network::native_tcp_accept(&evaluated),
        "native_tcp_connect" => network::native_tcp_connect(&evaluated),
        "native_tcp_connect_timeout" => network::native_tcp_connect_timeout(&evaluated),
        "native_tcp_read" => network::native_tcp_read(&evaluated),
        "native_tcp_write" => network::native_tcp_write(&evaluated),
        "native_tcp_flush" => network::native_tcp_flush(&evaluated),
        "native_tcp_shutdown" => network::native_tcp_shutdown(&evaluated),
        "native_tcp_close" => network::native_tcp_close(&evaluated),
        "native_tcp_set_nodelay" => network::native_tcp_set_nodelay(&evaluated),
        "native_tcp_set_keepalive" => network::native_tcp_set_keepalive(&evaluated),
        "native_tcp_set_read_timeout" => network::native_tcp_set_read_timeout(&evaluated),
        "native_tcp_set_write_timeout" => network::native_tcp_set_write_timeout(&evaluated),
        "native_tcp_get_nodelay" => network::native_tcp_get_nodelay(&evaluated),
        "native_tcp_peek" => network::native_tcp_peek(&evaluated),
        "native_tcp_set_backlog" => network::native_tcp_set_backlog(&evaluated),

        // ====================================================================
        // UDP Operations (18 functions)
        // ====================================================================
        "native_udp_bind" => network::native_udp_bind(&evaluated),
        "native_udp_connect" => network::native_udp_connect(&evaluated),
        "native_udp_recv_from" => network::native_udp_recv_from(&evaluated),
        "native_udp_recv" => network::native_udp_recv(&evaluated),
        "native_udp_send_to" => network::native_udp_send_to(&evaluated),
        "native_udp_send" => network::native_udp_send(&evaluated),
        "native_udp_peek_from" => network::native_udp_peek_from(&evaluated),
        "native_udp_peek" => network::native_udp_peek(&evaluated),
        "native_udp_peer_addr" => network::native_udp_peer_addr(&evaluated),
        "native_udp_set_broadcast" => network::native_udp_set_broadcast(&evaluated),
        "native_udp_set_multicast_loop" => network::native_udp_set_multicast_loop(&evaluated),
        "native_udp_set_multicast_ttl" => network::native_udp_set_multicast_ttl(&evaluated),
        "native_udp_set_ttl" => network::native_udp_set_ttl(&evaluated),
        "native_udp_set_read_timeout" => network::native_udp_set_read_timeout(&evaluated),
        "native_udp_set_write_timeout" => network::native_udp_set_write_timeout(&evaluated),
        "native_udp_get_broadcast" => network::native_udp_get_broadcast(&evaluated),
        "native_udp_get_ttl" => network::native_udp_get_ttl(&evaluated),
        "native_udp_join_multicast_v4" => network::native_udp_join_multicast_v4(&evaluated),
        "native_udp_leave_multicast_v4" => network::native_udp_leave_multicast_v4(&evaluated),
        "native_udp_join_multicast_v6" => network::native_udp_join_multicast_v6(&evaluated),
        "native_udp_leave_multicast_v6" => network::native_udp_leave_multicast_v6(&evaluated),
        "native_udp_close" => network::native_udp_close(&evaluated),

        // ====================================================================
        // HTTP Operations (1 function)
        // ====================================================================
        "native_http_send" => network::native_http_send(&evaluated),

        // ====================================================================
        // System Operations (2 functions)
        // ====================================================================
        "sys_get_args" => system::sys_get_args(&evaluated),
        "sys_exit" => system::sys_exit(&evaluated),

        // ====================================================================
        // Lexer Operations (1 function)
        // ====================================================================
        "lexer_tokenize" => lexer_ffi::simple_lexer_tokenize(&evaluated),

        // ====================================================================
        // Environment Operations (8 functions)
        // ====================================================================
        "rt_env_set" => system::rt_env_set(&evaluated),
        "rt_env_get" => system::rt_env_get(&evaluated),
        "rt_env_exists" => system::rt_env_exists(&evaluated),
        "rt_env_remove" => system::rt_env_remove(&evaluated),
        "rt_env_all" => system::rt_env_all(&evaluated),
        "rt_env_home" => system::rt_env_home(&evaluated),
        "rt_env_temp" => system::rt_env_temp(&evaluated),
        "rt_env_cwd" => system::rt_env_cwd(&evaluated),
        "rt_platform_name" => system::rt_platform_name(&evaluated),
        "rt_exit" => system::rt_exit(&evaluated),

        // ====================================================================
        // Memory Operations (10 functions: 7 query + 3 allocator)
        // ====================================================================
        "memory_usage" => memory::memory_usage(&evaluated),
        "memory_limit" => memory::memory_limit(&evaluated),
        "memory_usage_percent" => memory::memory_usage_percent(&evaluated),
        "is_memory_limited" => memory::is_memory_limited(&evaluated),
        "default_memory_limit" => memory::default_memory_limit(&evaluated),
        "format_bytes" => memory::format_bytes(&evaluated),
        "parse_memory_size" => memory::parse_memory_size(&evaluated),

        // System allocator
        "sys_malloc" => memory::sys_malloc(&evaluated),
        "sys_free" => memory::sys_free(&evaluated),
        "sys_realloc" => memory::sys_realloc(&evaluated),

        // ====================================================================
        // RC/ARC Operations (20 functions: Rc + Arc reference counting)
        // ====================================================================
        // Rc box operations (non-atomic)
        "rc_box_size" => rc::rc_box_size(&evaluated),
        "rc_box_init" => rc::rc_box_init(&evaluated),
        "rc_box_get_value" => rc::rc_box_get_value(&evaluated),
        "rc_box_drop_value" => rc::rc_box_drop_value(&evaluated),
        "rc_box_strong_count" => rc::rc_box_strong_count(&evaluated),
        "rc_box_weak_count" => rc::rc_box_weak_count(&evaluated),
        "rc_box_inc_strong" => rc::rc_box_inc_strong(&evaluated),
        "rc_box_dec_strong" => rc::rc_box_dec_strong(&evaluated),
        "rc_box_inc_weak" => rc::rc_box_inc_weak(&evaluated),
        "rc_box_dec_weak" => rc::rc_box_dec_weak(&evaluated),

        // Arc box operations (atomic)
        "arc_box_size" => rc::arc_box_size(&evaluated),
        "arc_box_init" => rc::arc_box_init(&evaluated),
        "arc_box_get_value" => rc::arc_box_get_value(&evaluated),
        "arc_box_drop_value" => rc::arc_box_drop_value(&evaluated),
        "arc_box_strong_count" => rc::arc_box_strong_count(&evaluated),
        "arc_box_weak_count" => rc::arc_box_weak_count(&evaluated),
        "arc_box_inc_strong" => rc::arc_box_inc_strong(&evaluated),
        "arc_box_dec_strong" => rc::arc_box_dec_strong(&evaluated),
        "arc_box_inc_weak" => rc::arc_box_inc_weak(&evaluated),
        "arc_box_dec_weak" => rc::arc_box_dec_weak(&evaluated),

        // ====================================================================
        // Concurrency Operations (15 functions: Thread + Channel)
        // ====================================================================
        "rt_thread_available_parallelism" => concurrency::rt_thread_available_parallelism(&evaluated),
        "rt_thread_sleep" => concurrency::rt_thread_sleep(&evaluated),
        "rt_thread_yield" => concurrency::rt_thread_yield(&evaluated),
        "rt_thread_spawn_isolated" => {
            concurrency::rt_thread_spawn_isolated_with_context(&evaluated, env, functions, classes, enums, impl_methods)
        }
        "rt_thread_spawn_isolated2" => concurrency::rt_thread_spawn_isolated2_with_context(
            &evaluated,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        ),
        "rt_thread_join" => concurrency::rt_thread_join(&evaluated),
        "rt_thread_is_done" => concurrency::rt_thread_is_done(&evaluated),
        "rt_thread_id" => concurrency::rt_thread_id(&evaluated),
        "rt_thread_free" => concurrency::rt_thread_free(&evaluated),
        "rt_channel_new" => concurrency::rt_channel_new(&evaluated),
        "rt_channel_send" => concurrency::rt_channel_send(&evaluated),
        "rt_channel_try_recv" => concurrency::rt_channel_try_recv(&evaluated),
        "rt_channel_recv" => concurrency::rt_channel_recv(&evaluated),
        "rt_channel_close" => concurrency::rt_channel_close(&evaluated),
        "rt_channel_is_closed" => concurrency::rt_channel_is_closed(&evaluated),
        "rt_set_concurrent_backend" => concurrency::rt_set_concurrent_backend(&evaluated),
        "rt_get_concurrent_backend" => concurrency::rt_get_concurrent_backend(&evaluated),

        // ====================================================================
        // Runtime Config Operations (4 functions)
        // ====================================================================
        "rt_set_macro_trace" => system::rt_set_macro_trace(&evaluated),
        "rt_set_debug_mode" => system::rt_set_debug_mode(&evaluated),
        "rt_is_macro_trace_enabled" => system::rt_is_macro_trace_enabled(&evaluated),
        "rt_is_debug_mode_enabled" => system::rt_is_debug_mode_enabled(&evaluated),

        // ====================================================================
        // Ratatui TUI Functions (8 functions) - Requires 'tui' feature
        // ====================================================================
        #[cfg(feature = "tui")]
        "ratatui_terminal_new" => tui::ratatui_terminal_new_fn(&evaluated),
        #[cfg(feature = "tui")]
        "ratatui_terminal_cleanup" => tui::ratatui_terminal_cleanup_fn(&evaluated),
        #[cfg(feature = "tui")]
        "ratatui_terminal_clear" => tui::ratatui_terminal_clear_fn(&evaluated),
        #[cfg(feature = "tui")]
        "ratatui_textbuffer_new" => tui::ratatui_textbuffer_new_fn(&evaluated),
        #[cfg(feature = "tui")]
        "ratatui_textbuffer_insert_char" => tui::ratatui_textbuffer_insert_char_fn(&evaluated),
        #[cfg(feature = "tui")]
        "ratatui_textbuffer_backspace" => tui::ratatui_textbuffer_backspace_fn(&evaluated),
        #[cfg(feature = "tui")]
        "ratatui_textbuffer_newline" => tui::ratatui_textbuffer_newline_fn(&evaluated),
        #[cfg(feature = "tui")]
        "ratatui_object_destroy" => tui::ratatui_object_destroy_fn(&evaluated),

        // ====================================================================
        // REPL Runner Functions (2 functions)
        // ====================================================================
        "simple_repl_runner_init" => repl::simple_repl_runner_init_fn(&evaluated),
        "simple_repl_runner_cleanup" => repl::simple_repl_runner_cleanup_fn(&evaluated),

        // ====================================================================
        // Layout Marker Functions (1 function)
        // ====================================================================
        "simple_layout_mark" => layout::simple_layout_mark(&evaluated),

        // ====================================================================
        // Vulkan GPU Functions (13 functions, feature-gated)
        // ====================================================================
        "rt_vk_available" => gpu::rt_vk_available_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_device_create" => gpu::rt_vk_device_create_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_device_free" => gpu::rt_vk_device_free_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_device_sync" => gpu::rt_vk_device_sync_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_buffer_alloc" => gpu::rt_vk_buffer_alloc_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_buffer_free" => gpu::rt_vk_buffer_free_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_buffer_upload" => gpu::rt_vk_buffer_upload_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_buffer_download" => gpu::rt_vk_buffer_download_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_kernel_compile" => gpu::rt_vk_kernel_compile_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_kernel_free" => gpu::rt_vk_kernel_free_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_kernel_launch" => gpu::rt_vk_kernel_launch_fn(&evaluated),
        #[cfg(feature = "vulkan")]
        "rt_vk_kernel_launch_1d" => gpu::rt_vk_kernel_launch_1d_fn(&evaluated),

        // ====================================================================
        // Diagram FFI Functions (12 functions)
        // ====================================================================
        "rt_diagram_enable" => diagram::rt_diagram_enable(&evaluated),
        "rt_diagram_disable" => diagram::rt_diagram_disable(&evaluated),
        "rt_diagram_clear" => diagram::rt_diagram_clear(&evaluated),
        "rt_diagram_is_enabled" => diagram::rt_diagram_is_enabled(&evaluated),
        "rt_diagram_trace_method" => diagram::rt_diagram_trace_method(&evaluated),
        "rt_diagram_trace_method_with_args" => diagram::rt_diagram_trace_method_with_args(&evaluated),
        "rt_diagram_trace_return" => diagram::rt_diagram_trace_return(&evaluated),
        "rt_diagram_mark_architectural" => diagram::rt_diagram_mark_architectural(&evaluated),
        "rt_diagram_generate_sequence" => diagram::rt_diagram_generate_sequence(&evaluated),
        "rt_diagram_generate_class" => diagram::rt_diagram_generate_class(&evaluated),
        "rt_diagram_generate_arch" => diagram::rt_diagram_generate_arch(&evaluated),
        "rt_diagram_free_string" => diagram::rt_diagram_free_string(&evaluated),

        // ====================================================================
        // File I/O FFI Operations (rt_* functions)
        // ====================================================================
        // File metadata
        "rt_file_exists" | "rt_file_exists_str" => file_io::rt_file_exists(&evaluated),
        "rt_file_stat" => file_io::rt_file_stat(&evaluated),
        "rt_file_size" => file_io::rt_file_size(&evaluated),
        "rt_file_hash_sha256" => file_io::rt_file_hash_sha256(&evaluated),
        // File operations
        "rt_file_canonicalize" => file_io::rt_file_canonicalize(&evaluated),
        "rt_file_read_text" => file_io::rt_file_read_text(&evaluated),
        "rt_file_write_text" => file_io::rt_file_write_text(&evaluated),
        "rt_file_atomic_write" => file_io::rt_file_atomic_write(&evaluated),
        "rt_file_copy" => file_io::rt_file_copy(&evaluated),
        "rt_file_remove" => file_io::rt_file_remove(&evaluated),
        "rt_file_rename" => file_io::rt_file_rename(&evaluated),
        "rt_file_read_lines" => file_io::rt_file_read_lines(&evaluated),
        "rt_file_append_text" => file_io::rt_file_append_text(&evaluated),
        "rt_file_read_bytes" => file_io::rt_file_read_bytes(&evaluated),
        "rt_file_write_bytes" => file_io::rt_file_write_bytes(&evaluated),
        "rt_file_move" => file_io::rt_file_move(&evaluated),
        "rt_file_delete" => native_ffi::rt_file_delete(&evaluated),
        // Directory operations
        "rt_dir_create" => file_io::rt_dir_create(&evaluated),
        "rt_dir_list" => file_io::rt_dir_list(&evaluated),
        "rt_dir_remove" => file_io::rt_dir_remove(&evaluated),
        "rt_file_find" => file_io::rt_file_find(&evaluated),
        "rt_dir_glob" => file_io::rt_dir_glob(&evaluated),
        "rt_dir_create_all" => file_io::rt_dir_create_all(&evaluated),
        "rt_dir_walk" => file_io::rt_dir_walk(&evaluated),
        "rt_current_dir" => file_io::rt_current_dir(&evaluated),
        "rt_set_current_dir" => file_io::rt_set_current_dir(&evaluated),
        "rt_dir_remove_all" => file_io::rt_dir_remove_all(&evaluated),
        // File descriptor operations
        "rt_file_open" => file_io::rt_file_open(&evaluated),
        "rt_file_get_size" => file_io::rt_file_get_size(&evaluated),
        "rt_file_close" => file_io::rt_file_close(&evaluated),
        // Path operations
        "rt_path_basename" => file_io::rt_path_basename(&evaluated),
        "rt_path_dirname" => file_io::rt_path_dirname(&evaluated),
        "rt_path_ext" => file_io::rt_path_ext(&evaluated),
        "rt_path_absolute" => file_io::rt_path_absolute(&evaluated),
        "rt_path_separator" => file_io::rt_path_separator(&evaluated),
        "rt_path_stem" => file_io::rt_path_stem(&evaluated),
        "rt_path_relative" => file_io::rt_path_relative(&evaluated),
        "rt_path_join" => file_io::rt_path_join(&evaluated),
        // File locking
        "rt_file_lock" => file_io::rt_file_lock(&evaluated),
        "rt_file_unlock" => file_io::rt_file_unlock(&evaluated),
        // System info
        "rt_getpid" => file_io::rt_getpid(&evaluated),
        "rt_process_exists" => file_io::rt_process_exists(&evaluated),
        "rt_hostname" => file_io::rt_hostname(&evaluated),
        "rt_system_cpu_count" => file_io::rt_system_cpu_count(&evaluated),
        "rt_time_now_monotonic_ms" => file_io::rt_time_now_monotonic_ms(&evaluated),

        // ====================================================================
        // Collections FFI Operations (HashMap, HashSet, BTree)
        // ====================================================================
        // HashMap operations
        "__rt_hashmap_new" => collections::__rt_hashmap_new(&evaluated),
        "__rt_hashmap_insert" => collections::__rt_hashmap_insert(&evaluated),
        "__rt_hashmap_get" => collections::__rt_hashmap_get(&evaluated),
        "__rt_hashmap_contains_key" => collections::__rt_hashmap_contains_key(&evaluated),
        "__rt_hashmap_remove" => collections::__rt_hashmap_remove(&evaluated),
        "__rt_hashmap_len" => collections::__rt_hashmap_len(&evaluated),
        "__rt_hashmap_clear" => collections::__rt_hashmap_clear(&evaluated),
        "__rt_hashmap_keys" => collections::__rt_hashmap_keys(&evaluated),
        "__rt_hashmap_values" => collections::__rt_hashmap_values(&evaluated),
        "__rt_hashmap_entries" => collections::__rt_hashmap_entries(&evaluated),
        // HashSet operations
        "__rt_hashset_new" => collections::__rt_hashset_new(&evaluated),
        "__rt_hashset_insert" => collections::__rt_hashset_insert(&evaluated),
        "__rt_hashset_contains" => collections::__rt_hashset_contains(&evaluated),
        "__rt_hashset_remove" => collections::__rt_hashset_remove(&evaluated),
        "__rt_hashset_len" => collections::__rt_hashset_len(&evaluated),
        "__rt_hashset_clear" => collections::__rt_hashset_clear(&evaluated),
        "__rt_hashset_to_array" => collections::__rt_hashset_to_array(&evaluated),
        "__rt_hashset_union" => collections::__rt_hashset_union(&evaluated),
        "__rt_hashset_intersection" => collections::__rt_hashset_intersection(&evaluated),
        "__rt_hashset_difference" => collections::__rt_hashset_difference(&evaluated),
        "__rt_hashset_symmetric_difference" => collections::__rt_hashset_symmetric_difference(&evaluated),
        "__rt_hashset_is_subset" => collections::__rt_hashset_is_subset(&evaluated),
        "__rt_hashset_is_superset" => collections::__rt_hashset_is_superset(&evaluated),
        // BTreeMap operations
        "__rt_btreemap_new" => collections::__rt_btreemap_new(&evaluated),
        "__rt_btreemap_insert" => collections::__rt_btreemap_insert(&evaluated),
        "__rt_btreemap_get" => collections::__rt_btreemap_get(&evaluated),
        "__rt_btreemap_contains_key" => collections::__rt_btreemap_contains_key(&evaluated),
        "__rt_btreemap_remove" => collections::__rt_btreemap_remove(&evaluated),
        "__rt_btreemap_len" => collections::__rt_btreemap_len(&evaluated),
        "__rt_btreemap_clear" => collections::__rt_btreemap_clear(&evaluated),
        "__rt_btreemap_keys" => collections::__rt_btreemap_keys(&evaluated),
        "__rt_btreemap_values" => collections::__rt_btreemap_values(&evaluated),
        "__rt_btreemap_entries" => collections::__rt_btreemap_entries(&evaluated),
        "__rt_btreemap_first_key" => collections::__rt_btreemap_first_key(&evaluated),
        "__rt_btreemap_last_key" => collections::__rt_btreemap_last_key(&evaluated),
        // BTreeSet operations
        "__rt_btreeset_new" => collections::__rt_btreeset_new(&evaluated),
        "__rt_btreeset_insert" => collections::__rt_btreeset_insert(&evaluated),
        "__rt_btreeset_contains" => collections::__rt_btreeset_contains(&evaluated),
        "__rt_btreeset_remove" => collections::__rt_btreeset_remove(&evaluated),
        "__rt_btreeset_len" => collections::__rt_btreeset_len(&evaluated),
        "__rt_btreeset_clear" => collections::__rt_btreeset_clear(&evaluated),
        "__rt_btreeset_to_array" => collections::__rt_btreeset_to_array(&evaluated),
        "__rt_btreeset_first" => collections::__rt_btreeset_first(&evaluated),
        "__rt_btreeset_last" => collections::__rt_btreeset_last(&evaluated),
        "__rt_btreeset_union" => collections::__rt_btreeset_union(&evaluated),
        "__rt_btreeset_intersection" => collections::__rt_btreeset_intersection(&evaluated),
        "__rt_btreeset_difference" => collections::__rt_btreeset_difference(&evaluated),
        "__rt_btreeset_symmetric_difference" => collections::__rt_btreeset_symmetric_difference(&evaluated),
        "__rt_btreeset_is_subset" => collections::__rt_btreeset_is_subset(&evaluated),
        "__rt_btreeset_is_superset" => collections::__rt_btreeset_is_superset(&evaluated),

        // ====================================================================
        // CLI FFI Functions (46 functions - for Simple-based CLI)
        // ====================================================================
        // Basic CLI operations
        "rt_cli_version" => cli::rt_cli_version(&evaluated),
        "rt_cli_print_help" => cli::rt_cli_print_help(&evaluated),
        "rt_cli_print_version" => cli::rt_cli_print_version(&evaluated),
        "rt_cli_get_args" => cli::rt_cli_get_args(&evaluated),
        "rt_cli_file_exists" => cli::rt_cli_file_exists(&evaluated),
        "rt_cli_exit" => cli::rt_cli_exit(&evaluated),

        // Code execution
        "rt_cli_run_code" => cli::rt_cli_run_code(&evaluated),
        "rt_cli_run_file" => cli::rt_cli_run_file(&evaluated),
        "rt_cli_watch_file" => cli::rt_cli_watch_file(&evaluated),
        "rt_cli_run_repl" => cli::rt_cli_run_repl(&evaluated),

        // Testing
        "rt_cli_run_tests" => cli::rt_cli_run_tests(&evaluated),
        "rt_test_db_validate" => cli::rt_test_db_validate(&evaluated),
        "rt_test_db_enable_validation" => cli::rt_test_db_enable_validation(&evaluated),
        "rt_test_run_is_stale" => cli::rt_test_run_is_stale(&evaluated),
        "rt_test_db_cleanup_stale_runs" => cli::rt_test_db_cleanup_stale_runs(&evaluated),

        // Code quality
        "rt_cli_run_lint" => cli::rt_cli_run_lint(&evaluated),
        "rt_cli_run_fmt" => cli::rt_cli_run_fmt(&evaluated),
        "rt_cli_run_check" => cli::rt_cli_run_check(&evaluated),

        // Verification
        "rt_cli_run_verify" => cli::rt_cli_run_verify(&evaluated),

        // Migration and tooling
        "rt_cli_run_migrate" => cli::rt_cli_run_migrate(&evaluated),
        "rt_cli_run_mcp" => cli::rt_cli_run_mcp(&evaluated),
        "rt_cli_run_diff" => cli::rt_cli_run_diff(&evaluated),
        "rt_cli_run_context" => cli::rt_cli_run_context(&evaluated),
        "rt_cli_run_constr" => cli::rt_cli_run_constr(&evaluated),

        // Analysis
        "rt_cli_run_query" => cli::rt_cli_run_query(&evaluated),
        "rt_cli_run_info" => cli::rt_cli_run_info(&evaluated),

        // Auditing
        "rt_cli_run_spec_coverage" => cli::rt_cli_run_spec_coverage(&evaluated),
        "rt_cli_run_replay" => cli::rt_cli_run_replay(&evaluated),

        // Code generation
        "rt_cli_run_gen_lean" => cli::rt_cli_run_gen_lean(&evaluated),
        "rt_cli_run_feature_gen" => cli::rt_cli_run_feature_gen(&evaluated),
        "rt_cli_run_task_gen" => cli::rt_cli_run_task_gen(&evaluated),
        "rt_cli_run_spec_gen" => cli::rt_cli_run_spec_gen(&evaluated),
        "rt_cli_run_sspec_docgen" => cli::rt_cli_run_sspec_docgen(&evaluated),
        "rt_cli_run_todo_scan" => cli::rt_cli_run_todo_scan(&evaluated),
        "rt_cli_run_todo_gen" => cli::rt_cli_run_todo_gen(&evaluated),

        // i18n
        "rt_cli_run_i18n" => cli::rt_cli_run_i18n(&evaluated),

        // FFI generator
        "rt_cli_run_ffi_gen" => cli::rt_cli_run_ffi_gen(&evaluated),

        // Context pack generation
        "rt_context_generate" => cli::rt_context_generate(&evaluated),
        "rt_context_stats" => cli::rt_context_stats(&evaluated),

        // Settlement stub
        "rt_settlement_main" => cli::rt_settlement_main(&evaluated),

        // Compilation
        "rt_cli_handle_compile" => cli::rt_cli_handle_compile(&evaluated),
        "rt_cli_handle_targets" => cli::rt_cli_handle_targets(&evaluated),
        "rt_cli_handle_linkers" => cli::rt_cli_handle_linkers(&evaluated),

        // Web framework
        "rt_cli_handle_web" => cli::rt_cli_handle_web(&evaluated),

        // Diagram generation
        "rt_cli_handle_diagram" => cli::rt_cli_handle_diagram(&evaluated),

        // Package management
        "rt_cli_handle_init" => cli::rt_cli_handle_init(&evaluated),
        "rt_cli_handle_add" => cli::rt_cli_handle_add(&evaluated),
        "rt_cli_handle_remove" => cli::rt_cli_handle_remove(&evaluated),
        "rt_cli_handle_install" => cli::rt_cli_handle_install(&evaluated),
        "rt_cli_handle_update" => cli::rt_cli_handle_update(&evaluated),
        "rt_cli_handle_list" => cli::rt_cli_handle_list(&evaluated),
        "rt_cli_handle_tree" => cli::rt_cli_handle_tree(&evaluated),
        "rt_cli_handle_cache" => cli::rt_cli_handle_cache(&evaluated),

        // Environment management
        "rt_cli_handle_env" => cli::rt_cli_handle_env(&evaluated),

        // Lock file management
        "rt_cli_handle_lock" => cli::rt_cli_handle_lock(&evaluated),

        // Explicit run command
        "rt_cli_handle_run" => cli::rt_cli_handle_run(&evaluated),

        // Fault detection configuration
        "rt_fault_set_stack_overflow_detection" => cli::rt_fault_set_stack_overflow_detection(&evaluated),
        "rt_fault_set_max_recursion_depth" => cli::rt_fault_set_max_recursion_depth(&evaluated),
        "rt_fault_set_timeout" => cli::rt_fault_set_timeout(&evaluated),
        "rt_fault_set_execution_limit" => cli::rt_fault_set_execution_limit(&evaluated),

        // ====================================================================
        // Cargo Build System Functions (4 functions)
        // ====================================================================
        "rt_cargo_build" => cargo::rt_cargo_build(&evaluated),
        "rt_cargo_test" => cargo::rt_cargo_test(&evaluated),
        "rt_cargo_test_doc" => cargo::rt_cargo_test_doc(&evaluated),
        "rt_cargo_clean" => cargo::rt_cargo_clean(&evaluated),
        "rt_cargo_check" => cargo::rt_cargo_check(&evaluated),
        "rt_cargo_lint" => cargo::rt_cargo_lint(&evaluated),
        "rt_cargo_fmt" => cargo::rt_cargo_fmt(&evaluated),

        // SDN operations
        "rt_sdn_version" => sdn::rt_sdn_version(&evaluated),
        "rt_sdn_check" => sdn::rt_sdn_check(&evaluated),
        "rt_sdn_to_json" => sdn::rt_sdn_to_json(&evaluated),
        "rt_sdn_from_json" => sdn::rt_sdn_from_json(&evaluated),
        "rt_sdn_get" => sdn::rt_sdn_get(&evaluated),
        "rt_sdn_set" => sdn::rt_sdn_set(&evaluated),
        "rt_sdn_fmt" => sdn::rt_sdn_fmt(&evaluated),

        // ====================================================================
        // Coverage Operations (7 functions + 5 FFI functions)
        // ====================================================================
        "coverage_scan" => coverage::coverage_scan(&evaluated),
        "coverage_class" => coverage::coverage_class(&evaluated),
        "coverage_func" => coverage::coverage_func(&evaluated),
        "coverage_report" => coverage::coverage_report(&evaluated),
        "coverage_generate" => coverage::coverage_generate(&evaluated),
        "coverage_check" => coverage::coverage_check(&evaluated),
        "coverage_summary" => coverage::coverage_summary(&evaluated),
        // FFI functions for coverage.spl
        "rt_coverage_enabled" => coverage::rt_coverage_enabled(&evaluated),
        "rt_coverage_clear" => coverage::rt_coverage_clear(&evaluated),
        "rt_coverage_dump_sdn" => coverage::rt_coverage_dump_sdn(&evaluated),
        "rt_coverage_free_sdn" => coverage::rt_coverage_free_sdn(&evaluated),
        "rt_cstring_to_text" => coverage::rt_cstring_to_text(&evaluated),

        // ====================================================================
        // Cranelift FFI Functions (for self-hosting compiler)
        // ====================================================================
        // Module management
        "rt_cranelift_module_new" => cranelift::rt_cranelift_module_new(&evaluated),
        "rt_cranelift_new_module" => cranelift::rt_cranelift_new_module(&evaluated),
        "rt_cranelift_finalize_module" => cranelift::rt_cranelift_finalize_module(&evaluated),
        "rt_cranelift_free_module" => cranelift::rt_cranelift_free_module(&evaluated),
        "rt_cranelift_emit_object" => cranelift::rt_cranelift_emit_object(&evaluated),

        // Signature management
        "rt_cranelift_new_signature" => cranelift::rt_cranelift_new_signature(&evaluated),
        "rt_cranelift_sig_add_param" => cranelift::rt_cranelift_sig_add_param(&evaluated),
        "rt_cranelift_sig_set_return" => cranelift::rt_cranelift_sig_set_return(&evaluated),

        // Function building
        "rt_cranelift_begin_function" => cranelift::rt_cranelift_begin_function(&evaluated),
        "rt_cranelift_end_function" => cranelift::rt_cranelift_end_function(&evaluated),
        "rt_cranelift_define_function" => cranelift::rt_cranelift_define_function(&evaluated),

        // Block management
        "rt_cranelift_create_block" => cranelift::rt_cranelift_create_block(&evaluated),
        "rt_cranelift_switch_to_block" => cranelift::rt_cranelift_switch_to_block(&evaluated),
        "rt_cranelift_seal_block" => cranelift::rt_cranelift_seal_block(&evaluated),
        "rt_cranelift_seal_all_blocks" => cranelift::rt_cranelift_seal_all_blocks(&evaluated),
        "rt_cranelift_append_block_param" => cranelift::rt_cranelift_append_block_param(&evaluated),
        "rt_cranelift_block_param" => cranelift::rt_cranelift_block_param(&evaluated),

        // Constants
        "rt_cranelift_iconst" => cranelift::rt_cranelift_iconst(&evaluated),
        "rt_cranelift_fconst" => cranelift::rt_cranelift_fconst(&evaluated),
        "rt_cranelift_bconst" => cranelift::rt_cranelift_bconst(&evaluated),
        "rt_cranelift_null" => cranelift::rt_cranelift_null(&evaluated),

        // Arithmetic
        "rt_cranelift_iadd" => cranelift::rt_cranelift_iadd(&evaluated),
        "rt_cranelift_isub" => cranelift::rt_cranelift_isub(&evaluated),
        "rt_cranelift_imul" => cranelift::rt_cranelift_imul(&evaluated),
        "rt_cranelift_sdiv" => cranelift::rt_cranelift_sdiv(&evaluated),
        "rt_cranelift_udiv" => cranelift::rt_cranelift_udiv(&evaluated),
        "rt_cranelift_srem" => cranelift::rt_cranelift_srem(&evaluated),
        "rt_cranelift_urem" => cranelift::rt_cranelift_urem(&evaluated),
        "rt_cranelift_fadd" => cranelift::rt_cranelift_fadd(&evaluated),
        "rt_cranelift_fsub" => cranelift::rt_cranelift_fsub(&evaluated),
        "rt_cranelift_fmul" => cranelift::rt_cranelift_fmul(&evaluated),
        "rt_cranelift_fdiv" => cranelift::rt_cranelift_fdiv(&evaluated),

        // Bitwise
        "rt_cranelift_band" => cranelift::rt_cranelift_band(&evaluated),
        "rt_cranelift_bor" => cranelift::rt_cranelift_bor(&evaluated),
        "rt_cranelift_bxor" => cranelift::rt_cranelift_bxor(&evaluated),
        "rt_cranelift_bnot" => cranelift::rt_cranelift_bnot(&evaluated),
        "rt_cranelift_ishl" => cranelift::rt_cranelift_ishl(&evaluated),
        "rt_cranelift_ushr" => cranelift::rt_cranelift_ushr(&evaluated),
        "rt_cranelift_sshr" => cranelift::rt_cranelift_sshr(&evaluated),

        // Comparison
        "rt_cranelift_icmp" => cranelift::rt_cranelift_icmp(&evaluated),
        "rt_cranelift_fcmp" => cranelift::rt_cranelift_fcmp(&evaluated),

        // Memory
        "rt_cranelift_load" => cranelift::rt_cranelift_load(&evaluated),
        "rt_cranelift_store" => cranelift::rt_cranelift_store(&evaluated),
        "rt_cranelift_stack_slot" => cranelift::rt_cranelift_stack_slot(&evaluated),
        "rt_cranelift_stack_addr" => cranelift::rt_cranelift_stack_addr(&evaluated),

        // Control flow
        "rt_cranelift_jump" => cranelift::rt_cranelift_jump(&evaluated),
        "rt_cranelift_brif" => cranelift::rt_cranelift_brif(&evaluated),
        "rt_cranelift_return" => cranelift::rt_cranelift_return(&evaluated),
        "rt_cranelift_return_void" => cranelift::rt_cranelift_return_void(&evaluated),
        "rt_cranelift_trap" => cranelift::rt_cranelift_trap(&evaluated),

        // Function calls
        "rt_cranelift_call" => cranelift::rt_cranelift_call(&evaluated),
        "rt_cranelift_call_indirect" => cranelift::rt_cranelift_call_indirect(&evaluated),

        // Type conversions
        "rt_cranelift_sextend" => cranelift::rt_cranelift_sextend(&evaluated),
        "rt_cranelift_uextend" => cranelift::rt_cranelift_uextend(&evaluated),
        "rt_cranelift_ireduce" => cranelift::rt_cranelift_ireduce(&evaluated),
        "rt_cranelift_fcvt_to_sint" => cranelift::rt_cranelift_fcvt_to_sint(&evaluated),
        "rt_cranelift_fcvt_to_uint" => cranelift::rt_cranelift_fcvt_to_uint(&evaluated),
        "rt_cranelift_fcvt_from_sint" => cranelift::rt_cranelift_fcvt_from_sint(&evaluated),
        "rt_cranelift_fcvt_from_uint" => cranelift::rt_cranelift_fcvt_from_uint(&evaluated),
        "rt_cranelift_bitcast" => cranelift::rt_cranelift_bitcast(&evaluated),

        // JIT execution
        "rt_cranelift_get_function_ptr" => cranelift::rt_cranelift_get_function_ptr(&evaluated),
        "rt_cranelift_call_function_ptr" => cranelift::rt_cranelift_call_function_ptr(&evaluated),

        // Bootstrap test FFI
        "rt_exec" => cranelift::rt_exec(&evaluated),
        "rt_file_hash" => cranelift::rt_file_hash(&evaluated),
        "rt_write_file" => cranelift::rt_write_file(&evaluated),

        // ====================================================================
        // Mock Policy Operations (6 functions)
        // ====================================================================
        "__mock_policy_init_all" => mock_policy::mock_policy_init_all(&evaluated),
        "__mock_policy_init_hal_only" => mock_policy::mock_policy_init_hal_only(&evaluated),
        "__mock_policy_disable" => mock_policy::mock_policy_disable(&evaluated),
        "__mock_policy_init_patterns" => mock_policy::mock_policy_init_patterns(&evaluated),
        "__mock_policy_check" => mock_policy::mock_policy_check(&evaluated),
        "__mock_policy_try_check" => mock_policy::mock_policy_try_check(&evaluated),
        "__mock_policy_get_mode" => mock_policy::mock_policy_get_mode(&evaluated),

        // ====================================================================
        // Sandbox Operations (21 functions)
        // ====================================================================
        "rt_sandbox_reset" => sandbox::rt_sandbox_reset_fn(&evaluated),
        "rt_sandbox_set_cpu_time" => sandbox::rt_sandbox_set_cpu_time_fn(&evaluated),
        "rt_sandbox_set_memory" => sandbox::rt_sandbox_set_memory_fn(&evaluated),
        "rt_sandbox_set_fd_limit" => sandbox::rt_sandbox_set_fd_limit_fn(&evaluated),
        "rt_sandbox_set_thread_limit" => sandbox::rt_sandbox_set_thread_limit_fn(&evaluated),
        "rt_sandbox_disable_network" => sandbox::rt_sandbox_disable_network_fn(&evaluated),
        "rt_sandbox_set_network_allowlist" => sandbox::rt_sandbox_set_network_allowlist_fn(&evaluated),
        "rt_sandbox_set_network_blocklist" => sandbox::rt_sandbox_set_network_blocklist_fn(&evaluated),
        "rt_sandbox_add_allowed_domain" => sandbox::rt_sandbox_add_allowed_domain_fn(&evaluated),
        "rt_sandbox_add_blocked_domain" => sandbox::rt_sandbox_add_blocked_domain_fn(&evaluated),
        "rt_sandbox_set_fs_readonly" => sandbox::rt_sandbox_set_fs_readonly_fn(&evaluated),
        "rt_sandbox_set_fs_restricted" => sandbox::rt_sandbox_set_fs_restricted_fn(&evaluated),
        "rt_sandbox_set_fs_overlay" => sandbox::rt_sandbox_set_fs_overlay_fn(&evaluated),
        "rt_sandbox_add_read_path" => sandbox::rt_sandbox_add_read_path_fn(&evaluated),
        "rt_sandbox_add_write_path" => sandbox::rt_sandbox_add_write_path_fn(&evaluated),
        "rt_sandbox_apply" => sandbox::rt_sandbox_apply_fn(&evaluated),
        "rt_sandbox_cleanup" => sandbox::rt_sandbox_cleanup_fn(&evaluated),
        "rt_sandbox_is_configured" => sandbox::rt_sandbox_is_configured_fn(&evaluated),
        "rt_sandbox_get_cpu_time" => sandbox::rt_sandbox_get_cpu_time_fn(&evaluated),
        "rt_sandbox_get_memory" => sandbox::rt_sandbox_get_memory_fn(&evaluated),
        "rt_sandbox_get_network_mode" => sandbox::rt_sandbox_get_network_mode_fn(&evaluated),
        "rt_sandbox_get_fs_mode" => sandbox::rt_sandbox_get_fs_mode_fn(&evaluated),

        // ====================================================================
        // FFI Value Operations (17 functions)
        // ====================================================================
        // Value creation
        "rt_value_int" => ffi_value::rt_value_int_fn(&evaluated),
        "rt_value_float" => ffi_value::rt_value_float_fn(&evaluated),
        "rt_value_bool" => ffi_value::rt_value_bool_fn(&evaluated),
        "rt_value_nil" => ffi_value::rt_value_nil_fn(&evaluated),

        // Value extraction
        "rt_value_as_int" => ffi_value::rt_value_as_int_fn(&evaluated),
        "rt_value_as_float" => ffi_value::rt_value_as_float_fn(&evaluated),
        "rt_value_as_bool" => ffi_value::rt_value_as_bool_fn(&evaluated),

        // Value type checking
        "rt_value_truthy" => ffi_value::rt_value_truthy_fn(&evaluated),
        "rt_value_is_nil" => ffi_value::rt_value_is_nil_fn(&evaluated),
        "rt_value_is_int" => ffi_value::rt_value_is_int_fn(&evaluated),
        "rt_value_is_float" => ffi_value::rt_value_is_float_fn(&evaluated),
        "rt_value_is_bool" => ffi_value::rt_value_is_bool_fn(&evaluated),
        "rt_value_is_heap" => ffi_value::rt_value_is_heap_fn(&evaluated),
        "rt_value_type_tag" => ffi_value::rt_value_type_tag_fn(&evaluated),

        // Error handling
        "rt_function_not_found" => ffi_value::rt_function_not_found_fn(&evaluated),
        "rt_method_not_found" => ffi_value::rt_method_not_found_fn(&evaluated),
        "rt_is_error" => ffi_value::rt_is_error_fn(&evaluated),

        // ====================================================================
        // FFI Array Operations (7 functions)
        // ====================================================================
        "rt_array_new" => ffi_array::rt_array_new_fn(&evaluated),
        "rt_array_push" => ffi_array::rt_array_push_fn(&evaluated),
        "rt_array_get" => ffi_array::rt_array_get_fn(&evaluated),
        "rt_array_set" => ffi_array::rt_array_set_fn(&evaluated),
        "rt_array_pop" => ffi_array::rt_array_pop_fn(&evaluated),
        "rt_array_clear" => ffi_array::rt_array_clear_fn(&evaluated),
        "rt_array_len" => ffi_array::rt_array_len_fn(&evaluated),

        // ====================================================================
        // FFI Dictionary Operations (7 functions)
        // ====================================================================
        "rt_dict_new" => ffi_dict::rt_dict_new_fn(&evaluated),
        "rt_dict_set" => ffi_dict::rt_dict_set_fn(&evaluated),
        "rt_dict_get" => ffi_dict::rt_dict_get_fn(&evaluated),
        "rt_dict_len" => ffi_dict::rt_dict_len_fn(&evaluated),
        "rt_dict_clear" => ffi_dict::rt_dict_clear_fn(&evaluated),
        "rt_dict_keys" => ffi_dict::rt_dict_keys_fn(&evaluated),
        "rt_dict_values" => ffi_dict::rt_dict_values_fn(&evaluated),

        // ====================================================================
        // FFI String Operations (4 functions)
        // ====================================================================
        "rt_string_new" => ffi_string::rt_string_new_fn(&evaluated),
        "rt_string_concat" => ffi_string::rt_string_concat_fn(&evaluated),
        "rt_string_len" => ffi_string::rt_string_len_fn(&evaluated),
        "rt_string_eq" => ffi_string::rt_string_eq_fn(&evaluated),

        // ====================================================================
        // I18n Operations (5 functions)
        // ====================================================================
        "rt_i18n_context_new" => i18n::rt_i18n_context_new(env),
        "rt_i18n_context_insert" => i18n::rt_i18n_context_insert(&evaluated, env),
        "rt_i18n_context_free" => i18n::rt_i18n_context_free(&evaluated, env),
        "rt_i18n_get_message" => i18n::rt_i18n_get_message(&evaluated, env),
        "rt_i18n_severity_name" => i18n::rt_i18n_severity_name(&evaluated, env),

        // Unknown extern function
        // ====================================================================
        // Native Compilation & Execution (3 functions)
        // ====================================================================
        "rt_compile_to_native" => native_ffi::rt_compile_to_native(&evaluated),
        "rt_execute_native" => native_ffi::rt_execute_native(&evaluated),

        // ====================================================================
        // Package Management Operations (11 functions)
        // ====================================================================
        "rt_package_sha256" => package::sha256(&evaluated),
        "rt_package_create_tarball" => package::create_tarball(&evaluated),
        "rt_package_extract_tarball" => package::extract_tarball(&evaluated),
        "rt_package_file_size" => package::file_size(&evaluated),
        "rt_package_copy_file" => package::copy_file(&evaluated),
        "rt_package_mkdir_all" => package::mkdir_all(&evaluated),
        "rt_package_remove_dir_all" => package::remove_dir_all(&evaluated),
        "rt_package_create_symlink" => package::create_symlink(&evaluated),
        "rt_package_chmod" => package::chmod(&evaluated),
        "rt_package_exists" => package::exists(&evaluated),
        "rt_package_is_dir" => package::is_dir(&evaluated),

        // ====================================================================
        // Regex Operations (8 functions)
        // ====================================================================
        "ffi_regex_is_match" => regex::is_match(&evaluated),
        "ffi_regex_find" => regex::find(&evaluated),
        "ffi_regex_find_all" => regex::find_all(&evaluated),
        "ffi_regex_captures" => regex::captures(&evaluated),
        "ffi_regex_replace" => regex::replace(&evaluated),
        "ffi_regex_replace_all" => regex::replace_all(&evaluated),
        "ffi_regex_split" => regex::split(&evaluated),
        "ffi_regex_split_n" => regex::split_n(&evaluated),

        // ====================================================================
        // JSON Operations (4 functions)
        // ====================================================================
        "json_parse" => json::json_parse(&evaluated),
        "json_serialize" => json::json_serialize(&evaluated),
        "json_pretty" => json::json_pretty(&evaluated),
        "parse_int" => json::parse_int(&evaluated),

        // ====================================================================
        // AST Node Accessor FFI (28 functions)
        // ====================================================================
        "rt_ast_expr_tag" => ast_ffi::rt_ast_expr_tag(&evaluated),
        "rt_ast_expr_int_value" => ast_ffi::rt_ast_expr_int_value(&evaluated),
        "rt_ast_expr_float_value" => ast_ffi::rt_ast_expr_float_value(&evaluated),
        "rt_ast_expr_string_value" => ast_ffi::rt_ast_expr_string_value(&evaluated),
        "rt_ast_expr_bool_value" => ast_ffi::rt_ast_expr_bool_value(&evaluated),
        "rt_ast_expr_ident_name" => ast_ffi::rt_ast_expr_ident_name(&evaluated),
        "rt_ast_expr_binary_op" => ast_ffi::rt_ast_expr_binary_op(&evaluated),
        "rt_ast_expr_binary_left" => ast_ffi::rt_ast_expr_binary_left(&evaluated),
        "rt_ast_expr_binary_right" => ast_ffi::rt_ast_expr_binary_right(&evaluated),
        "rt_ast_expr_unary_op" => ast_ffi::rt_ast_expr_unary_op(&evaluated),
        "rt_ast_expr_unary_operand" => ast_ffi::rt_ast_expr_unary_operand(&evaluated),
        "rt_ast_expr_call_callee" => ast_ffi::rt_ast_expr_call_callee(&evaluated),
        "rt_ast_expr_call_arg_count" => ast_ffi::rt_ast_expr_call_arg_count(&evaluated),
        "rt_ast_expr_call_arg" => ast_ffi::rt_ast_expr_call_arg(&evaluated),
        "rt_ast_arg_value" => ast_ffi::rt_ast_arg_value(&evaluated),
        "rt_ast_arg_name" => ast_ffi::rt_ast_arg_name(&evaluated),
        "rt_ast_expr_method_receiver" => ast_ffi::rt_ast_expr_method_receiver(&evaluated),
        "rt_ast_expr_method_name" => ast_ffi::rt_ast_expr_method_name(&evaluated),
        "rt_ast_expr_method_arg_count" => ast_ffi::rt_ast_expr_method_arg_count(&evaluated),
        "rt_ast_expr_method_arg" => ast_ffi::rt_ast_expr_method_arg(&evaluated),
        "rt_ast_expr_field_receiver" => ast_ffi::rt_ast_expr_field_receiver(&evaluated),
        "rt_ast_expr_field_name" => ast_ffi::rt_ast_expr_field_name(&evaluated),
        "rt_ast_expr_array_len" => ast_ffi::rt_ast_expr_array_len(&evaluated),
        "rt_ast_expr_array_get" => ast_ffi::rt_ast_expr_array_get(&evaluated),
        "rt_ast_expr_free" => ast_ffi::rt_ast_expr_free(&evaluated),
        "rt_ast_node_free" => ast_ffi::rt_ast_node_free(&evaluated),
        "rt_ast_arg_free" => ast_ffi::rt_ast_arg_free(&evaluated),
        "rt_ast_registry_clear" => ast_ffi::rt_ast_registry_clear(&evaluated),
        "rt_ast_registry_count" => ast_ffi::rt_ast_registry_count(&evaluated),

        // ====================================================================
        // Environment/Scope FFI (12 functions)
        // ====================================================================
        "rt_env_new_handle" => env_ffi::rt_env_new(&evaluated),
        "rt_env_push_scope" => env_ffi::rt_env_push_scope(&evaluated),
        "rt_env_pop_scope" => env_ffi::rt_env_pop_scope(&evaluated),
        "rt_env_define_var" => env_ffi::rt_env_define(&evaluated),
        "rt_env_get_var" => env_ffi::rt_env_get_var(&evaluated),
        "rt_env_set_var" => env_ffi::rt_env_set_var(&evaluated),
        "rt_env_has_var" => env_ffi::rt_env_has_var(&evaluated),
        "rt_env_snapshot" => env_ffi::rt_env_snapshot(&evaluated),
        "rt_env_scope_depth" => env_ffi::rt_env_scope_depth(&evaluated),
        "rt_env_free_handle" => env_ffi::rt_env_free_handle(&evaluated),
        "rt_env_var_count" => env_ffi::rt_env_var_count(&evaluated),
        "rt_env_var_names" => env_ffi::rt_env_var_names(&evaluated),

        // ====================================================================
        // Error Creation FFI (9 functions)
        // ====================================================================
        "rt_error_semantic" => error_ffi::rt_error_semantic(&evaluated),
        "rt_error_type_mismatch" => error_ffi::rt_error_type_mismatch(&evaluated),
        "rt_error_undefined_var" => error_ffi::rt_error_undefined_var(&evaluated),
        "rt_error_arg_count" => error_ffi::rt_error_arg_count(&evaluated),
        "rt_error_division_by_zero" => error_ffi::rt_error_division_by_zero(&evaluated),
        "rt_error_index_oob" => error_ffi::rt_error_index_oob(&evaluated),
        "rt_error_throw" => error_ffi::rt_error_throw(&evaluated),
        "rt_error_message" => error_ffi::rt_error_message(&evaluated),
        "rt_error_free" => error_ffi::rt_error_free(&evaluated),

        // ====================================================================
        // Span Interop FFI (6 functions)
        // ====================================================================
        "rt_span_create" => span_ffi::rt_span_create(&evaluated),
        "rt_span_start" => span_ffi::rt_span_start(&evaluated),
        "rt_span_end" => span_ffi::rt_span_end(&evaluated),
        "rt_span_line" => span_ffi::rt_span_line(&evaluated),
        "rt_span_column" => span_ffi::rt_span_column(&evaluated),
        "rt_span_free" => span_ffi::rt_span_free(&evaluated),

        _ => Err(common::unknown_function(name)),
    }
}
