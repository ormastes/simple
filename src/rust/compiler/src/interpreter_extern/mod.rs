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
pub mod terminal;
pub mod atomic;
pub mod tui;
pub mod repl;
pub mod gpu;

// Import parent interpreter types
type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

// Import shared functions from parent module
use super::{evaluate_expr, is_debug_mode};

// Import diagram tracing
use simple_runtime::value::diagram_ffi;

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
        "print" => io::print::print(&evaluated),
        "print_raw" => io::print::print_raw(&evaluated),
        "println" => io::print::println(&evaluated),
        "eprint" => io::print::eprint(&evaluated),
        "eprint_raw" => io::print::eprint_raw(&evaluated),
        "eprintln" => io::print::eprintln(&evaluated),
        "dprint" => io::print::dprint(&evaluated),
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
        // Time Operations (2 functions)
        // ====================================================================
        "rt_time_now_seconds" => time::rt_time_now_seconds(&evaluated),
        "_current_time_unix" => time::_current_time_unix(&evaluated),

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
        // Process Control (2 functions)
        // ====================================================================
        "exit" => process::exit(&evaluated),
        "panic" => process::panic(&evaluated),

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

        // ====================================================================
        // Runtime Config Operations (2 functions)
        // ====================================================================
        "rt_set_macro_trace" => system::rt_set_macro_trace(&evaluated),
        "rt_set_debug_mode" => system::rt_set_debug_mode(&evaluated),

        // ====================================================================
        // Ratatui TUI Functions (8 functions)
        // ====================================================================
        "ratatui_terminal_new" => tui::ratatui_terminal_new_fn(&evaluated),
        "ratatui_terminal_cleanup" => tui::ratatui_terminal_cleanup_fn(&evaluated),
        "ratatui_terminal_clear" => tui::ratatui_terminal_clear_fn(&evaluated),
        "ratatui_textbuffer_new" => tui::ratatui_textbuffer_new_fn(&evaluated),
        "ratatui_textbuffer_insert_char" => tui::ratatui_textbuffer_insert_char_fn(&evaluated),
        "ratatui_textbuffer_backspace" => tui::ratatui_textbuffer_backspace_fn(&evaluated),
        "ratatui_textbuffer_newline" => tui::ratatui_textbuffer_newline_fn(&evaluated),
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

        // Unknown extern function
        _ => Err(common::unknown_function(name)),
    }
}
