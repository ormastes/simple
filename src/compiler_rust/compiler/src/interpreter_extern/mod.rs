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
//! ### SFFI Operations
//! - `atomic`: Atomic operations (AtomicBool, AtomicInt, AtomicFlag)
//! - `tui`: Ratatui TUI bindings
//! - `repl`: REPL runner integration
//! - `gpu`: Vulkan GPU compute operations (feature-gated)

use std::sync::{Arc, LazyLock};
use crate::error::CompileError;
use crate::value::{Env, Value};
use simple_parser::ast::{Argument, ClassDef, EnumDef, FunctionDef};
use std::collections::HashMap;

/// Function pointer type for extern dispatches.
type ExternHandler = fn(
    &[Value],
    &mut Env,
    &mut HashMap<String, Arc<FunctionDef>>,
    &mut HashMap<String, Arc<ClassDef>>,
    &Enums,
    &ImplMethods,
) -> Result<Value, CompileError>;

/// Static dispatch table for O(1) extern function lookup.
static EXTERN_DISPATCH: LazyLock<HashMap<&'static str, ExternHandler>> = LazyLock::new(init_dispatch_table);

// Module declarations
pub mod common;
pub mod conversion;
pub mod process;
pub mod pty;
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
pub mod torch;
pub mod atomic;
pub mod concurrency;
#[cfg(feature = "tui")]
pub mod tui;
pub mod repl;
pub mod gpu;
pub mod simd;
pub mod diagram;
pub mod memory;
pub mod cli;
pub mod cargo;
pub mod sdn;
pub mod coverage;
pub mod cranelift;
pub mod jit_native;
// pub mod perf; // TODO: file not yet created
pub mod sandbox;
pub mod mock_policy;
pub mod sffi_value;
pub mod sffi_array;
pub mod sffi_db;
pub mod sffi_dict;
pub mod signatures;
pub mod pbkdf2;
pub mod sffi_string;
pub mod collections;
pub mod lexer_sffi;
pub mod tls13;
pub mod i18n;
pub mod native_sffi;
pub mod package;
pub mod regex;
pub mod hosted;
pub mod ast_sffi;
pub mod env_sffi;
pub mod error_sffi;
pub mod span_sffi;
pub mod rc;
pub mod wsffi;
pub mod crypto;
pub mod sha512;
pub mod dynamic_sffi;
#[cfg(feature = "gui")]
pub mod winit_sffi;
pub mod rapier2d_sffi;
pub mod io_driver;
pub mod qmp_socket;
pub mod host_wm_bridge;

// Import parent interpreter types
type Enums = HashMap<String, Arc<EnumDef>>;
type ImplMethods = HashMap<String, Vec<Arc<FunctionDef>>>;

// Import shared functions from parent module
use super::{evaluate_expr, is_debug_mode};
use crate::interpreter::interpreter_call::exec_function_with_values;
use crate::interpreter::interpreter_native_net;
use crate::interpreter::interpreter_event_loop;

// Import diagram tracing
use simple_runtime::value::diagram_sffi;

/// Resolve fmt() methods on Object values for print functions.
/// Converts Objects with fmt() methods to their string representation.
fn resolve_fmt_for_print(
    values: &[Value],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
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

fn call_loaded_function_by_name(
    lookup_name: &str,
    args: &[Value],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let func = functions
        .get(lookup_name)
        .cloned()
        .ok_or_else(|| CompileError::semantic(format!("function `{lookup_name}` not found for extern bridge")))?;
    exec_function_with_values(&func, args, env, functions, classes, enums, impl_methods)
}

// ---------------------------------------------------------------------------
// Stub wrappers for functions whose natural call-site passes an empty slice
// or returns a fixed value — needed so they match `ExternFn = fn(&[Value])`.
// ---------------------------------------------------------------------------

/// `rt_stdin_read_line` — read a line from stdin (ignores all args)
fn rt_stdin_read_line_stub(_args: &[Value]) -> Result<Value, CompileError> {
    io::input::input(&[])
}

/// `rt_tls_client_connect` / `rt_tls_client_connect_with_sni` — stub
fn rt_tls_client_connect_stub(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(-1))
}

/// `rt_tls_client_write` — stub
fn rt_tls_client_write_stub(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(-1))
}

/// `rt_tls_client_read` — stub
fn rt_tls_client_read_stub(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Str(String::new()))
}

/// `rt_tls_client_close` — stub
fn rt_tls_client_close_stub(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

/// `rt_tls_get_protocol_version` — stub
fn rt_tls_get_protocol_version_stub(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Str(String::new()))
}

/// `rt_perf_*` stubs — perf module not yet implemented
fn rt_perf_stub(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Nil)
}

/// Build the dispatch table mapping extern function names to their implementations.
/// Only includes "simple" functions that take `&[Value]` and return `Result<Value, CompileError>`.
/// Complex functions (needing env, functions, classes, etc.) remain in the match fallback.
fn init_dispatch_table() -> HashMap<&'static str, ExternHandler> {
    let mut m = HashMap::with_capacity(1200);
    macro_rules! insert_simple {
        ($name:literal, $handler:path) => {
            m.insert(
                $name,
                (|evaluated, _env, _functions, _classes, _enums, _impl_methods| $handler(evaluated)) as ExternHandler,
            );
        };
    }
    insert_simple!("abs", math::abs);
    insert_simple!("arc_box_dec_strong", rc::arc_box_dec_strong);
    insert_simple!("arc_box_dec_weak", rc::arc_box_dec_weak);
    insert_simple!("arc_box_drop_value", rc::arc_box_drop_value);
    insert_simple!("arc_box_get_value", rc::arc_box_get_value);
    insert_simple!("arc_box_inc_strong", rc::arc_box_inc_strong);
    insert_simple!("arc_box_inc_weak", rc::arc_box_inc_weak);
    insert_simple!("arc_box_init", rc::arc_box_init);
    insert_simple!("arc_box_size", rc::arc_box_size);
    insert_simple!("arc_box_strong_count", rc::arc_box_strong_count);
    insert_simple!("arc_box_weak_count", rc::arc_box_weak_count);
    insert_simple!("bytes_to_u16_be", conversion::bytes_to_u16_be_fn);
    insert_simple!("bytes_to_u16_le", conversion::bytes_to_u16_le_fn);
    insert_simple!("bytes_to_u32_be", conversion::bytes_to_u32_be_fn);
    insert_simple!("bytes_to_u32_le", conversion::bytes_to_u32_le_fn);
    insert_simple!("bytes_to_u64_be", conversion::bytes_to_u64_be_fn);
    insert_simple!("bytes_to_u64_le", conversion::bytes_to_u64_le_fn);
    insert_simple!("ceil", math::ceil);
    insert_simple!("coverage_check", coverage::coverage_check);
    insert_simple!("coverage_class", coverage::coverage_class);
    insert_simple!("coverage_func", coverage::coverage_func);
    insert_simple!("coverage_generate", coverage::coverage_generate);
    insert_simple!("coverage_report", coverage::coverage_report);
    insert_simple!("coverage_scan", coverage::coverage_scan);
    insert_simple!("coverage_summary", coverage::coverage_summary);
    insert_simple!("_current_time_unix", time::_current_time_unix);
    insert_simple!("default_memory_limit", memory::default_memory_limit);
    insert_simple!("dprint", io::print::dprint);
    insert_simple!("eprintln", io::print::eprintln);
    insert_simple!("exit", process::exit);
    insert_simple!("f32_from_bits", memory::f32_from_bits);
    insert_simple!("sffi_regex_captures", regex::captures);
    insert_simple!("sffi_regex_find_all", regex::find_all);
    insert_simple!("sffi_regex_find", regex::find);
    insert_simple!("sffi_regex_is_match", regex::is_match);
    insert_simple!("sffi_regex_replace_all", regex::replace_all);
    insert_simple!("sffi_regex_replace", regex::replace);
    insert_simple!("sffi_regex_split_n", regex::split_n);
    insert_simple!("sffi_regex_split", regex::split);
    insert_simple!("floor", math::floor);
    insert_simple!("format_bytes", memory::format_bytes);
    insert_simple!("input", io::input::input);
    insert_simple!("is_memory_limited", memory::is_memory_limited);
    insert_simple!("lexer_tokenize", lexer_sffi::simple_lexer_tokenize);
    insert_simple!("max", math::max);
    insert_simple!("memory_limit", memory::memory_limit);
    insert_simple!("memory_usage", memory::memory_usage);
    insert_simple!("memory_usage_percent", memory::memory_usage_percent);
    insert_simple!("min", math::min);
    insert_simple!("__mock_policy_check", mock_policy::mock_policy_check);
    insert_simple!("__mock_policy_disable", mock_policy::mock_policy_disable);
    insert_simple!("__mock_policy_get_mode", mock_policy::mock_policy_get_mode);
    insert_simple!("__mock_policy_init_all", mock_policy::mock_policy_init_all);
    insert_simple!("__mock_policy_init_hal_only", mock_policy::mock_policy_init_hal_only);
    insert_simple!("__mock_policy_init_patterns", mock_policy::mock_policy_init_patterns);
    insert_simple!("__mock_policy_try_check", mock_policy::mock_policy_try_check);
    insert_simple!("native_disable_raw_mode", terminal::native_disable_raw_mode);
    insert_simple!("native_enable_raw_mode", terminal::native_enable_raw_mode);
    insert_simple!("native_file_close", filesystem::native_file_close);
    insert_simple!("native_file_flush", filesystem::native_file_flush);
    insert_simple!("native_file_read", filesystem::native_file_read);
    insert_simple!("native_file_seek", filesystem::native_file_seek);
    insert_simple!("native_file_sync", filesystem::native_file_sync);
    insert_simple!("native_file_write", filesystem::native_file_write);
    insert_simple!("native_fs_append", filesystem::native_fs_append);
    insert_simple!("native_fs_copy", filesystem::native_fs_copy);
    insert_simple!("native_fs_create_dir", filesystem::native_fs_create_dir);
    insert_simple!("native_fs_exists", filesystem::native_fs_exists);
    insert_simple!("native_fs_metadata", filesystem::native_fs_metadata);
    insert_simple!("native_fs_open", filesystem::native_fs_open);
    insert_simple!("native_fs_read_dir", filesystem::native_fs_read_dir);
    insert_simple!("native_fs_read", filesystem::native_fs_read);
    insert_simple!("native_fs_read_string", filesystem::native_fs_read_string);
    insert_simple!("native_fs_remove_dir", filesystem::native_fs_remove_dir);
    insert_simple!("native_fs_remove_file", filesystem::native_fs_remove_file);
    insert_simple!("native_fs_rename", filesystem::native_fs_rename);
    insert_simple!("native_fs_write", filesystem::native_fs_write);
    insert_simple!("native_fs_write_string", filesystem::native_fs_write_string);
    insert_simple!("native_get_term_size", terminal::native_get_term_size);
    insert_simple!("native_http_send", network::native_http_send);
    insert_simple!("native_is_tty", terminal::native_is_tty);
    insert_simple!("native_stderr", terminal::native_stderr);
    insert_simple!("native_stdin", terminal::native_stdin);
    insert_simple!("native_stdout", terminal::native_stdout);
    insert_simple!("native_tcp_accept", network::native_tcp_accept);
    insert_simple!("native_tcp_bind", network::native_tcp_bind);
    insert_simple!("native_tcp_close", network::native_tcp_close);
    insert_simple!("native_tcp_connect", network::native_tcp_connect);
    insert_simple!("native_tcp_connect_timeout", network::native_tcp_connect_timeout);
    insert_simple!("native_tcp_flush", network::native_tcp_flush);
    insert_simple!("native_tcp_get_nodelay", network::native_tcp_get_nodelay);
    insert_simple!("native_tcp_peek", network::native_tcp_peek);
    insert_simple!("native_tcp_read", network::native_tcp_read);
    insert_simple!("native_tcp_set_backlog", network::native_tcp_set_backlog);
    insert_simple!("native_tcp_set_keepalive", network::native_tcp_set_keepalive);
    insert_simple!("native_tcp_set_nodelay", network::native_tcp_set_nodelay);
    insert_simple!("native_tcp_set_read_timeout", network::native_tcp_set_read_timeout);
    insert_simple!("native_tcp_set_write_timeout", network::native_tcp_set_write_timeout);
    insert_simple!("native_tcp_shutdown", network::native_tcp_shutdown);
    insert_simple!("native_tcp_write", network::native_tcp_write);
    insert_simple!("native_term_flush", terminal::native_term_flush);
    insert_simple!("native_term_poll", terminal::native_term_poll);
    insert_simple!("native_term_read", terminal::native_term_read);
    insert_simple!("native_term_read_timeout", terminal::native_term_read_timeout);
    insert_simple!("native_term_write", terminal::native_term_write);
    insert_simple!("native_udp_bind", network::native_udp_bind);
    insert_simple!("native_udp_close", network::native_udp_close);
    insert_simple!("native_udp_connect", network::native_udp_connect);
    insert_simple!("native_udp_get_broadcast", network::native_udp_get_broadcast);
    insert_simple!("native_udp_get_ttl", network::native_udp_get_ttl);
    insert_simple!("native_udp_join_multicast_v4", network::native_udp_join_multicast_v4);
    insert_simple!("native_udp_join_multicast_v6", network::native_udp_join_multicast_v6);
    insert_simple!("native_udp_leave_multicast_v4", network::native_udp_leave_multicast_v4);
    insert_simple!("native_udp_leave_multicast_v6", network::native_udp_leave_multicast_v6);
    insert_simple!("native_udp_peek_from", network::native_udp_peek_from);
    insert_simple!("native_udp_peek", network::native_udp_peek);
    insert_simple!("native_udp_peer_addr", network::native_udp_peer_addr);
    insert_simple!("native_udp_recv_from", network::native_udp_recv_from);
    insert_simple!("native_udp_recv", network::native_udp_recv);
    insert_simple!("native_udp_send", network::native_udp_send);
    insert_simple!("native_udp_send_to", network::native_udp_send_to);
    insert_simple!("native_udp_set_broadcast", network::native_udp_set_broadcast);
    insert_simple!("native_udp_set_multicast_loop", network::native_udp_set_multicast_loop);
    insert_simple!("native_udp_set_multicast_ttl", network::native_udp_set_multicast_ttl);
    insert_simple!("native_udp_set_read_timeout", network::native_udp_set_read_timeout);
    insert_simple!("native_udp_set_ttl", network::native_udp_set_ttl);
    insert_simple!("native_udp_set_write_timeout", network::native_udp_set_write_timeout);
    insert_simple!("panic", process::panic);
    insert_simple!("parse_memory_size", memory::parse_memory_size);
    insert_simple!("pow", math::pow);
    insert_simple!("println", io::print::println);
    insert_simple!("rc_box_dec_strong", rc::rc_box_dec_strong);
    insert_simple!("rc_box_dec_weak", rc::rc_box_dec_weak);
    insert_simple!("rc_box_drop_value", rc::rc_box_drop_value);
    insert_simple!("rc_box_get_value", rc::rc_box_get_value);
    insert_simple!("rc_box_inc_strong", rc::rc_box_inc_strong);
    insert_simple!("rc_box_inc_weak", rc::rc_box_inc_weak);
    insert_simple!("rc_box_init", rc::rc_box_init);
    insert_simple!("rc_box_size", rc::rc_box_size);
    insert_simple!("rc_box_strong_count", rc::rc_box_strong_count);
    insert_simple!("rc_box_weak_count", rc::rc_box_weak_count);
    insert_simple!("rt_aes128_decrypt_block_pure", simd::rt_aes128_decrypt_block_pure);
    insert_simple!("rt_aes128_encrypt_block_into", simd::rt_aes128_encrypt_block_into);
    insert_simple!("rt_aes128_encrypt_block_pure", simd::rt_aes128_encrypt_block_pure);
    insert_simple!("rt_aes256_encrypt_block_into", simd::rt_aes256_encrypt_block_into);
    insert_simple!("rt_aes256_encrypt_block_pure", simd::rt_aes256_encrypt_block_pure);
    insert_simple!(
        "rt_aes_decrypt_block_with_expanded",
        simd::rt_aes_decrypt_block_with_expanded
    );
    insert_simple!(
        "rt_aes_encrypt_block_with_expanded",
        simd::rt_aes_encrypt_block_with_expanded
    );
    insert_simple!("rt_aes_rcon", simd::rt_aes_rcon);
    insert_simple!("rt_aes_sbox", simd::rt_aes_sbox);
    insert_simple!("rt_alloc", memory::rt_alloc);
    insert_simple!("rt_array_clear", sffi_array::rt_array_clear_fn);
    insert_simple!("rt_array_extend_i64", sffi_array::rt_array_extend_i64_fn);
    insert_simple!("rt_array_get", sffi_array::rt_array_get_fn);
    insert_simple!("rt_array_get_text", sffi_array::rt_array_get_fn);
    insert_simple!("rt_array_len", sffi_array::rt_array_len_fn);
    insert_simple!("rt_array_new", sffi_array::rt_array_new_fn);
    insert_simple!("rt_array_new_with_cap", sffi_array::rt_array_new_with_cap_fn);
    insert_simple!("rt_array_new_with_cap_text", sffi_array::rt_array_new_with_cap_fn);
    insert_simple!("rt_array_pop", sffi_array::rt_array_pop_fn);
    insert_simple!("rt_array_push", sffi_array::rt_array_push_fn);
    insert_simple!("rt_array_repeat", sffi_array::rt_array_repeat_fn);
    insert_simple!("rt_array_set", sffi_array::rt_array_set_fn);
    insert_simple!("rt_array_set_len_known", sffi_array::rt_array_set_len_known_fn);
    insert_simple!("rt_array_set_len_known_text", sffi_array::rt_array_set_len_known_fn);
    insert_simple!("rt_array_set_text", sffi_array::rt_array_set_fn);
    insert_simple!("rt_ast_arg_free", ast_sffi::rt_ast_arg_free);
    insert_simple!("rt_ast_arg_name", ast_sffi::rt_ast_arg_name);
    insert_simple!("rt_ast_arg_value", ast_sffi::rt_ast_arg_value);
    insert_simple!("rt_ast_expr_array_get", ast_sffi::rt_ast_expr_array_get);
    insert_simple!("rt_ast_expr_array_len", ast_sffi::rt_ast_expr_array_len);
    insert_simple!("rt_ast_expr_binary_left", ast_sffi::rt_ast_expr_binary_left);
    insert_simple!("rt_ast_expr_binary_op", ast_sffi::rt_ast_expr_binary_op);
    insert_simple!("rt_ast_expr_binary_right", ast_sffi::rt_ast_expr_binary_right);
    insert_simple!("rt_ast_expr_bool_value", ast_sffi::rt_ast_expr_bool_value);
    insert_simple!("rt_ast_expr_call_arg", ast_sffi::rt_ast_expr_call_arg);
    insert_simple!("rt_ast_expr_call_arg_count", ast_sffi::rt_ast_expr_call_arg_count);
    insert_simple!("rt_ast_expr_call_callee", ast_sffi::rt_ast_expr_call_callee);
    insert_simple!("rt_ast_expr_field_name", ast_sffi::rt_ast_expr_field_name);
    insert_simple!("rt_ast_expr_field_receiver", ast_sffi::rt_ast_expr_field_receiver);
    insert_simple!("rt_ast_expr_float_value", ast_sffi::rt_ast_expr_float_value);
    insert_simple!("rt_ast_expr_free", ast_sffi::rt_ast_expr_free);
    insert_simple!("rt_ast_expr_ident_name", ast_sffi::rt_ast_expr_ident_name);
    insert_simple!("rt_ast_expr_int_value", ast_sffi::rt_ast_expr_int_value);
    insert_simple!("rt_ast_expr_method_arg", ast_sffi::rt_ast_expr_method_arg);
    insert_simple!("rt_ast_expr_method_arg_count", ast_sffi::rt_ast_expr_method_arg_count);
    insert_simple!("rt_ast_expr_method_name", ast_sffi::rt_ast_expr_method_name);
    insert_simple!("rt_ast_expr_method_receiver", ast_sffi::rt_ast_expr_method_receiver);
    insert_simple!("rt_ast_expr_string_value", ast_sffi::rt_ast_expr_string_value);
    insert_simple!("rt_ast_expr_tag", ast_sffi::rt_ast_expr_tag);
    insert_simple!("rt_ast_expr_unary_op", ast_sffi::rt_ast_expr_unary_op);
    insert_simple!("rt_ast_expr_unary_operand", ast_sffi::rt_ast_expr_unary_operand);
    insert_simple!("rt_ast_node_free", ast_sffi::rt_ast_node_free);
    insert_simple!("rt_ast_registry_clear", ast_sffi::rt_ast_registry_clear);
    insert_simple!("rt_ast_registry_count", ast_sffi::rt_ast_registry_count);
    insert_simple!("rt_async_ws_read_raw", network::rt_async_ws_read_raw);
    insert_simple!("rt_async_ws_write_raw", network::rt_async_ws_write_raw);
    insert_simple!("rt_atomic_bool_free", atomic::rt_atomic_bool_free);
    insert_simple!("rt_atomic_bool_load", atomic::rt_atomic_bool_load);
    insert_simple!("rt_atomic_bool_new", atomic::rt_atomic_bool_new);
    insert_simple!("rt_atomic_bool_store", atomic::rt_atomic_bool_store);
    insert_simple!("rt_atomic_bool_swap", atomic::rt_atomic_bool_swap);
    insert_simple!("rt_atomic_compare_exchange", atomic::rt_atomic_compare_exchange_fn);
    insert_simple!("rt_atomic_fetch_add", atomic::rt_atomic_fetch_add_fn);
    insert_simple!("rt_atomic_fetch_add_u64", atomic::rt_atomic_fetch_add_u64);
    insert_simple!("rt_atomic_fetch_and", atomic::rt_atomic_fetch_and_fn);
    insert_simple!("rt_atomic_fetch_or", atomic::rt_atomic_fetch_or_fn);
    insert_simple!("rt_atomic_fetch_sub", atomic::rt_atomic_fetch_sub_fn);
    insert_simple!("rt_atomic_flag_clear", atomic::rt_atomic_flag_clear);
    insert_simple!("rt_atomic_flag_free", atomic::rt_atomic_flag_free);
    insert_simple!("rt_atomic_flag_new", atomic::rt_atomic_flag_new);
    insert_simple!("rt_atomic_flag_test_and_set", atomic::rt_atomic_flag_test_and_set);
    insert_simple!("rt_atomic_int_compare_exchange", atomic::rt_atomic_int_compare_exchange);
    insert_simple!("rt_atomic_int_fetch_add", atomic::rt_atomic_int_fetch_add);
    insert_simple!("rt_atomic_int_fetch_and", atomic::rt_atomic_int_fetch_and);
    insert_simple!("rt_atomic_int_fetch_or", atomic::rt_atomic_int_fetch_or);
    insert_simple!("rt_atomic_int_fetch_sub", atomic::rt_atomic_int_fetch_sub);
    insert_simple!("rt_atomic_int_fetch_xor", atomic::rt_atomic_int_fetch_xor);
    insert_simple!("rt_atomic_int_free", atomic::rt_atomic_int_free);
    insert_simple!("rt_atomic_int_load", atomic::rt_atomic_int_load);
    insert_simple!("rt_atomic_int_new", atomic::rt_atomic_int_new);
    insert_simple!("rt_atomic_int_store", atomic::rt_atomic_int_store);
    insert_simple!("rt_atomic_int_swap", atomic::rt_atomic_int_swap);
    insert_simple!("rt_atomic_load", atomic::rt_atomic_load_fn);
    insert_simple!("rt_atomic_load_u32", atomic::rt_atomic_load_u32);
    insert_simple!("rt_atomic_load_u64", atomic::rt_atomic_load_u64);
    insert_simple!("rt_atomic_new", atomic::rt_atomic_new_fn);
    insert_simple!("rt_atomic_store", atomic::rt_atomic_store_fn);
    insert_simple!("rt_atomic_store_u32", atomic::rt_atomic_store_u32);
    insert_simple!("rt_atomic_store_u64", atomic::rt_atomic_store_u64);
    insert_simple!("rt_atomic_store_u8", atomic::rt_atomic_store_u8);
    insert_simple!("rt_atomic_swap", atomic::rt_atomic_swap_fn);
    insert_simple!("rt_base64_decode", crypto::rt_base64_decode);
    insert_simple!("rt_base64_encode", crypto::rt_base64_encode);
    insert_simple!("rt_base64url_decode", crypto::rt_base64url_decode);
    insert_simple!("rt_base64url_encode", crypto::rt_base64url_encode);
    insert_simple!("rt_black_box", file_io::rt_black_box);
    insert_simple!("__rt_btreemap_clear", collections::__rt_btreemap_clear);
    insert_simple!("__rt_btreemap_contains_key", collections::__rt_btreemap_contains_key);
    insert_simple!("__rt_btreemap_entries", collections::__rt_btreemap_entries);
    insert_simple!("__rt_btreemap_first_key", collections::__rt_btreemap_first_key);
    insert_simple!("__rt_btreemap_get", collections::__rt_btreemap_get);
    insert_simple!("__rt_btreemap_insert", collections::__rt_btreemap_insert);
    insert_simple!("__rt_btreemap_keys", collections::__rt_btreemap_keys);
    insert_simple!("__rt_btreemap_last_key", collections::__rt_btreemap_last_key);
    insert_simple!("__rt_btreemap_len", collections::__rt_btreemap_len);
    insert_simple!("__rt_btreemap_new", collections::__rt_btreemap_new);
    insert_simple!("__rt_btreemap_remove", collections::__rt_btreemap_remove);
    insert_simple!("__rt_btreemap_values", collections::__rt_btreemap_values);
    insert_simple!("__rt_btreeset_clear", collections::__rt_btreeset_clear);
    insert_simple!("__rt_btreeset_contains", collections::__rt_btreeset_contains);
    insert_simple!("__rt_btreeset_difference", collections::__rt_btreeset_difference);
    insert_simple!("__rt_btreeset_first", collections::__rt_btreeset_first);
    insert_simple!("__rt_btreeset_insert", collections::__rt_btreeset_insert);
    insert_simple!("__rt_btreeset_intersection", collections::__rt_btreeset_intersection);
    insert_simple!("__rt_btreeset_is_subset", collections::__rt_btreeset_is_subset);
    insert_simple!("__rt_btreeset_is_superset", collections::__rt_btreeset_is_superset);
    insert_simple!("__rt_btreeset_last", collections::__rt_btreeset_last);
    insert_simple!("__rt_btreeset_len", collections::__rt_btreeset_len);
    insert_simple!("__rt_btreeset_new", collections::__rt_btreeset_new);
    insert_simple!("__rt_btreeset_remove", collections::__rt_btreeset_remove);
    insert_simple!(
        "__rt_btreeset_symmetric_difference",
        collections::__rt_btreeset_symmetric_difference
    );
    insert_simple!("__rt_btreeset_to_array", collections::__rt_btreeset_to_array);
    insert_simple!("__rt_btreeset_union", collections::__rt_btreeset_union);
    insert_simple!("rt_byte_array_new", sffi_array::rt_byte_array_new_fn);
    insert_simple!("rt_byte_array_new_len", sffi_array::rt_byte_array_new_fn);
    insert_simple!("rt_byte_char", conversion::rt_byte_char_fn);
    insert_simple!("rt_bytes_alloc", file_io::rt_bytes_alloc);
    insert_simple!("rt_bytes_from_raw", file_io::rt_bytes_from_raw);
    insert_simple!("rt_bytes_to_text", conversion::rt_bytes_to_text_fn);
    insert_simple!("rt_bytes_u32_le_at", sffi_array::rt_bytes_u32_le_at_fn);
    insert_simple!("rt_bytes_u64_le_at", sffi_array::rt_bytes_u64_le_at_fn);
    insert_simple!("rt_bytes_u8_at", sffi_array::rt_bytes_u8_at_fn);
    insert_simple!("rt_bytes_u8_set", sffi_array::rt_bytes_u8_set_fn);
    insert_simple!("rt_cargo_build", cargo::rt_cargo_build);
    insert_simple!("rt_cargo_check", cargo::rt_cargo_check);
    insert_simple!("rt_cargo_clean", cargo::rt_cargo_clean);
    insert_simple!("rt_cargo_fmt", cargo::rt_cargo_fmt);
    insert_simple!("rt_cargo_lint", cargo::rt_cargo_lint);
    insert_simple!("rt_cargo_test", cargo::rt_cargo_test);
    insert_simple!("rt_cargo_test_doc", cargo::rt_cargo_test_doc);
    insert_simple!("rt_channel_close", concurrency::rt_channel_close);
    insert_simple!("rt_channel_is_closed", concurrency::rt_channel_is_closed);
    insert_simple!("rt_channel_new", concurrency::rt_channel_new);
    insert_simple!("rt_channel_recv", concurrency::rt_channel_recv);
    insert_simple!("rt_channel_send", concurrency::rt_channel_send);
    insert_simple!("rt_channel_try_recv", concurrency::rt_channel_try_recv);
    insert_simple!("rt_cli_exit", cli::rt_cli_exit);
    insert_simple!("rt_cli_file_exists", cli::rt_cli_file_exists);
    insert_simple!("rt_cli_get_args", cli::rt_cli_get_args);
    insert_simple!("rt_cli_handle_add", cli::rt_cli_handle_add);
    insert_simple!("rt_cli_handle_cache", cli::rt_cli_handle_cache);
    insert_simple!("rt_cli_handle_compile", cli::rt_cli_handle_compile);
    insert_simple!("rt_cli_handle_diagram", cli::rt_cli_handle_diagram);
    insert_simple!("rt_cli_handle_env", cli::rt_cli_handle_env);
    insert_simple!("rt_cli_handle_init", cli::rt_cli_handle_init);
    insert_simple!("rt_cli_handle_install", cli::rt_cli_handle_install);
    insert_simple!("rt_cli_handle_linkers", cli::rt_cli_handle_linkers);
    insert_simple!("rt_cli_handle_list", cli::rt_cli_handle_list);
    insert_simple!("rt_cli_handle_lock", cli::rt_cli_handle_lock);
    insert_simple!("rt_cli_handle_remove", cli::rt_cli_handle_remove);
    insert_simple!("rt_cli_handle_run", cli::rt_cli_handle_run);
    insert_simple!("rt_cli_handle_targets", cli::rt_cli_handle_targets);
    insert_simple!("rt_cli_handle_tree", cli::rt_cli_handle_tree);
    insert_simple!("rt_cli_handle_update", cli::rt_cli_handle_update);
    insert_simple!("rt_cli_handle_web", cli::rt_cli_handle_web);
    insert_simple!("rt_cli_print_help", cli::rt_cli_print_help);
    insert_simple!("rt_cli_print_version", cli::rt_cli_print_version);
    insert_simple!("rt_cli_run_check", cli::rt_cli_run_check);
    insert_simple!("rt_cli_run_code", cli::rt_cli_run_code);
    insert_simple!("rt_cli_run_constr", cli::rt_cli_run_constr);
    insert_simple!("rt_cli_run_context", cli::rt_cli_run_context);
    insert_simple!("rt_cli_run_diff", cli::rt_cli_run_diff);
    insert_simple!("rt_cli_run_feature_gen", cli::rt_cli_run_feature_gen);
    insert_simple!("rt_cli_run_sffi_gen", cli::rt_cli_run_sffi_gen);
    insert_simple!("rt_cli_run_file", cli::rt_cli_run_file);
    insert_simple!("rt_cli_run_fmt", cli::rt_cli_run_fmt);
    insert_simple!("rt_cli_run_gen_lean", cli::rt_cli_run_gen_lean);
    insert_simple!("rt_cli_run_i18n", cli::rt_cli_run_i18n);
    insert_simple!("rt_cli_run_info", cli::rt_cli_run_info);
    insert_simple!("rt_cli_run_lint", cli::rt_cli_run_lint);
    insert_simple!("rt_cli_run_mcp", cli::rt_cli_run_mcp);
    insert_simple!("rt_cli_run_migrate", cli::rt_cli_run_migrate);
    insert_simple!("rt_cli_run_query", cli::rt_cli_run_query);
    insert_simple!("rt_cli_run_replay", cli::rt_cli_run_replay);
    insert_simple!("rt_cli_run_repl", cli::rt_cli_run_repl);
    insert_simple!("rt_cli_run_spec_coverage", cli::rt_cli_run_spec_coverage);
    insert_simple!("rt_cli_run_spec_gen", cli::rt_cli_run_spec_gen);
    insert_simple!("rt_cli_run_spipe_docgen", cli::rt_cli_run_spipe_docgen);
    insert_simple!("rt_cli_run_task_gen", cli::rt_cli_run_task_gen);
    insert_simple!("rt_cli_run_tests", cli::rt_cli_run_tests);
    insert_simple!("rt_cli_run_todo_gen", cli::rt_cli_run_todo_gen);
    insert_simple!("rt_cli_run_todo_scan", cli::rt_cli_run_todo_scan);
    insert_simple!("rt_cli_run_verify", cli::rt_cli_run_verify);
    insert_simple!("rt_cli_version", cli::rt_cli_version);
    insert_simple!("rt_cli_watch_file", cli::rt_cli_watch_file);
    insert_simple!("rt_compile_to_llvm_ir", native_sffi::rt_compile_to_llvm_ir);
    insert_simple!("rt_compile_to_native", native_sffi::rt_compile_to_native);
    insert_simple!("rt_compile_to_native_with_opt", native_sffi::rt_compile_to_native);
    insert_simple!("rt_constant_time_compare", crypto::rt_constant_time_compare);
    insert_simple!("rt_context_generate", cli::rt_context_generate);
    insert_simple!("rt_context_stats", cli::rt_context_stats);
    insert_simple!("rt_coverage_clear", coverage::rt_coverage_clear);
    insert_simple!("rt_coverage_condition_probe", coverage::rt_coverage_condition_probe_fn);
    insert_simple!("rt_coverage_decision_probe", coverage::rt_coverage_decision_probe_fn);
    insert_simple!("rt_coverage_dump_sdn", coverage::rt_coverage_dump_sdn);
    insert_simple!("rt_coverage_enable", coverage::rt_coverage_enable_fn);
    insert_simple!("rt_coverage_enabled", coverage::rt_coverage_enabled);
    insert_simple!("rt_coverage_enable_timed", coverage::rt_coverage_enable_timed_fn);
    insert_simple!("rt_coverage_free_sdn", coverage::rt_coverage_free_sdn);
    insert_simple!(
        "rt_cranelift_append_block_param",
        cranelift::rt_cranelift_append_block_param
    );
    insert_simple!("rt_cranelift_band", cranelift::rt_cranelift_band);
    insert_simple!("rt_cranelift_bconst", cranelift::rt_cranelift_bconst);
    insert_simple!("rt_cranelift_begin_function", cranelift::rt_cranelift_begin_function);
    insert_simple!("rt_cranelift_bitcast", cranelift::rt_cranelift_bitcast);
    insert_simple!("rt_cranelift_block_param", cranelift::rt_cranelift_block_param);
    insert_simple!("rt_cranelift_bnot", cranelift::rt_cranelift_bnot);
    insert_simple!("rt_cranelift_bor", cranelift::rt_cranelift_bor);
    insert_simple!("rt_cranelift_brif", cranelift::rt_cranelift_brif);
    insert_simple!("rt_cranelift_bxor", cranelift::rt_cranelift_bxor);
    insert_simple!("rt_cranelift_call", cranelift::rt_cranelift_call);
    insert_simple!(
        "rt_cranelift_call_function_ptr",
        cranelift::rt_cranelift_call_function_ptr
    );
    insert_simple!("rt_cranelift_call_indirect", cranelift::rt_cranelift_call_indirect);
    insert_simple!("rt_cranelift_create_block", cranelift::rt_cranelift_create_block);
    insert_simple!("rt_cranelift_define_function", cranelift::rt_cranelift_define_function);
    insert_simple!("rt_cranelift_emit_object", cranelift::rt_cranelift_emit_object);
    insert_simple!("rt_cranelift_end_function", cranelift::rt_cranelift_end_function);
    insert_simple!("rt_cranelift_fadd", cranelift::rt_cranelift_fadd);
    insert_simple!("rt_cranelift_fcmp", cranelift::rt_cranelift_fcmp);
    insert_simple!("rt_cranelift_fconst", cranelift::rt_cranelift_fconst);
    insert_simple!("rt_cranelift_fcvt_from_sint", cranelift::rt_cranelift_fcvt_from_sint);
    insert_simple!("rt_cranelift_fcvt_from_uint", cranelift::rt_cranelift_fcvt_from_uint);
    insert_simple!("rt_cranelift_fcvt_to_sint", cranelift::rt_cranelift_fcvt_to_sint);
    insert_simple!("rt_cranelift_fcvt_to_uint", cranelift::rt_cranelift_fcvt_to_uint);
    insert_simple!("rt_cranelift_fdiv", cranelift::rt_cranelift_fdiv);
    insert_simple!("rt_cranelift_finalize_module", cranelift::rt_cranelift_finalize_module);
    insert_simple!("rt_cranelift_fmul", cranelift::rt_cranelift_fmul);
    insert_simple!("rt_cranelift_free_module", cranelift::rt_cranelift_free_module);
    insert_simple!("rt_cranelift_fsub", cranelift::rt_cranelift_fsub);
    insert_simple!(
        "rt_cranelift_get_function_ptr",
        cranelift::rt_cranelift_get_function_ptr
    );
    insert_simple!("rt_cranelift_iadd", cranelift::rt_cranelift_iadd);
    insert_simple!("rt_cranelift_icmp", cranelift::rt_cranelift_icmp);
    insert_simple!("rt_cranelift_iconst", cranelift::rt_cranelift_iconst);
    insert_simple!("rt_cranelift_imul", cranelift::rt_cranelift_imul);
    insert_simple!("rt_cranelift_ireduce", cranelift::rt_cranelift_ireduce);
    insert_simple!("rt_cranelift_ishl", cranelift::rt_cranelift_ishl);
    insert_simple!("rt_cranelift_isub", cranelift::rt_cranelift_isub);
    insert_simple!("rt_cranelift_jump", cranelift::rt_cranelift_jump);
    insert_simple!("rt_cranelift_load", cranelift::rt_cranelift_load);
    insert_simple!("rt_cranelift_module_new", cranelift::rt_cranelift_module_new);
    insert_simple!("rt_cranelift_new_module", cranelift::rt_cranelift_new_module);
    insert_simple!("rt_cranelift_new_signature", cranelift::rt_cranelift_new_signature);
    insert_simple!("rt_cranelift_null", cranelift::rt_cranelift_null);
    insert_simple!("rt_cranelift_return", cranelift::rt_cranelift_return);
    insert_simple!("rt_cranelift_return_void", cranelift::rt_cranelift_return_void);
    insert_simple!("rt_cranelift_sdiv", cranelift::rt_cranelift_sdiv);
    insert_simple!("rt_cranelift_seal_all_blocks", cranelift::rt_cranelift_seal_all_blocks);
    insert_simple!("rt_cranelift_seal_block", cranelift::rt_cranelift_seal_block);
    insert_simple!("rt_cranelift_sextend", cranelift::rt_cranelift_sextend);
    insert_simple!("rt_cranelift_sig_add_param", cranelift::rt_cranelift_sig_add_param);
    insert_simple!("rt_cranelift_sig_set_return", cranelift::rt_cranelift_sig_set_return);
    insert_simple!("rt_cranelift_srem", cranelift::rt_cranelift_srem);
    insert_simple!("rt_cranelift_sshr", cranelift::rt_cranelift_sshr);
    insert_simple!("rt_cranelift_stack_addr", cranelift::rt_cranelift_stack_addr);
    insert_simple!("rt_cranelift_stack_slot", cranelift::rt_cranelift_stack_slot);
    insert_simple!("rt_cranelift_store", cranelift::rt_cranelift_store);
    insert_simple!("rt_cranelift_switch_to_block", cranelift::rt_cranelift_switch_to_block);
    insert_simple!("rt_cranelift_trap", cranelift::rt_cranelift_trap);
    insert_simple!("rt_cranelift_udiv", cranelift::rt_cranelift_udiv);
    insert_simple!("rt_cranelift_uextend", cranelift::rt_cranelift_uextend);
    insert_simple!("rt_cranelift_urem", cranelift::rt_cranelift_urem);
    insert_simple!("rt_cranelift_ushr", cranelift::rt_cranelift_ushr);
    insert_simple!("rt_cstring_to_text", coverage::rt_cstring_to_text);
    insert_simple!("rt_cstring_to_text", wsffi::rt_cstring_to_text);
    insert_simple!("rt_cuda_available", gpu::rt_cuda_available_fn);
    insert_simple!("rt_cuda_ctx_create", gpu::rt_cuda_ctx_create_fn);
    insert_simple!("rt_cuda_ctx_destroy", gpu::rt_cuda_ctx_destroy_fn);
    insert_simple!("rt_cuda_ctx_synchronize", gpu::rt_cuda_ctx_synchronize_fn);
    insert_simple!(
        "rt_cuda_device_compute_capability",
        gpu::rt_cuda_device_compute_capability_fn
    );
    insert_simple!("rt_cuda_device_count", gpu::rt_cuda_device_count_fn);
    insert_simple!("rt_cuda_device_get", gpu::rt_cuda_device_get_fn);
    insert_simple!("rt_cuda_device_name", gpu::rt_cuda_device_name_fn);
    insert_simple!("rt_cuda_f64_binary_op", gpu::rt_cuda_f64_binary_op_fn);
    insert_simple!("rt_cuda_f64_minmax", gpu::rt_cuda_f64_minmax_fn);
    insert_simple!("rt_cuda_f64_scalar_div", gpu::rt_cuda_f64_scalar_div_fn);
    insert_simple!("rt_cuda_f64_slice_1d", gpu::rt_cuda_f64_slice_1d_fn);
    insert_simple!("rt_cuda_f64_slice_2d", gpu::rt_cuda_f64_slice_2d_fn);
    insert_simple!("rt_cuda_f64_sum_axis", gpu::rt_cuda_f64_sum_axis_fn);
    insert_simple!("rt_cuda_f64_sum", gpu::rt_cuda_f64_sum_fn);
    insert_simple!("rt_cuda_get_error_string", gpu::rt_cuda_get_error_string_fn);
    insert_simple!("rt_cuda_init", gpu::rt_cuda_init_fn);
    insert_simple!("rt_cuda_launch_kernel", gpu::rt_cuda_launch_kernel_fn);
    insert_simple!("rt_cuda_mem_alloc", gpu::rt_cuda_mem_alloc_fn);
    insert_simple!("rt_cuda_memcpy_dtod", gpu::rt_cuda_memcpy_dtod_fn);
    insert_simple!("rt_cuda_memcpy_dtoh", gpu::rt_cuda_memcpy_dtoh_fn);
    insert_simple!("rt_cuda_memcpy_htod", gpu::rt_cuda_memcpy_htod_fn);
    insert_simple!("rt_cuda_mem_free", gpu::rt_cuda_mem_free_fn);
    insert_simple!("rt_cuda_memset", gpu::rt_cuda_memset_fn);
    insert_simple!("rt_cuda_module_get_function", gpu::rt_cuda_module_get_function_fn);
    insert_simple!("rt_cuda_module_load_data", gpu::rt_cuda_module_load_data_fn);
    insert_simple!("rt_cuda_module_load", gpu::rt_cuda_module_load_fn);
    insert_simple!("rt_cuda_module_unload", gpu::rt_cuda_module_unload_fn);
    insert_simple!("rt_cuda_sync", gpu::rt_cuda_sync_fn);
    insert_simple!("rt_metal_alloc_buffer", gpu::rt_metal_alloc_buffer_fn);
    insert_simple!("rt_metal_begin_render_pass", gpu::rt_metal_begin_render_pass_fn);
    insert_simple!("rt_metal_buffer_download", gpu::rt_metal_buffer_download_fn);
    insert_simple!("rt_metal_buffer_upload", gpu::rt_metal_buffer_upload_fn);
    insert_simple!("rt_metal_commit_command_buffer", gpu::rt_metal_commit_command_buffer_fn);
    insert_simple!("rt_metal_compile_shader", gpu::rt_metal_compile_shader_fn);
    insert_simple!("rt_metal_create_command_buffer", gpu::rt_metal_create_command_buffer_fn);
    insert_simple!("rt_metal_create_command_queue", gpu::rt_metal_create_command_queue_fn);
    insert_simple!(
        "rt_metal_create_compute_encoder",
        gpu::rt_metal_create_compute_encoder_fn
    );
    insert_simple!(
        "rt_metal_create_compute_pipeline",
        gpu::rt_metal_create_compute_pipeline_fn
    );
    insert_simple!("rt_metal_create_device", gpu::rt_metal_create_device_fn);
    insert_simple!(
        "rt_metal_create_render_pipeline",
        gpu::rt_metal_create_render_pipeline_fn
    );
    insert_simple!("rt_metal_create_sampler", gpu::rt_metal_create_sampler_fn);
    insert_simple!("rt_metal_create_swapchain", gpu::rt_metal_create_swapchain_fn);
    insert_simple!("rt_metal_create_texture", gpu::rt_metal_create_texture_fn);
    insert_simple!("rt_metal_destroy_command_queue", gpu::rt_metal_destroy_command_queue_fn);
    insert_simple!("rt_metal_destroy_device", gpu::rt_metal_destroy_device_fn);
    insert_simple!("rt_metal_destroy_pipeline", gpu::rt_metal_destroy_pipeline_fn);
    insert_simple!(
        "rt_metal_destroy_render_pipeline",
        gpu::rt_metal_destroy_render_pipeline_fn
    );
    insert_simple!("rt_metal_destroy_sampler", gpu::rt_metal_destroy_sampler_fn);
    insert_simple!("rt_metal_destroy_shader", gpu::rt_metal_destroy_shader_fn);
    insert_simple!("rt_metal_destroy_swapchain", gpu::rt_metal_destroy_swapchain_fn);
    insert_simple!("rt_metal_device_count", gpu::rt_metal_device_count_fn);
    insert_simple!("rt_metal_device_memory", gpu::rt_metal_device_memory_fn);
    insert_simple!("rt_metal_device_name", gpu::rt_metal_device_name_fn);
    insert_simple!("rt_metal_dispatch_compute", gpu::rt_metal_dispatch_compute_fn);
    insert_simple!("rt_metal_draw_indexed", gpu::rt_metal_draw_indexed_fn);
    insert_simple!("rt_metal_draw_primitives", gpu::rt_metal_draw_primitives_fn);
    insert_simple!("rt_metal_end_compute_encoder", gpu::rt_metal_end_compute_encoder_fn);
    insert_simple!("rt_metal_end_render_pass", gpu::rt_metal_end_render_pass_fn);
    insert_simple!("rt_metal_free_buffer", gpu::rt_metal_free_buffer_fn);
    insert_simple!("rt_metal_free_texture", gpu::rt_metal_free_texture_fn);
    insert_simple!("rt_metal_get_last_error", gpu::rt_metal_get_last_error_fn);
    insert_simple!("rt_metal_init", gpu::rt_metal_init_fn);
    insert_simple!("rt_metal_is_available", gpu::rt_metal_is_available_fn);
    insert_simple!("rt_metal_present", gpu::rt_metal_present_fn);
    insert_simple!("rt_metal_run_blit_frame", gpu::rt_metal_run_blit_frame_fn);
    insert_simple!("rt_metal_run_compute_frame", gpu::rt_metal_run_compute_frame_fn);
    insert_simple!("rt_metal_set_buffer", gpu::rt_metal_set_buffer_fn);
    insert_simple!("rt_metal_set_bytes", gpu::rt_metal_set_bytes_fn);
    insert_simple!("rt_metal_set_scissor", gpu::rt_metal_set_scissor_fn);
    insert_simple!("rt_metal_set_viewport", gpu::rt_metal_set_viewport_fn);
    insert_simple!("rt_metal_wait_completed", gpu::rt_metal_wait_completed_fn);
    insert_simple!("rt_current_dir", file_io::rt_current_dir);
    insert_simple!("rt_current_time_ms", time::rt_current_time_ms);
    insert_simple!("rt_db_accel_bitmap_and_words", simd::rt_db_accel_bitmap_and_words);
    insert_simple!("rt_db_accel_bitmap_or_words", simd::rt_db_accel_bitmap_or_words);
    insert_simple!("rt_db_col_count", sffi_db::rt_db_col_count_fn);
    insert_simple!("rt_db_delete", sffi_db::rt_db_delete_fn);
    insert_simple!("rt_db_get", sffi_db::rt_db_get_fn);
    insert_simple!("rt_db_get_int", sffi_db::rt_db_get_int_fn);
    insert_simple!("rt_db_get_text", sffi_db::rt_db_get_text_fn);
    insert_simple!("rt_db_put", sffi_db::rt_db_put_fn);
    insert_simple!("rt_db_put_value_int", sffi_db::rt_db_put_value_int_fn);
    insert_simple!("rt_db_put_value_text", sffi_db::rt_db_put_value_text_fn);
    insert_simple!("rt_db_row_count", sffi_db::rt_db_row_count_fn);
    insert_simple!("rt_db_scan_range", sffi_db::rt_db_scan_range_fn);
    insert_simple!("rt_db_scan_result", sffi_db::rt_db_scan_result_fn);
    insert_simple!("rt_db_table_create", sffi_db::rt_db_table_create_fn);
    insert_simple!("rt_db_table_destroy", sffi_db::rt_db_table_destroy_fn);
    insert_simple!("rt_db_put_row3", sffi_db::rt_db_put_row3_fn);
    insert_simple!("rt_db_get_int_by_pk", sffi_db::rt_db_get_int_by_pk_fn);
    insert_simple!("rt_db_update_int", sffi_db::rt_db_update_int_fn);
    insert_simple!("rt_db_update_text", sffi_db::rt_db_update_text_fn);
    insert_simple!("rt_db_iput3", sffi_db::rt_db_iput3_fn);
    insert_simple!("rt_db_iget_int", sffi_db::rt_db_iget_int_fn);
    insert_simple!("rt_db_iupdate_int", sffi_db::rt_db_iupdate_int_fn);
    insert_simple!("rt_db_idelete", sffi_db::rt_db_idelete_fn);
    insert_simple!("rt_diagram_clear", diagram::rt_diagram_clear);
    insert_simple!("rt_diagram_disable", diagram::rt_diagram_disable);
    insert_simple!("rt_diagram_enable", diagram::rt_diagram_enable);
    insert_simple!("rt_diagram_free_string", diagram::rt_diagram_free_string);
    insert_simple!("rt_diagram_generate_arch", diagram::rt_diagram_generate_arch);
    insert_simple!("rt_diagram_generate_class", diagram::rt_diagram_generate_class);
    insert_simple!("rt_diagram_generate_sequence", diagram::rt_diagram_generate_sequence);
    insert_simple!("rt_diagram_is_enabled", diagram::rt_diagram_is_enabled);
    insert_simple!("rt_diagram_mark_architectural", diagram::rt_diagram_mark_architectural);
    insert_simple!("rt_diagram_trace_method", diagram::rt_diagram_trace_method);
    insert_simple!(
        "rt_diagram_trace_method_with_args",
        diagram::rt_diagram_trace_method_with_args
    );
    insert_simple!("rt_diagram_trace_return", diagram::rt_diagram_trace_return);
    insert_simple!("rt_dict_clear", sffi_dict::rt_dict_clear_fn);
    insert_simple!("rt_dict_get", sffi_dict::rt_dict_get_fn);
    insert_simple!("rt_dict_keys", sffi_dict::rt_dict_keys_fn);
    insert_simple!("rt_dict_len", sffi_dict::rt_dict_len_fn);
    insert_simple!("rt_dict_new", sffi_dict::rt_dict_new_fn);
    insert_simple!("rt_dict_set", sffi_dict::rt_dict_set_fn);
    insert_simple!("rt_dict_values", sffi_dict::rt_dict_values_fn);
    insert_simple!("rt_dir_create_all", file_io::rt_dir_create_all);
    insert_simple!("rt_dir_create", file_io::rt_dir_create);
    insert_simple!("rt_dir_exists", file_io::rt_dir_exists);
    insert_simple!("rt_dir_glob", file_io::rt_dir_glob);
    insert_simple!("rt_dir_list", file_io::rt_dir_list);
    insert_simple!("rt_dir_remove_all", file_io::rt_dir_remove_all);
    insert_simple!("rt_dir_remove", file_io::rt_dir_remove);
    insert_simple!("rt_dir_walk", file_io::rt_dir_walk);
    insert_simple!("rt_dns_lookup", interpreter_native_net::rt_dns_lookup_interp);
    insert_simple!(
        "rt_dyn_torch_tensor_from_bits_1d",
        torch::rt_dyn_torch_tensor_from_bits_1d
    );
    insert_simple!("rt_ecdsa_p256_sign", signatures::rt_ecdsa_p256_sign);
    insert_simple!("rt_ecdsa_p256_verify", signatures::rt_ecdsa_p256_verify);
    insert_simple!("rt_ed25519_sign", signatures::rt_ed25519_sign);
    insert_simple!("rt_ed25519_verify", signatures::rt_ed25519_verify);
    insert_simple!("rt_entropy_hardware_ready", random::rt_entropy_hardware_ready_fn);
    insert_simple!("rt_env_all", system::rt_env_all);
    insert_simple!("rt_env_cwd", system::rt_env_cwd);
    insert_simple!("rt_env_define_var", env_sffi::rt_env_define);
    insert_simple!("rt_env_exists", system::rt_env_exists);
    insert_simple!("rt_env_free_handle", env_sffi::rt_env_free_handle);
    insert_simple!("rt_env_get_i64", system::rt_env_get_i64);
    insert_simple!("rt_env_get", system::rt_env_get);
    insert_simple!("rt_env_get_var", env_sffi::rt_env_get_var);
    insert_simple!("rt_env_has_var", env_sffi::rt_env_has_var);
    insert_simple!("rt_env_home", system::rt_env_home);
    insert_simple!("rt_env_new_handle", env_sffi::rt_env_new);
    insert_simple!("rt_env_pop_scope", env_sffi::rt_env_pop_scope);
    insert_simple!("rt_env_push_scope", env_sffi::rt_env_push_scope);
    insert_simple!("rt_env_remove", system::rt_env_remove);
    insert_simple!("rt_env_scope_depth", env_sffi::rt_env_scope_depth);
    insert_simple!("rt_env_set", system::rt_env_set);
    insert_simple!("rt_env_set_var", env_sffi::rt_env_set_var);
    insert_simple!("rt_env_snapshot", env_sffi::rt_env_snapshot);
    insert_simple!("rt_env_temp", system::rt_env_temp);
    insert_simple!("rt_env_var_count", env_sffi::rt_env_var_count);
    insert_simple!("rt_env_var_names", env_sffi::rt_env_var_names);
    insert_simple!(
        "rt_event_loop_close",
        interpreter_event_loop::rt_event_loop_close_interp
    );
    insert_simple!(
        "rt_event_loop_create",
        interpreter_event_loop::rt_event_loop_create_interp
    );
    insert_simple!(
        "rt_event_loop_deregister",
        interpreter_event_loop::rt_event_loop_deregister_interp
    );
    insert_simple!("rt_event_loop_poll", interpreter_event_loop::rt_event_loop_poll_interp);
    insert_simple!(
        "rt_event_loop_register",
        interpreter_event_loop::rt_event_loop_register_interp
    );
    // Per-backend event loop externs for cross-platform PlatformEvent dispatch
    insert_simple!("rt_kqueue_create", interpreter_event_loop::rt_kqueue_create_interp);
    insert_simple!("rt_kqueue_register", interpreter_event_loop::rt_kqueue_register_interp);
    insert_simple!(
        "rt_kqueue_deregister",
        interpreter_event_loop::rt_kqueue_deregister_interp
    );
    insert_simple!("rt_kqueue_poll", interpreter_event_loop::rt_kqueue_poll_interp);
    insert_simple!("rt_kqueue_close", interpreter_event_loop::rt_kqueue_close_interp);
    insert_simple!("rt_iocp_create", interpreter_event_loop::rt_iocp_create_interp);
    insert_simple!("rt_iocp_register", interpreter_event_loop::rt_iocp_register_interp);
    insert_simple!("rt_iocp_deregister", interpreter_event_loop::rt_iocp_deregister_interp);
    insert_simple!("rt_iocp_poll", interpreter_event_loop::rt_iocp_poll_interp);
    insert_simple!("rt_iocp_close", interpreter_event_loop::rt_iocp_close_interp);
    insert_simple!(
        "rt_event_ports_create",
        interpreter_event_loop::rt_event_ports_create_interp
    );
    insert_simple!(
        "rt_event_ports_register",
        interpreter_event_loop::rt_event_ports_register_interp
    );
    insert_simple!(
        "rt_event_ports_deregister",
        interpreter_event_loop::rt_event_ports_deregister_interp
    );
    insert_simple!(
        "rt_event_ports_poll",
        interpreter_event_loop::rt_event_ports_poll_interp
    );
    insert_simple!(
        "rt_event_ports_close",
        interpreter_event_loop::rt_event_ports_close_interp
    );
    insert_simple!("rt_error_arg_count", error_sffi::rt_error_arg_count);
    insert_simple!("rt_error_division_by_zero", error_sffi::rt_error_division_by_zero);
    insert_simple!("rt_error_free", error_sffi::rt_error_free);
    insert_simple!("rt_error_index_oob", error_sffi::rt_error_index_oob);
    insert_simple!("rt_error_message", error_sffi::rt_error_message);
    insert_simple!("rt_error_semantic", error_sffi::rt_error_semantic);
    insert_simple!("rt_error_throw", error_sffi::rt_error_throw);
    insert_simple!("rt_error_type_mismatch", error_sffi::rt_error_type_mismatch);
    insert_simple!("rt_error_undefined_var", error_sffi::rt_error_undefined_var);
    insert_simple!("rt_exec", cranelift::rt_exec);
    insert_simple!("rt_execute_native", native_sffi::rt_execute_native);
    insert_simple!("rt_exit", system::rt_exit);
    insert_simple!("rt_fault_set_execution_limit", cli::rt_fault_set_execution_limit);
    insert_simple!(
        "rt_fault_set_max_recursion_depth",
        cli::rt_fault_set_max_recursion_depth
    );
    insert_simple!(
        "rt_fault_set_stack_overflow_detection",
        cli::rt_fault_set_stack_overflow_detection
    );
    insert_simple!("rt_fault_set_timeout", cli::rt_fault_set_timeout);
    insert_simple!("rt_fd_close", qmp_socket::rt_fd_close);
    insert_simple!("rt_fd_read_until", qmp_socket::rt_fd_read_until);
    insert_simple!("rt_fd_write", qmp_socket::rt_fd_write);
    insert_simple!("rt_file_append_text", file_io::rt_file_append_text);
    insert_simple!("rt_file_atomic_write", file_io::rt_file_atomic_write);
    insert_simple!("rt_file_canonicalize", file_io::rt_file_canonicalize);
    insert_simple!("rt_file_close", file_io::rt_file_close);
    insert_simple!("rt_file_copy", file_io::rt_file_copy);
    insert_simple!("rt_crc32_text", file_io::rt_crc32_text);
    insert_simple!("rt_file_create_excl", file_io::rt_file_create_excl);
    insert_simple!("rt_file_delete", native_sffi::rt_file_delete);
    insert_simple!("rt_file_exists", file_io::rt_file_exists);
    insert_simple!("rt_file_exists_str", file_io::rt_file_exists);
    insert_simple!("rt_file_find", file_io::rt_file_find);
    insert_simple!("rt_file_fsync_cached", file_io::rt_file_fsync_cached);
    insert_simple!("rt_file_fsync", file_io::rt_file_fsync);
    insert_simple!("rt_file_sync", file_io::rt_file_fsync);
    insert_simple!("rt_file_get_size", file_io::rt_file_get_size);
    insert_simple!("rt_file_hash", cranelift::rt_file_hash);
    insert_simple!("rt_file_hash_sha256", file_io::rt_file_hash_sha256);
    insert_simple!("rt_file_is_dir", file_io::rt_file_is_dir);
    insert_simple!("rt_file_list_dir", file_io::rt_dir_list);
    insert_simple!("rt_file_lock", file_io::rt_file_lock);
    insert_simple!("rt_file_mmap_read_bytes", file_io::rt_file_mmap_read_bytes);
    insert_simple!("rt_file_mmap_read_text", file_io::rt_file_mmap_read_text);
    insert_simple!("rt_file_move", file_io::rt_file_move);
    insert_simple!("rt_file_open", file_io::rt_file_open);
    insert_simple!("rt_file_read_bytes", file_io::rt_file_read_bytes);
    insert_simple!("rt_file_read_lines", file_io::rt_file_read_lines);
    insert_simple!("rt_file_read_text", file_io::rt_file_read_text);
    insert_simple!("rt_file_read_text_at", file_io::rt_file_read_text_at);
    insert_simple!("rt_file_remove", file_io::rt_file_remove);
    insert_simple!("rt_file_rename", file_io::rt_file_rename);
    insert_simple!("rt_file_size", file_io::rt_file_size);
    insert_simple!("rt_file_stat", file_io::rt_file_stat);
    insert_simple!("rt_file_stat_free", file_io::rt_file_stat_free);
    insert_simple!("rt_file_stat_is_dir", file_io::rt_file_stat_is_dir);
    insert_simple!("rt_file_stat_is_file", file_io::rt_file_stat_is_file);
    insert_simple!("rt_file_stat_mtime", file_io::rt_file_stat_mtime);
    insert_simple!("rt_file_stat_size", file_io::rt_file_stat_size);
    insert_simple!("rt_file_truncate", file_io::rt_file_truncate);
    insert_simple!("rt_file_unlock", file_io::rt_file_unlock);
    insert_simple!("rt_file_write_bytes", file_io::rt_file_write_bytes);
    insert_simple!("rt_file_write_text_at", file_io::rt_file_write_text_at);
    insert_simple!("rt_file_write_text", file_io::rt_file_write_text);
    insert_simple!("rt_free", memory::rt_free);
    insert_simple!("rt_function_not_found", sffi_value::rt_function_not_found_fn);
    insert_simple!("rt_get_concurrent_backend", concurrency::rt_get_concurrent_backend);
    insert_simple!("rt_get_cwd", file_io::rt_get_cwd);
    insert_simple!("rt_getpid", file_io::rt_getpid);
    insert_simple!("rt_gui_get_glyph_8x16", conversion::rt_gui_get_glyph_8x16_fn);
    insert_simple!("__rt_hashmap_clear", collections::__rt_hashmap_clear);
    insert_simple!("__rt_hashmap_contains_key", collections::__rt_hashmap_contains_key);
    insert_simple!("__rt_hashmap_entries", collections::__rt_hashmap_entries);
    insert_simple!("__rt_hashmap_get", collections::__rt_hashmap_get);
    insert_simple!("__rt_hashmap_insert", collections::__rt_hashmap_insert);
    insert_simple!("__rt_hashmap_keys", collections::__rt_hashmap_keys);
    insert_simple!("__rt_hashmap_len", collections::__rt_hashmap_len);
    insert_simple!("__rt_hashmap_new", collections::__rt_hashmap_new);
    insert_simple!("__rt_hashmap_remove", collections::__rt_hashmap_remove);
    insert_simple!("__rt_hashmap_values", collections::__rt_hashmap_values);
    insert_simple!("__rt_hashset_clear", collections::__rt_hashset_clear);
    insert_simple!("__rt_hashset_contains", collections::__rt_hashset_contains);
    insert_simple!("__rt_hashset_difference", collections::__rt_hashset_difference);
    insert_simple!("__rt_hashset_insert", collections::__rt_hashset_insert);
    insert_simple!("__rt_hashset_intersection", collections::__rt_hashset_intersection);
    insert_simple!("__rt_hashset_is_subset", collections::__rt_hashset_is_subset);
    insert_simple!("__rt_hashset_is_superset", collections::__rt_hashset_is_superset);
    insert_simple!("__rt_hashset_len", collections::__rt_hashset_len);
    insert_simple!("__rt_hashset_new", collections::__rt_hashset_new);
    insert_simple!("__rt_hashset_remove", collections::__rt_hashset_remove);
    insert_simple!(
        "__rt_hashset_symmetric_difference",
        collections::__rt_hashset_symmetric_difference
    );
    insert_simple!("__rt_hashset_to_array", collections::__rt_hashset_to_array);
    insert_simple!("__rt_hashset_union", collections::__rt_hashset_union);
    insert_simple!("rt_hash_text", conversion::rt_hash_text);
    insert_simple!("rt_hosted_select_surface", hosted::select_surface);
    insert_simple!("rt_hosted_set_surface_override", hosted::set_surface_override);
    insert_simple!("rt_hostname", file_io::rt_hostname);
    insert_simple!("rt_host_wm_client_connect", host_wm_bridge::rt_host_wm_client_connect);
    insert_simple!(
        "rt_host_wm_client_poll_event",
        host_wm_bridge::rt_host_wm_client_poll_event
    );
    insert_simple!("rt_host_wm_client_request", host_wm_bridge::rt_host_wm_client_request);
    insert_simple!("rt_host_wm_server_cleanup", host_wm_bridge::rt_host_wm_server_cleanup);
    insert_simple!("rt_host_wm_server_poll", host_wm_bridge::rt_host_wm_server_poll);
    insert_simple!(
        "rt_host_wm_server_reply_create",
        host_wm_bridge::rt_host_wm_server_reply_create
    );
    insert_simple!(
        "rt_host_wm_server_reply_status",
        host_wm_bridge::rt_host_wm_server_reply_status
    );
    insert_simple!(
        "rt_host_wm_server_send_event",
        host_wm_bridge::rt_host_wm_server_send_event
    );
    insert_simple!("rt_host_wm_server_start", host_wm_bridge::rt_host_wm_server_start);
    insert_simple!("rt_http_get", network::rt_http_get);
    insert_simple!("rt_io_tcp_accept", interpreter_native_net::rt_io_tcp_accept_interp);
    insert_simple!(
        "rt_io_tcp_accept_timeout",
        interpreter_native_net::rt_io_tcp_accept_timeout_interp
    );
    insert_simple!("rt_io_tcp_bind", interpreter_native_net::rt_io_tcp_bind_interp);
    insert_simple!("rt_io_tcp_close", interpreter_native_net::rt_io_tcp_close_interp);
    insert_simple!("rt_io_tcp_connect", interpreter_native_net::rt_io_tcp_connect_interp);
    insert_simple!(
        "rt_io_tcp_connect_timeout",
        interpreter_native_net::rt_io_tcp_connect_timeout_interp
    );
    insert_simple!(
        "rt_io_tcp_drain_line",
        interpreter_native_net::rt_io_tcp_drain_line_interp
    );
    insert_simple!("rt_io_tcp_flush", interpreter_native_net::rt_io_tcp_flush_interp);
    insert_simple!(
        "rt_io_tcp_local_addr",
        interpreter_native_net::rt_io_tcp_local_addr_interp
    );
    insert_simple!(
        "rt_io_tcp_peer_addr",
        interpreter_native_net::rt_io_tcp_peer_addr_interp
    );
    insert_simple!(
        "rt_io_tcp_read_exact",
        interpreter_native_net::rt_io_tcp_read_exact_interp
    );
    insert_simple!(
        "rt_io_tcp_read_exact_len",
        interpreter_native_net::rt_io_tcp_read_exact_len_interp
    );
    insert_simple!("rt_io_tcp_read", interpreter_native_net::rt_io_tcp_read_interp);
    insert_simple!(
        "rt_io_tcp_read_line",
        interpreter_native_net::rt_io_tcp_read_line_interp
    );
    insert_simple!(
        "rt_io_tcp_set_nodelay",
        interpreter_native_net::rt_io_tcp_set_nodelay_interp
    );
    insert_simple!(
        "rt_io_tcp_set_nonblocking",
        interpreter_native_net::rt_io_tcp_set_nonblocking_interp
    );
    insert_simple!(
        "rt_io_tcp_socket_create",
        interpreter_native_net::rt_io_tcp_socket_create_interp
    );
    insert_simple!("rt_io_tcp_bind_fd", interpreter_native_net::rt_io_tcp_bind_fd_interp);
    insert_simple!("rt_io_tcp_listen", interpreter_native_net::rt_io_tcp_listen_interp);
    insert_simple!(
        "rt_io_tcp_set_reuseport",
        interpreter_native_net::rt_io_tcp_set_reuseport_interp
    );
    insert_simple!(
        "rt_io_tcp_set_reuseaddr",
        interpreter_native_net::rt_io_tcp_set_reuseaddr_interp
    );
    insert_simple!(
        "rt_io_tcp_set_read_timeout",
        interpreter_native_net::rt_io_tcp_set_read_timeout_interp
    );
    insert_simple!(
        "rt_io_tcp_set_write_timeout",
        interpreter_native_net::rt_io_tcp_set_write_timeout_interp
    );
    insert_simple!("rt_io_tcp_shutdown", interpreter_native_net::rt_io_tcp_shutdown_interp);
    insert_simple!(
        "rt_io_tcp_write_all",
        interpreter_native_net::rt_io_tcp_write_all_interp
    );
    insert_simple!(
        "rt_io_tcp_write_http",
        interpreter_native_net::rt_io_tcp_write_http_interp
    );
    insert_simple!("rt_io_tcp_write", interpreter_native_net::rt_io_tcp_write_interp);
    insert_simple!("rt_io_tcp_write_bytes", interpreter_native_net::rt_io_tcp_write_interp);
    insert_simple!(
        "rt_io_tcp_write_text",
        interpreter_native_net::rt_io_tcp_write_text_interp
    );
    insert_simple!(
        "rt_io_tcp_write_text_read_exact_len",
        interpreter_native_net::rt_io_tcp_write_text_read_exact_len_interp
    );
    insert_simple!("rt_is_debug_mode_enabled", system::rt_is_debug_mode_enabled);
    insert_simple!("rt_is_error", sffi_value::rt_is_error_fn);
    insert_simple!("rt_is_macro_trace_enabled", system::rt_is_macro_trace_enabled);
    insert_simple!("rt_jit_backend_name", jit_native::rt_jit_backend_name);
    insert_simple!("rt_jit_call_i64_i64", jit_native::rt_jit_call_i64_i64);
    insert_simple!("rt_jit_call_i64", jit_native::rt_jit_call_i64);
    insert_simple!("rt_jit_call_void", jit_native::rt_jit_call_void);
    insert_simple!("rt_jit_cleanup", jit_native::rt_jit_cleanup);
    insert_simple!("rt_jit_compile_source", jit_native::rt_jit_compile_source);
    insert_simple!("rt_jit_create", jit_native::rt_jit_create);
    insert_simple!("rt_jit_create_for_target", jit_native::rt_jit_create_for_target);
    insert_simple!("rt_jit_has_function", jit_native::rt_jit_has_function);
    insert_simple!("rt_math_acos", math::rt_math_acos_fn);
    insert_simple!("rt_math_asin", math::rt_math_asin_fn);
    insert_simple!("rt_math_atan2", math::rt_math_atan2_fn);
    insert_simple!("rt_math_atan", math::rt_math_atan_fn);
    insert_simple!("rt_math_cbrt", math::rt_math_cbrt_fn);
    insert_simple!("rt_math_ceil", math::rt_math_ceil_fn);
    insert_simple!("rt_math_cosh", math::rt_math_cosh_fn);
    insert_simple!("rt_math_cos", math::rt_math_cos_fn);
    insert_simple!("rt_math_exp", math::rt_math_exp_fn);
    insert_simple!("rt_math_floor", math::rt_math_floor_fn);
    insert_simple!("rt_math_inf", math::rt_math_inf_fn);
    insert_simple!("rt_math_is_finite", math::rt_math_is_finite_fn);
    insert_simple!("rt_math_is_inf", math::rt_math_is_inf_fn);
    insert_simple!("rt_math_is_nan", math::rt_math_is_nan_fn);
    insert_simple!("rt_math_log10", math::rt_math_log10_fn);
    insert_simple!("rt_math_log2", math::rt_math_log2_fn);
    insert_simple!("rt_math_log", math::rt_math_log_fn);
    insert_simple!("rt_math_nan", math::rt_math_nan_fn);
    insert_simple!("rt_math_pow", math::rt_math_pow_fn);
    insert_simple!("rt_math_sinh", math::rt_math_sinh_fn);
    insert_simple!("rt_math_sin", math::rt_math_sin_fn);
    insert_simple!("rt_math_sqrt", math::rt_math_sqrt_fn);
    insert_simple!("rt_math_tanh", math::rt_math_tanh_fn);
    insert_simple!("rt_math_tan", math::rt_math_tan_fn);
    insert_simple!("rt_memcpy", memory::rt_memcpy);
    insert_simple!("rt_memset", memory::rt_memset);
    insert_simple!("rt_method_not_found", sffi_value::rt_method_not_found_fn);
    insert_simple!("rt_mkdir", file_io::rt_mkdir);
    insert_simple!("rt_mkdir_p", file_io::rt_dir_create_all);
    insert_simple!("rt_mutex_lock", atomic::rt_mutex_lock_fn);
    insert_simple!("rt_mutex_new", atomic::rt_mutex_new_fn);
    insert_simple!("rt_mutex_try_lock", atomic::rt_mutex_try_lock_fn);
    insert_simple!("rt_mutex_unlock", atomic::rt_mutex_unlock_fn);
    insert_simple!("rt_native_build", cli::rt_native_build);
    insert_simple!("rt_package_chmod", package::chmod);
    insert_simple!("rt_package_copy_file", package::copy_file);
    insert_simple!("rt_package_create_symlink", package::create_symlink);
    insert_simple!("rt_package_create_tarball", package::create_tarball);
    insert_simple!("rt_package_exists", package::exists);
    insert_simple!("rt_package_extract_tarball", package::extract_tarball);
    insert_simple!("rt_package_file_size", package::file_size);
    insert_simple!("rt_package_is_dir", package::is_dir);
    insert_simple!("rt_package_mkdir_all", package::mkdir_all);
    insert_simple!("rt_package_remove_dir_all", package::remove_dir_all);
    insert_simple!("rt_package_sha256", package::sha256);
    insert_simple!("rt_path_absolute", file_io::rt_path_absolute);
    insert_simple!("rt_path_basename", file_io::rt_path_basename);
    insert_simple!("rt_path_dirname", file_io::rt_path_dirname);
    insert_simple!("rt_path_ext", file_io::rt_path_ext);
    insert_simple!("rt_path_join", file_io::rt_path_join);
    insert_simple!("rt_path_relative", file_io::rt_path_relative);
    insert_simple!("rt_path_separator", file_io::rt_path_separator);
    insert_simple!("rt_path_stem", file_io::rt_path_stem);
    insert_simple!("rt_platform_name", system::rt_platform_name);
    insert_simple!("rt_process_execute", system::rt_process_execute);
    insert_simple!("rt_process_exists", file_io::rt_process_exists);
    insert_simple!("rt_process_is_running", system::rt_process_is_running);
    insert_simple!("rt_process_kill", system::rt_process_kill);
    insert_simple!("rt_process_run", system::rt_process_run);
    insert_simple!("rt_process_run_timeout", system::rt_process_run_timeout);
    insert_simple!("rt_process_spawn_async", system::rt_process_spawn_async);
    insert_simple!("rt_process_wait", system::rt_process_wait);
    insert_simple!("rt_profiler_is_active", time::rt_profiler_is_active_fn);
    insert_simple!("rt_profiler_record_call", time::rt_profiler_record_call_fn);
    insert_simple!("rt_profiler_record_return", time::rt_profiler_record_return_fn);
    insert_simple!("rt_progress_get_elapsed_seconds", time::rt_progress_get_elapsed_seconds);
    insert_simple!("rt_progress_init", time::rt_progress_init);
    insert_simple!("rt_progress_reset", time::rt_progress_reset);
    insert_simple!(
        "rt_ps_torch_tensor_from_bits_1d",
        torch::rt_ps_torch_tensor_from_bits_1d
    );
    insert_simple!("rt_ps_torch_tensor_from_data", torch::rt_ps_torch_tensor_from_data);
    insert_simple!("rt_ps_torch_tensor", torch::rt_ps_torch_tensor);
    insert_simple!("rt_ps_torch_tensor_zeros", torch::rt_ps_torch_tensor_zeros);
    insert_simple!("rt_ptr_read_i32", memory::rt_ptr_read_i32);
    insert_simple!("rt_ptr_read_i64", memory::rt_ptr_read_i64);
    insert_simple!("rt_ptr_write_i32", memory::rt_ptr_write_i32);
    insert_simple!("rt_ptr_write_i64", memory::rt_ptr_write_i64);
    insert_simple!("rt_ptr_write_u8", memory::rt_ptr_write_u8);
    insert_simple!("rt_random_getstate", random::rt_random_getstate_fn);
    insert_simple!("rt_random_hex", random::rt_random_hex_fn);
    insert_simple!("rt_random_i64", random::rt_random_i64_fn);
    insert_simple!("rt_random_next", random::rt_random_next_fn);
    insert_simple!("rt_random_randint", random::rt_random_randint_fn);
    insert_simple!("rt_random_random", random::rt_random_random_fn);
    insert_simple!("rt_random_seed", random::rt_random_seed_fn);
    insert_simple!("rt_random_setstate", random::rt_random_setstate_fn);
    insert_simple!("rt_random_uniform", random::rt_random_uniform_fn);
    insert_simple!("rt_rank_query", simd::rt_rank_query);
    insert_simple!("rt_rank_select_build", simd::rt_rank_select_build);
    insert_simple!("rt_rank_select_free", simd::rt_rank_select_free);
    insert_simple!("rt_readdir_count", file_io::rt_readdir_count);
    insert_simple!("rt_readdir_entry", file_io::rt_readdir_entry);
    insert_simple!("rt_readdir", file_io::rt_readdir);
    insert_simple!("rt_readdir_free", file_io::rt_readdir_free);
    insert_simple!("rt_remove", file_io::rt_remove);
    insert_simple!("rt_rsa_pss_sha256_verify", signatures::rt_rsa_pss_sha256_verify);
    insert_simple!("rt_rsa_pss_sha384_verify", signatures::rt_rsa_pss_sha384_verify);
    insert_simple!("rt_rsa_pss_sha512_verify", signatures::rt_rsa_pss_sha512_verify);
    insert_simple!("rt_rsa_sha256_sign", signatures::rt_rsa_sha256_sign);
    insert_simple!("rt_rsa_sha256_verify", signatures::rt_rsa_sha256_verify);
    insert_simple!("rt_rsa_sha512_sign", signatures::rt_rsa_sha512_sign);
    insert_simple!("rt_rsa_sha512_verify", signatures::rt_rsa_sha512_verify);
    insert_simple!("rt_rwlock_new", atomic::rt_rwlock_new_fn);
    insert_simple!("rt_rwlock_read", atomic::rt_rwlock_read_fn);
    insert_simple!("rt_rwlock_set", atomic::rt_rwlock_set_fn);
    insert_simple!("rt_rwlock_try_read", atomic::rt_rwlock_try_read_fn);
    insert_simple!("rt_rwlock_try_write", atomic::rt_rwlock_try_write_fn);
    insert_simple!("rt_rwlock_write", atomic::rt_rwlock_write_fn);
    insert_simple!(
        "rt_sandbox_add_allowed_domain",
        sandbox::rt_sandbox_add_allowed_domain_fn
    );
    insert_simple!(
        "rt_sandbox_add_blocked_domain",
        sandbox::rt_sandbox_add_blocked_domain_fn
    );
    insert_simple!("rt_sandbox_add_read_path", sandbox::rt_sandbox_add_read_path_fn);
    insert_simple!("rt_sandbox_add_write_path", sandbox::rt_sandbox_add_write_path_fn);
    insert_simple!("rt_sandbox_apply", sandbox::rt_sandbox_apply_fn);
    insert_simple!("rt_sandbox_cleanup", sandbox::rt_sandbox_cleanup_fn);
    insert_simple!("rt_sandbox_disable_network", sandbox::rt_sandbox_disable_network_fn);
    insert_simple!("rt_sandbox_get_cpu_time", sandbox::rt_sandbox_get_cpu_time_fn);
    insert_simple!("rt_sandbox_get_fs_mode", sandbox::rt_sandbox_get_fs_mode_fn);
    insert_simple!("rt_sandbox_get_memory", sandbox::rt_sandbox_get_memory_fn);
    insert_simple!("rt_sandbox_get_network_mode", sandbox::rt_sandbox_get_network_mode_fn);
    insert_simple!("rt_sandbox_is_configured", sandbox::rt_sandbox_is_configured_fn);
    insert_simple!("rt_sandbox_reset", sandbox::rt_sandbox_reset_fn);
    insert_simple!("rt_sandbox_set_cpu_time", sandbox::rt_sandbox_set_cpu_time_fn);
    insert_simple!("rt_sandbox_set_fd_limit", sandbox::rt_sandbox_set_fd_limit_fn);
    insert_simple!("rt_sandbox_set_fs_overlay", sandbox::rt_sandbox_set_fs_overlay_fn);
    insert_simple!("rt_sandbox_set_fs_readonly", sandbox::rt_sandbox_set_fs_readonly_fn);
    insert_simple!("rt_sandbox_set_fs_restricted", sandbox::rt_sandbox_set_fs_restricted_fn);
    insert_simple!("rt_sandbox_set_memory", sandbox::rt_sandbox_set_memory_fn);
    insert_simple!(
        "rt_sandbox_set_network_allowlist",
        sandbox::rt_sandbox_set_network_allowlist_fn
    );
    insert_simple!(
        "rt_sandbox_set_network_blocklist",
        sandbox::rt_sandbox_set_network_blocklist_fn
    );
    insert_simple!("rt_sandbox_set_thread_limit", sandbox::rt_sandbox_set_thread_limit_fn);
    insert_simple!("rt_sdn_check", sdn::rt_sdn_check);
    insert_simple!("rt_sdn_fmt", sdn::rt_sdn_fmt);
    insert_simple!("rt_sdn_from_json", sdn::rt_sdn_from_json);
    insert_simple!("rt_sdn_get", sdn::rt_sdn_get);
    insert_simple!("rt_sdn_set", sdn::rt_sdn_set);
    insert_simple!("rt_sdn_to_json", sdn::rt_sdn_to_json);
    insert_simple!("rt_sdn_version", sdn::rt_sdn_version);
    insert_simple!("rt_select_query", simd::rt_select_query);
    insert_simple!("rt_set_concurrent_backend", concurrency::rt_set_concurrent_backend);
    insert_simple!("rt_set_current_dir", file_io::rt_set_current_dir);
    insert_simple!("rt_set_debug_mode", system::rt_set_debug_mode);
    insert_simple!("rt_set_macro_trace", system::rt_set_macro_trace);
    insert_simple!("rt_settlement_main", cli::rt_settlement_main);
    insert_simple!("rt_sha1", crypto::rt_sha1);
    insert_simple!("rt_sha1_finish_base64", crypto::rt_sha1_finish_base64);
    insert_simple!("rt_sha1_finish_bytes", crypto::rt_sha1_finish_bytes);
    insert_simple!("rt_sha1_finish", crypto::rt_sha1_finish);
    insert_simple!("rt_sha1_free", crypto::rt_sha1_free);
    insert_simple!("rt_sha1_new", crypto::rt_sha1_new);
    insert_simple!("rt_sha1_reset", crypto::rt_sha1_reset);
    insert_simple!("rt_sha1_write", crypto::rt_sha1_write);
    insert_simple!("rt_simd_add_f32x4", simd::rt_simd_add_f32x4);
    insert_simple!("rt_simd_add_f32x8", simd::rt_simd_add_f32x8);
    insert_simple!("rt_simd_add_f64x4", simd::rt_simd_add_f64x4);
    insert_simple!("rt_simd_add_i32x4", simd::rt_simd_add_i32x4);
    insert_simple!("rt_simd_add_i32x8", simd::rt_simd_add_i32x8);
    insert_simple!("rt_simd_add_i64x4", simd::rt_simd_add_i64x4);
    insert_simple!("rt_simd_add_u32x4", simd::rt_simd_add_u32x4);
    insert_simple!("rt_simd_add_u8x16", simd::rt_simd_add_u8x16);
    insert_simple!("rt_simd_aes_round_last_u8x16", simd::rt_simd_aes_round_last_u8x16);
    insert_simple!("rt_simd_aes_round_u8x16", simd::rt_simd_aes_round_u8x16);
    insert_simple!("rt_simd_and_i32x4", simd::rt_simd_and_i32x4);
    insert_simple!("rt_simd_and_i32x8", simd::rt_simd_and_i32x8);
    insert_simple!("rt_simd_and_u32x4", simd::rt_simd_and_u32x4);
    insert_simple!("rt_simd_and_u64x4", simd::rt_simd_and_u64x4);
    insert_simple!("rt_simd_clmul_hi_u64", simd::rt_simd_clmul_hi_u64);
    insert_simple!("rt_simd_clmul_lo_u64", simd::rt_simd_clmul_lo_u64);
    insert_simple!("rt_simd_detect_profile", simd::rt_simd_detect_profile);
    insert_simple!("rt_simd_div_f32x4", simd::rt_simd_div_f32x4);
    insert_simple!("rt_simd_div_f32x8", simd::rt_simd_div_f32x8);
    insert_simple!("rt_simd_div_f64x4", simd::rt_simd_div_f64x4);
    insert_simple!("rt_simd_fma_f32x4", simd::rt_simd_fma_f32x4);
    insert_simple!("rt_simd_fma_f32x8", simd::rt_simd_fma_f32x8);
    insert_simple!("rt_simd_fma_f64x4", simd::rt_simd_fma_f64x4);
    insert_simple!("rt_simd_hadd_f32x4", simd::rt_simd_hadd_f32x4);
    insert_simple!("rt_simd_hmax_f32x4", simd::rt_simd_hmax_f32x4);
    insert_simple!("rt_simd_hmin_f32x4", simd::rt_simd_hmin_f32x4);
    insert_simple!("rt_simd_has_avx2", simd::rt_simd_has_avx2);
    insert_simple!("rt_simd_has_avx", simd::rt_simd_has_avx);
    insert_simple!("rt_simd_has_neon", simd::rt_simd_has_neon);
    insert_simple!("rt_simd_has_rvv", simd::rt_simd_has_rvv);
    insert_simple!("rt_simd_has_sse", simd::rt_simd_has_sse);
    insert_simple!("rt_simd_mul_f32x4", simd::rt_simd_mul_f32x4);
    insert_simple!("rt_simd_mul_f32x8", simd::rt_simd_mul_f32x8);
    insert_simple!("rt_simd_mul_f64x4", simd::rt_simd_mul_f64x4);
    insert_simple!("rt_simd_mul_i32x4", simd::rt_simd_mul_i32x4);
    insert_simple!("rt_simd_mul_i32x8", simd::rt_simd_mul_i32x8);
    insert_simple!("rt_simd_or_i32x4", simd::rt_simd_or_i32x4);
    insert_simple!("rt_simd_or_i32x8", simd::rt_simd_or_i32x8);
    insert_simple!("rt_simd_or_u32x4", simd::rt_simd_or_u32x4);
    insert_simple!("rt_simd_or_u64x4", simd::rt_simd_or_u64x4);
    insert_simple!("rt_simd_profile_name", simd::rt_simd_profile_name);
    insert_simple!("rt_simd_shl_i32x4", simd::rt_simd_shl_i32x4);
    insert_simple!("rt_simd_shl_i32x8", simd::rt_simd_shl_i32x8);
    insert_simple!("rt_simd_shl_u64x4", simd::rt_simd_shl_u64x4);
    insert_simple!("rt_simd_shuffle_u8x16", simd::rt_simd_shuffle_u8x16);
    insert_simple!("rt_simd_shr_i32x4", simd::rt_simd_shr_i32x4);
    insert_simple!("rt_simd_shr_i32x8", simd::rt_simd_shr_i32x8);
    insert_simple!("rt_simd_shr_u64x4", simd::rt_simd_shr_u64x4);
    // Interpreter-internal string acceleration helpers. These are deliberately
    // not part of the public std.simd extern surface in simd.spl.
    insert_simple!("rt_simd_str_equal", simd::rt_simd_str_equal);
    insert_simple!("rt_simd_str_last_index_of", simd::rt_simd_str_last_index_of);
    insert_simple!("rt_simd_str_search", simd::rt_simd_str_search);
    insert_simple!("rt_simd_sub_f32x4", simd::rt_simd_sub_f32x4);
    insert_simple!("rt_simd_sub_f32x8", simd::rt_simd_sub_f32x8);
    insert_simple!("rt_simd_sub_f64x4", simd::rt_simd_sub_f64x4);
    insert_simple!("rt_simd_sub_i32x4", simd::rt_simd_sub_i32x4);
    insert_simple!("rt_simd_sub_i32x8", simd::rt_simd_sub_i32x8);
    insert_simple!("rt_simd_sub_i64x4", simd::rt_simd_sub_i64x4);
    insert_simple!("rt_simd_sub_u32x4", simd::rt_simd_sub_u32x4);
    insert_simple!("rt_simd_vec2u64_hi", simd::rt_simd_vec2u64_hi);
    insert_simple!("rt_simd_vec2u64_lo", simd::rt_simd_vec2u64_lo);
    insert_simple!("rt_simd_vec2u64_new", simd::rt_simd_vec2u64_new);
    insert_simple!("rt_simd_vec4u64_get", simd::rt_simd_vec4u64_get);
    insert_simple!("rt_simd_vec4u64_new", simd::rt_simd_vec4u64_new);
    insert_simple!("rt_simd_xor_i32x4", simd::rt_simd_xor_i32x4);
    insert_simple!("rt_simd_xor_i32x8", simd::rt_simd_xor_i32x8);
    insert_simple!("rt_simd_xor_u32x4", simd::rt_simd_xor_u32x4);
    insert_simple!("rt_simd_xor_u64x2", simd::rt_simd_xor_u64x2);
    insert_simple!("rt_simd_xor_u64x4", simd::rt_simd_xor_u64x4);
    insert_simple!("rt_simd_xor_u8x16", simd::rt_simd_xor_u8x16);
    insert_simple!("rt_sleep_ms", time::rt_sleep_ms);
    insert_simple!("rt_smf_parse_relocs", file_io::rt_smf_parse_relocs);
    insert_simple!("rt_smf_relocs_from_path", file_io::rt_smf_relocs_from_path);
    insert_simple!("rt_span_column", span_sffi::rt_span_column);
    insert_simple!("rt_span_create", span_sffi::rt_span_create);
    insert_simple!("rt_span_end", span_sffi::rt_span_end);
    insert_simple!("rt_span_free", span_sffi::rt_span_free);
    insert_simple!("rt_span_line", span_sffi::rt_span_line);
    insert_simple!("rt_span_start", span_sffi::rt_span_start);
    insert_simple!("rt_stat_open", file_io::rt_stat_open);
    insert_simple!("rt_stderr_write", io::stderr_write);
    insert_simple!("rt_stdout_write_text", io::stdout_write);
    insert_simple!("rt_string_concat", sffi_string::rt_string_concat_fn);
    insert_simple!("rt_string_eq", sffi_string::rt_string_eq_fn);
    insert_simple!("rt_string_len", sffi_string::rt_string_len_fn);
    insert_simple!("rt_string_new", sffi_string::rt_string_new_fn);
    insert_simple!("rt_swi_build", simd::rt_swi_build);
    insert_simple!("rt_swi_byte_to_char", simd::rt_swi_byte_to_char);
    insert_simple!("rt_swi_char_to_byte", simd::rt_swi_char_to_byte);
    insert_simple!("rt_swi_free", simd::rt_swi_free);
    insert_simple!("rt_system_cpu_count", file_io::rt_system_cpu_count);
    insert_simple!("rt_term_enable_ansi", system::rt_term_enable_ansi);
    insert_simple!("rt_term_get_size", system::rt_term_get_size);
    insert_simple!("rt_test_db_cleanup_stale_runs", cli::rt_test_db_cleanup_stale_runs);
    insert_simple!("rt_test_db_enable_validation", cli::rt_test_db_enable_validation);
    insert_simple!("rt_test_db_validate", cli::rt_test_db_validate);
    insert_simple!("rt_test_run_is_stale", cli::rt_test_run_is_stale);
    insert_simple!("rt_text_count_codepoints_cached", simd::rt_text_count_codepoints_cached);
    insert_simple!("rt_text_count_codepoints", simd::rt_text_count_codepoints);
    insert_simple!("rt_text_find_invalid_utf8", simd::rt_text_find_invalid_utf8);
    insert_simple!("rt_text_is_ascii", simd::rt_text_is_ascii);
    insert_simple!("rt_text_to_bytes", conversion::rt_text_to_bytes_fn);
    insert_simple!("rt_text_to_lower_ascii", simd::rt_text_to_lower_ascii);
    insert_simple!("rt_text_to_upper_ascii", simd::rt_text_to_upper_ascii);
    insert_simple!("rt_text_validate_utf8", simd::rt_text_validate_utf8);
    insert_simple!(
        "rt_thread_available_parallelism",
        concurrency::rt_thread_available_parallelism
    );
    insert_simple!("spl_thread_cpu_count", concurrency::rt_thread_available_parallelism);
    insert_simple!("spl_thread_join", concurrency::rt_thread_join);
    insert_simple!("spl_thread_detach", concurrency::rt_thread_free);
    insert_simple!("spl_thread_current_id", concurrency::rt_thread_id);
    insert_simple!("spl_thread_sleep", concurrency::rt_thread_sleep);
    insert_simple!("spl_thread_yield", concurrency::rt_thread_yield);
    insert_simple!("rt_thread_free", concurrency::rt_thread_free);
    insert_simple!("rt_thread_id", concurrency::rt_thread_id);
    insert_simple!("rt_thread_is_done", concurrency::rt_thread_is_done);
    insert_simple!("rt_thread_join", concurrency::rt_thread_join);
    insert_simple!("rt_thread_local_free", concurrency::rt_thread_local_free);
    insert_simple!("rt_thread_local_get", concurrency::rt_thread_local_get);
    insert_simple!("rt_thread_local_new", concurrency::rt_thread_local_new);
    insert_simple!("rt_thread_local_set", concurrency::rt_thread_local_set);
    insert_simple!("rt_thread_sleep", concurrency::rt_thread_sleep);
    insert_simple!("rt_thread_yield", concurrency::rt_thread_yield);
    insert_simple!("rt_time_monotonic_ns", time::rt_time_monotonic_ns);
    insert_simple!("rt_time_ms", time::rt_time_ms_fn);
    insert_simple!("rt_time_now_micros", time::rt_time_now_micros);
    insert_simple!("rt_time_now_monotonic_ms", file_io::rt_time_now_monotonic_ms);
    insert_simple!("rt_time_now_ms", time::rt_time_now_ms);
    insert_simple!("rt_time_now_nanos", time::rt_time_now_nanos);
    insert_simple!("rt_time_now_seconds", time::rt_time_now_seconds);
    insert_simple!("rt_time_now", time::rt_time_now);
    insert_simple!("rt_time_now_unix_micros", time::rt_time_now_unix_micros);
    insert_simple!("rt_timestamp_add_days", time::rt_timestamp_add_days);
    insert_simple!("rt_timestamp_diff_days", time::rt_timestamp_diff_days);
    insert_simple!("rt_timestamp_from_components", time::rt_timestamp_from_components);
    insert_simple!("rt_timestamp_get_day", time::rt_timestamp_get_day);
    insert_simple!("rt_timestamp_get_hour", time::rt_timestamp_get_hour);
    insert_simple!("rt_timestamp_get_microsecond", time::rt_timestamp_get_microsecond);
    insert_simple!("rt_timestamp_get_minute", time::rt_timestamp_get_minute);
    insert_simple!("rt_timestamp_get_month", time::rt_timestamp_get_month);
    insert_simple!("rt_timestamp_get_second", time::rt_timestamp_get_second);
    insert_simple!("rt_timestamp_get_year", time::rt_timestamp_get_year);
    insert_simple!("rt_timestamp_iso8601", time::rt_timestamp_iso8601);
    insert_simple!("rt_tls13_aes128_gcm_decrypt", simd::rt_tls13_aes128_gcm_decrypt);
    insert_simple!("rt_tls13_aes128_gcm_encrypt", simd::rt_tls13_aes128_gcm_encrypt);
    insert_simple!("rt_tls13_aes256_gcm_decrypt", simd::rt_tls13_aes256_gcm_decrypt);
    insert_simple!("rt_tls13_aes256_gcm_encrypt", simd::rt_tls13_aes256_gcm_encrypt);
    insert_simple!("rt_tls13_ed25519_verify", signatures::rt_ed25519_verify);
    insert_simple!("rt_torch_clone", torch::rt_torch_clone);
    insert_simple!("rt_torch_copy_data_to_cpu", torch::rt_torch_copy_data_to_cpu);
    insert_simple!("rt_torch_free", torch::rt_torch_free);
    insert_simple!("rt_torch_tensor", torch::rt_torch_tensor);
    insert_simple!("rt_torch_to_cpu", torch::rt_torch_to_cpu);
    insert_simple!("rt_torch_to_cuda", torch::rt_torch_to_cuda);
    insert_simple!("rt_typed_bytes_u32_le_at", sffi_array::rt_bytes_u32_le_at_fn);
    insert_simple!("rt_typed_bytes_u64_le_at", sffi_array::rt_bytes_u64_le_at_fn);
    insert_simple!("rt_typed_bytes_u64_le_unchecked", sffi_array::rt_bytes_u64_le_at_fn);
    insert_simple!("rt_typed_bytes_u8_push", sffi_array::rt_typed_bytes_u8_push_fn);
    insert_simple!("rt_typed_bytes_u8_unchecked", sffi_array::rt_bytes_u8_at_fn);
    insert_simple!("rt_typed_words_u32_at", sffi_array::rt_typed_words_u32_at_fn);
    insert_simple!("rt_typed_words_u32_push", sffi_array::rt_typed_words_u32_push_fn);
    insert_simple!("rt_typed_words_u32_set", sffi_array::rt_typed_words_u32_set_fn);
    insert_simple!(
        "rt_typed_words_u32_unchecked",
        sffi_array::rt_typed_words_u32_unchecked_fn
    );
    insert_simple!("rt_typed_words_u64_at", sffi_array::rt_typed_words_u64_at_fn);
    insert_simple!(
        "rt_typed_words_u64_unchecked",
        sffi_array::rt_typed_words_u64_unchecked_fn
    );
    insert_simple!("rt_u32_alloc_filled", file_io::rt_u32_alloc_filled);
    insert_simple!("rt_unix_socket_accept", qmp_socket::rt_unix_socket_accept);
    insert_simple!("rt_unix_socket_close", qmp_socket::rt_unix_socket_close);
    insert_simple!("rt_unix_socket_connect", qmp_socket::rt_unix_socket_connect);
    insert_simple!("rt_unix_socket_listen", qmp_socket::rt_unix_socket_listen);
    insert_simple!("rt_unix_socket_recv", qmp_socket::rt_unix_socket_recv);
    insert_simple!("rt_unix_socket_send", qmp_socket::rt_unix_socket_send);
    insert_simple!("rt_utf8_count_codepoints", simd::rt_utf8_count_codepoints);
    insert_simple!("rt_utf8_find_invalid", simd::rt_utf8_find_invalid);
    insert_simple!("rt_utf8_validate", simd::rt_utf8_validate);
    insert_simple!("rt_value_as_bool", sffi_value::rt_value_as_bool_fn);
    insert_simple!("rt_value_as_float", sffi_value::rt_value_as_float_fn);
    insert_simple!("rt_value_as_int", sffi_value::rt_value_as_int_fn);
    insert_simple!("rt_value_bool", sffi_value::rt_value_bool_fn);
    insert_simple!("rt_value_float", sffi_value::rt_value_float_fn);
    insert_simple!("rt_value_int", sffi_value::rt_value_int_fn);
    insert_simple!("rt_value_is_bool", sffi_value::rt_value_is_bool_fn);
    insert_simple!("rt_value_is_float", sffi_value::rt_value_is_float_fn);
    insert_simple!("rt_value_is_heap", sffi_value::rt_value_is_heap_fn);
    insert_simple!("rt_value_is_int", sffi_value::rt_value_is_int_fn);
    insert_simple!("rt_value_is_nil", sffi_value::rt_value_is_nil_fn);
    insert_simple!("rt_value_nil", sffi_value::rt_value_nil_fn);
    insert_simple!("rt_value_truthy", sffi_value::rt_value_truthy_fn);
    insert_simple!("rt_value_type_tag", sffi_value::rt_value_type_tag_fn);
    insert_simple!("rt_vk_available", gpu::rt_vk_available_fn);
    insert_simple!("rt_vulkan_begin_graphics_frame", gpu::rt_vulkan_begin_graphics_frame_fn);
    insert_simple!("rt_vulkan_begin_render_pass", gpu::rt_vulkan_begin_render_pass_fn);
    insert_simple!(
        "rt_vulkan_cmd_bind_index_buffer",
        gpu::rt_vulkan_cmd_bind_index_buffer_fn
    );
    insert_simple!("rt_vulkan_cmd_bind_texture", gpu::rt_vulkan_cmd_bind_texture_fn);
    insert_simple!(
        "rt_vulkan_cmd_bind_uniform_buffer",
        gpu::rt_vulkan_cmd_bind_uniform_buffer_fn
    );
    insert_simple!(
        "rt_vulkan_cmd_bind_vertex_buffer",
        gpu::rt_vulkan_cmd_bind_vertex_buffer_fn
    );
    insert_simple!("rt_vulkan_cmd_draw_indexed", gpu::rt_vulkan_cmd_draw_indexed_fn);
    insert_simple!("rt_vulkan_cmd_set_pipeline", gpu::rt_vulkan_cmd_set_pipeline_fn);
    insert_simple!("rt_vulkan_alloc_buffer", gpu::rt_vulkan_alloc_buffer_fn);
    insert_simple!("rt_vulkan_begin_compute", gpu::rt_vulkan_begin_compute_fn);
    insert_simple!("rt_vulkan_bind_buffer", gpu::rt_vulkan_bind_buffer_fn);
    insert_simple!("rt_vulkan_bind_descriptors", gpu::rt_vulkan_bind_descriptors_fn);
    insert_simple!("rt_vulkan_bind_pipeline", gpu::rt_vulkan_bind_pipeline_fn);
    insert_simple!("rt_vulkan_copy_to_buffer", gpu::rt_vulkan_copy_to_buffer_fn);
    insert_simple!("rt_vulkan_compile_glsl", gpu::rt_vulkan_compile_glsl_fn);
    insert_simple!("rt_vulkan_compile_spirv", gpu::rt_vulkan_compile_spirv_fn);
    insert_simple!("rt_vulkan_read_buffer_bytes", gpu::rt_vulkan_read_buffer_bytes_fn);
    insert_simple!(
        "rt_vulkan_create_compute_pipeline",
        gpu::rt_vulkan_create_compute_pipeline_fn
    );
    insert_simple!(
        "rt_vulkan_create_descriptor_set",
        gpu::rt_vulkan_create_descriptor_set_fn
    );
    insert_simple!(
        "rt_vulkan_create_graphics_buffer",
        gpu::rt_vulkan_create_graphics_buffer_fn
    );
    insert_simple!(
        "rt_vulkan_destroy_descriptor_set",
        gpu::rt_vulkan_destroy_descriptor_set_fn
    );
    insert_simple!("rt_vulkan_destroy_pipeline", gpu::rt_vulkan_destroy_pipeline_fn);
    insert_simple!("rt_vulkan_destroy_shader", gpu::rt_vulkan_destroy_shader_fn);
    insert_simple!("rt_vulkan_device_count", gpu::rt_vulkan_device_count_fn);
    insert_simple!("rt_vulkan_device_name", gpu::rt_vulkan_device_name_fn);
    insert_simple!("rt_vulkan_dispatch", gpu::rt_vulkan_dispatch_fn);
    insert_simple!("rt_vulkan_end_compute", gpu::rt_vulkan_end_compute_fn);
    insert_simple!("rt_vulkan_free_buffer", gpu::rt_vulkan_free_buffer_fn);
    insert_simple!("rt_vulkan_get_device", gpu::rt_vulkan_get_device_fn);
    insert_simple!("rt_vulkan_get_last_error", gpu::rt_vulkan_get_last_error_fn);
    insert_simple!("rt_vulkan_init", gpu::rt_vulkan_init_fn);
    insert_simple!("rt_vulkan_is_available", gpu::rt_vulkan_is_available_fn);
    insert_simple!("rt_vulkan_push_constants", gpu::rt_vulkan_push_constants_fn);
    insert_simple!("rt_vulkan_select_device", gpu::rt_vulkan_select_device_fn);
    insert_simple!("rt_vulkan_shutdown", gpu::rt_vulkan_shutdown_fn);
    insert_simple!("rt_vulkan_submit_and_wait", gpu::rt_vulkan_submit_and_wait_fn);
    insert_simple!("rt_vulkan_wait_idle", gpu::rt_vulkan_wait_idle_fn);
    insert_simple!(
        "rt_vulkan_create_graphics_pipeline",
        gpu::rt_vulkan_create_graphics_pipeline_fn
    );
    insert_simple!("rt_vulkan_create_image", gpu::rt_vulkan_create_image_fn);
    insert_simple!("rt_vulkan_end_graphics_frame", gpu::rt_vulkan_end_graphics_frame_fn);
    insert_simple!("rt_vulkan_end_render_pass", gpu::rt_vulkan_end_render_pass_fn);
    insert_simple!("rt_vulkan_graphics_present", gpu::rt_vulkan_graphics_present_fn);
    insert_simple!("rt_vulkan_init_graphics", gpu::rt_vulkan_init_graphics_fn);
    insert_simple!("rt_vulkan_shutdown_graphics", gpu::rt_vulkan_shutdown_graphics_fn);
    insert_simple!(
        "rt_vulkan_upload_graphics_buffer",
        gpu::rt_vulkan_upload_graphics_buffer_fn
    );
    insert_simple!("rt_vulkan_upload_image", gpu::rt_vulkan_upload_image_fn);
    insert_simple!("rt_webgpu_compute_draw", gpu::rt_webgpu_compute_draw_fn);
    insert_simple!("rt_webgpu_create_surface", gpu::rt_webgpu_create_surface_fn);
    insert_simple!("rt_webgpu_destroy_surface", gpu::rt_webgpu_destroy_surface_fn);
    insert_simple!("rt_webgpu_init", gpu::rt_webgpu_init_fn);
    insert_simple!("rt_webgpu_is_available", gpu::rt_webgpu_is_available_fn);
    insert_simple!("rt_webgpu_present", gpu::rt_webgpu_present_fn);
    insert_simple!("rt_webgpu_shutdown", gpu::rt_webgpu_shutdown_fn);
    insert_simple!("rt_webgpu_upload_pixels", gpu::rt_webgpu_upload_pixels_fn);
    insert_simple!("rt_wgpu_3d_begin_frame", gpu::rt_wgpu_3d_begin_frame_fn);
    insert_simple!("rt_wgpu_3d_begin_render_pass", gpu::rt_wgpu_3d_begin_render_pass_fn);
    insert_simple!(
        "rt_wgpu_3d_cmd_bind_index_buffer",
        gpu::rt_wgpu_3d_cmd_bind_index_buffer_fn
    );
    insert_simple!("rt_wgpu_3d_cmd_bind_texture", gpu::rt_wgpu_3d_cmd_bind_texture_fn);
    insert_simple!(
        "rt_wgpu_3d_cmd_bind_uniform_buffer",
        gpu::rt_wgpu_3d_cmd_bind_uniform_buffer_fn
    );
    insert_simple!(
        "rt_wgpu_3d_cmd_bind_vertex_buffer",
        gpu::rt_wgpu_3d_cmd_bind_vertex_buffer_fn
    );
    insert_simple!("rt_wgpu_3d_cmd_draw_indexed", gpu::rt_wgpu_3d_cmd_draw_indexed_fn);
    insert_simple!("rt_wgpu_3d_cmd_set_pipeline", gpu::rt_wgpu_3d_cmd_set_pipeline_fn);
    insert_simple!("rt_wgpu_3d_create_buffer", gpu::rt_wgpu_3d_create_buffer_fn);
    insert_simple!("rt_wgpu_3d_create_pipeline", gpu::rt_wgpu_3d_create_pipeline_fn);
    insert_simple!("rt_wgpu_3d_create_texture", gpu::rt_wgpu_3d_create_texture_fn);
    insert_simple!("rt_wgpu_3d_end_frame", gpu::rt_wgpu_3d_end_frame_fn);
    insert_simple!("rt_wgpu_3d_end_render_pass", gpu::rt_wgpu_3d_end_render_pass_fn);
    insert_simple!("rt_wgpu_3d_init", gpu::rt_wgpu_3d_init_fn);
    insert_simple!("rt_wgpu_3d_present", gpu::rt_wgpu_3d_present_fn);
    insert_simple!("rt_wgpu_3d_shutdown", gpu::rt_wgpu_3d_shutdown_fn);
    insert_simple!("rt_wgpu_3d_upload_buffer", gpu::rt_wgpu_3d_upload_buffer_fn);
    insert_simple!("rt_wgpu_3d_upload_texture", gpu::rt_wgpu_3d_upload_texture_fn);
    insert_simple!("rt_write_file", cranelift::rt_write_file);
    insert_simple!("serial_println", host_wm_bridge::serial_println);
    insert_simple!("simple_layout_mark", layout::simple_layout_mark);
    insert_simple!("simple_repl_runner_cleanup", repl::simple_repl_runner_cleanup_fn);
    insert_simple!("simple_repl_runner_init", repl::simple_repl_runner_init_fn);
    insert_simple!("spl_bits_to_f64", wsffi::spl_bits_to_f64);
    insert_simple!("spl_dlclose", wsffi::spl_dlclose);
    insert_simple!("spl_dlopen", wsffi::spl_dlopen);
    insert_simple!("spl_dlsym", wsffi::spl_dlsym);
    insert_simple!("spl_f64_to_bits", wsffi::spl_f64_to_bits);
    insert_simple!("spl_i64_is_zero", memory::spl_i64_is_zero);
    insert_simple!("spl_str_ptr", wsffi::spl_str_ptr);
    insert_simple!("spl_wffi_call_f64", wsffi::spl_wffi_call_f64);
    insert_simple!("spl_wffi_call_i64", wsffi::spl_wffi_call_i64);
    insert_simple!("sqrt", math::sqrt);
    insert_simple!("stderr_flush", io::stderr_flush);
    insert_simple!("stderr_write", io::stderr_write);
    insert_simple!("stdin_read_char", io::input::stdin_read_char);
    insert_simple!("stdout_flush", io::stdout_flush);
    insert_simple!("stdout_write", io::stdout_write);
    insert_simple!("sys_exit", system::sys_exit);
    insert_simple!("sys_free", memory::sys_free);
    insert_simple!("sys_get_args", system::sys_get_args);
    insert_simple!("sys_malloc", memory::sys_malloc);
    insert_simple!("sys_realloc", memory::sys_realloc);
    insert_simple!("to_int", conversion::to_int);
    insert_simple!("to_string", conversion::to_string);

    // TUI (ratatui) operations — feature-gated
    #[cfg(feature = "tui")]
    {
        insert_simple!("ratatui_object_destroy", tui::ratatui_object_destroy_fn);
        insert_simple!("ratatui_terminal_cleanup", tui::ratatui_terminal_cleanup_fn);
        insert_simple!("ratatui_terminal_clear", tui::ratatui_terminal_clear_fn);
        insert_simple!("ratatui_terminal_new", tui::ratatui_terminal_new_fn);
        insert_simple!("ratatui_textbuffer_backspace", tui::ratatui_textbuffer_backspace_fn);
        insert_simple!("ratatui_textbuffer_insert_char", tui::ratatui_textbuffer_insert_char_fn);
        insert_simple!("ratatui_textbuffer_newline", tui::ratatui_textbuffer_newline_fn);
        insert_simple!("ratatui_textbuffer_new", tui::ratatui_textbuffer_new_fn);
    }

    // Vulkan GPU operations — feature-gated
    #[cfg(feature = "vulkan")]
    {
        insert_simple!("rt_vk_buffer_alloc", gpu::rt_vk_buffer_alloc_fn);
        insert_simple!("rt_vk_buffer_download", gpu::rt_vk_buffer_download_fn);
        insert_simple!("rt_vk_buffer_free", gpu::rt_vk_buffer_free_fn);
        insert_simple!("rt_vk_buffer_upload", gpu::rt_vk_buffer_upload_fn);
        insert_simple!("rt_vk_device_create", gpu::rt_vk_device_create_fn);
        insert_simple!("rt_vk_device_free", gpu::rt_vk_device_free_fn);
        insert_simple!("rt_vk_device_sync", gpu::rt_vk_device_sync_fn);
        insert_simple!("rt_vk_kernel_compile", gpu::rt_vk_kernel_compile_fn);
        insert_simple!("rt_vk_kernel_free", gpu::rt_vk_kernel_free_fn);
        insert_simple!("rt_vk_kernel_launch_1d", gpu::rt_vk_kernel_launch_1d_fn);
        insert_simple!("rt_vk_kernel_launch", gpu::rt_vk_kernel_launch_fn);
    }

    // Previously missing from HashMap — simple &[Value] functions
    // PBKDF2, SHA-512, TLS 1.3 crypto helpers
    insert_simple!("rt_pbkdf2_hmac_sha1", pbkdf2::rt_pbkdf2_hmac_sha1);
    insert_simple!("rt_pbkdf2_hmac_sha256", pbkdf2::rt_pbkdf2_hmac_sha256);
    insert_simple!("rt_pbkdf2_hmac_sha384", pbkdf2::rt_pbkdf2_hmac_sha384);
    insert_simple!("rt_pbkdf2_hmac_sha512", pbkdf2::rt_pbkdf2_hmac_sha512);
    insert_simple!("rt_sha512_hash", sha512::rt_sha512_hash);
    insert_simple!("rt_sha512_byte", sha512::rt_sha512_byte);
    insert_simple!("rt_sha512_K", sha512::rt_sha512_k);
    insert_simple!("rt_sha512_H", sha512::rt_sha512_h);
    insert_simple!("rt_tls13_sha256", tls13::rt_tls13_sha256);
    insert_simple!("rt_tls13_hkdf_extract", tls13::rt_tls13_hkdf_extract);
    insert_simple!("rt_tls13_hkdf_extract_into", tls13::rt_tls13_hkdf_extract_into);
    insert_simple!("rt_tls13_hkdf_expand_into", tls13::rt_tls13_hkdf_expand_into);
    insert_simple!("rt_tls13_hkdf_expand_label", tls13::rt_tls13_hkdf_expand_label);
    insert_simple!(
        "rt_tls13_hkdf_expand_label_into",
        tls13::rt_tls13_hkdf_expand_label_into
    );
    insert_simple!(
        "rt_tls13_hkdf_expand_label_derived",
        tls13::rt_tls13_hkdf_expand_label_derived
    );
    insert_simple!("rt_tls13_hkdf_expand_label_key", tls13::rt_tls13_hkdf_expand_label_key);
    insert_simple!("rt_tls13_hkdf_expand_label_iv", tls13::rt_tls13_hkdf_expand_label_iv);
    insert_simple!(
        "rt_tls13_hkdf_expand_label_finished",
        tls13::rt_tls13_hkdf_expand_label_finished
    );
    insert_simple!(
        "rt_tls13_hkdf_expand_label_client_hs",
        tls13::rt_tls13_hkdf_expand_label_client_hs
    );
    insert_simple!(
        "rt_tls13_hkdf_expand_label_server_hs",
        tls13::rt_tls13_hkdf_expand_label_server_hs
    );
    insert_simple!(
        "rt_tls13_hkdf_expand_label_client_app",
        tls13::rt_tls13_hkdf_expand_label_client_app
    );
    insert_simple!(
        "rt_tls13_hkdf_expand_label_server_app",
        tls13::rt_tls13_hkdf_expand_label_server_app
    );
    // TLS client stubs (interpreter mode — no real TLS)
    insert_simple!("rt_tls_client_connect", rt_tls_client_connect_stub);
    insert_simple!("rt_tls_client_connect_with_sni", rt_tls_client_connect_stub);
    insert_simple!("rt_tls_client_write", rt_tls_client_write_stub);
    insert_simple!("rt_tls_client_read", rt_tls_client_read_stub);
    insert_simple!("rt_tls_client_close", rt_tls_client_close_stub);
    insert_simple!("rt_tls_get_protocol_version", rt_tls_get_protocol_version_stub);
    // PTY (pseudo-terminal) operations
    insert_simple!("rt_pty_open", pty::rt_pty_open);
    insert_simple!("rt_pty_spawn", pty::rt_pty_spawn);
    // I/O wrappers that pass empty slice or alias another function
    insert_simple!("rt_stdin_read_line", rt_stdin_read_line_stub);
    insert_simple!("rt_stdout_flush", io::stdout_flush);
    insert_simple!("rt_stderr_flush", io::stderr_flush);
    // Hosted surface selection
    insert_simple!("rt_hosted_select_surface", hosted::select_surface);
    insert_simple!("rt_hosted_set_surface_override", hosted::set_surface_override);
    // Native compilation & execution
    insert_simple!("rt_compile_to_llvm_ir", native_sffi::rt_compile_to_llvm_ir);
    insert_simple!("rt_compile_to_native", native_sffi::rt_compile_to_native);
    insert_simple!("rt_compile_to_native_with_opt", native_sffi::rt_compile_to_native);
    insert_simple!("rt_execute_native", native_sffi::rt_execute_native);
    // Package management
    insert_simple!("rt_package_sha256", package::sha256);
    insert_simple!("rt_package_create_tarball", package::create_tarball);
    insert_simple!("rt_package_extract_tarball", package::extract_tarball);
    insert_simple!("rt_package_file_size", package::file_size);
    insert_simple!("rt_package_copy_file", package::copy_file);
    insert_simple!("rt_package_mkdir_all", package::mkdir_all);
    insert_simple!("rt_package_remove_dir_all", package::remove_dir_all);
    insert_simple!("rt_package_create_symlink", package::create_symlink);
    insert_simple!("rt_package_chmod", package::chmod);
    insert_simple!("rt_package_exists", package::exists);
    insert_simple!("rt_package_is_dir", package::is_dir);
    // Performance stubs
    insert_simple!("rt_perf_enable", rt_perf_stub);
    insert_simple!("rt_perf_enabled", rt_perf_stub);
    insert_simple!("rt_perf_clock_ns", rt_perf_stub);
    insert_simple!("rt_perf_rdtsc", rt_perf_stub);
    insert_simple!("rt_perf_cycles_to_ns", rt_perf_stub);
    insert_simple!("rt_perf_region_enter", rt_perf_stub);
    insert_simple!("rt_perf_region_exit", rt_perf_stub);
    insert_simple!("rt_perf_dump_sdn", rt_perf_stub);
    insert_simple!("rt_perf_free_sdn", rt_perf_stub);
    insert_simple!("rt_perf_clear", rt_perf_stub);

    m.insert(
        "compiler__driver__driver__compiler_driver_create",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            call_loaded_function_by_name(
                "compiler_driver_create",
                evaluated,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }) as ExternHandler,
    );
    m.insert(
        "compiler__driver__driver__CompilerDriver_dot_compile",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            call_loaded_function_by_name(
                "CompilerDriver_dot_compile",
                evaluated,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }) as ExternHandler,
    );
    m.insert(
        "print",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            let resolved = resolve_fmt_for_print(evaluated, env, functions, classes, enums, impl_methods);
            io::print::print(&resolved)
        }) as ExternHandler,
    );
    m.insert(
        "print_raw",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            let resolved = resolve_fmt_for_print(evaluated, env, functions, classes, enums, impl_methods);
            io::print::print_raw(&resolved)
        }) as ExternHandler,
    );
    m.insert(
        "eprint",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            let resolved = resolve_fmt_for_print(evaluated, env, functions, classes, enums, impl_methods);
            io::print::eprint(&resolved)
        }) as ExternHandler,
    );
    m.insert(
        "eprint_raw",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            let resolved = resolve_fmt_for_print(evaluated, env, functions, classes, enums, impl_methods);
            io::print::eprint_raw(&resolved)
        }) as ExternHandler,
    );
    m.insert(
        "dbg",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            let resolved = resolve_fmt_for_print(evaluated, env, functions, classes, enums, impl_methods);
            io::print::dbg(&resolved)
        }) as ExternHandler,
    );
    m.insert(
        "spl_thread_create",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            concurrency::rt_thread_spawn_isolated_with_context(evaluated, env, functions, classes, enums, impl_methods)
        }) as ExternHandler,
    );
    m.insert(
        "rt_thread_spawn_isolated",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            concurrency::rt_thread_spawn_isolated_with_context(evaluated, env, functions, classes, enums, impl_methods)
        }) as ExternHandler,
    );
    m.insert(
        "rt_thread_spawn_isolated2",
        (|evaluated, env, functions, classes, enums, impl_methods| {
            concurrency::rt_thread_spawn_isolated2_with_context(evaluated, env, functions, classes, enums, impl_methods)
        }) as ExternHandler,
    );
    m.insert(
        "rt_i18n_context_new",
        (|_evaluated, env, _functions, _classes, _enums, _impl_methods| i18n::rt_i18n_context_new(env))
            as ExternHandler,
    );
    m.insert(
        "rt_i18n_context_insert",
        (|evaluated, env, _functions, _classes, _enums, _impl_methods| i18n::rt_i18n_context_insert(evaluated, env))
            as ExternHandler,
    );
    m.insert(
        "rt_i18n_context_free",
        (|evaluated, env, _functions, _classes, _enums, _impl_methods| i18n::rt_i18n_context_free(evaluated, env))
            as ExternHandler,
    );
    m.insert(
        "rt_i18n_get_message",
        (|evaluated, env, _functions, _classes, _enums, _impl_methods| i18n::rt_i18n_get_message(evaluated, env))
            as ExternHandler,
    );
    m.insert(
        "rt_i18n_severity_name",
        (|evaluated, env, _functions, _classes, _enums, _impl_methods| i18n::rt_i18n_severity_name(evaluated, env))
            as ExternHandler,
    );
    m
}

/// Central extern function dispatcher
///
/// Routes extern function calls to the appropriate module based on function name.
/// Uses O(1) HashMap lookup for ~1038 simple extern functions, with a match
/// fallback for ~20 complex externs that need env/functions/classes.
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
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Diagram tracing for extern function calls
    if diagram_sffi::is_diagram_enabled() {
        diagram_sffi::trace_call(name);
    }

    if !simple_runtime::rt_security_host_import_allowed(name.as_ptr(), name.len() as u64) {
        return Err(CompileError::runtime(format!(
            "host import '{name}' denied by active sandbox"
        )));
    }

    // Evaluate all arguments upfront
    let evaluated: Vec<Value> = args
        .iter()
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .collect::<Result<Vec<_>, _>>()?;

    // Fast path: O(1) HashMap lookup for extern functions.
    if let Some(func) = EXTERN_DISPATCH.get(name) {
        return func(&evaluated, env, functions, classes, enums, impl_methods);
    }

    // Prefix dispatches remain outside the table because they are wildcard namespaces.
    #[cfg(feature = "gui")]
    if name.starts_with("rt_winit_") {
        return winit_sffi::dispatch(name, &evaluated);
    }

    if name.starts_with("rt_rapier2d_") {
        return rapier2d_sffi::dispatch(name, &evaluated);
    }

    if name.starts_with("rt_driver_") {
        if let Some(result) = io_driver::dispatch(name, &evaluated) {
            return result;
        }
        return Err(common::unknown_function(name));
    }

    if let Some(result) = dynamic_sffi::try_call_dynamic(name, &evaluated) {
        return result;
    }

    Err(common::unknown_function(name))
}
