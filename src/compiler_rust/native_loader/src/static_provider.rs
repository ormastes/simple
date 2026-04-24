//! Static symbol provider - runtime functions compiled into the binary.
//!
//! This provider has zero runtime lookup cost since all function pointers
//! are resolved at compile time via direct references.

use simple_common::{AbiVersion, RuntimeSymbolProvider, RUNTIME_SYMBOL_NAMES};
use simple_runtime::value::ffi::{rt_native_eq, rt_native_neq};

/// Provides runtime symbols via static linking (compiled into binary).
///
/// This is the default provider for release builds - all runtime FFI
/// functions are directly linked into the binary with zero lookup overhead.
pub struct StaticSymbolProvider;

impl StaticSymbolProvider {
    /// Create a new static symbol provider.
    pub fn new() -> Self {
        Self
    }
}

impl Default for StaticSymbolProvider {
    fn default() -> Self {
        Self::new()
    }
}

/// Macro to generate match arms for all runtime symbols.
/// This reduces boilerplate and ensures consistency with the symbol list.
macro_rules! match_runtime_symbol {
    ($name:expr, $($sym:ident),* $(,)?) => {
        match $name {
            $(stringify!($sym) => Some($sym as *const u8),)*
            _ => None,
        }
    };
}

impl RuntimeSymbolProvider for StaticSymbolProvider {
    fn get_symbol(&self, name: &str) -> Option<*const u8> {
        let normalized = name.strip_prefix('_').unwrap_or(name);
        use simple_runtime::value::{
            rt_array_clear, rt_array_first, rt_capture_stderr_start, rt_capture_stdout_start, rt_cli_get_args,
            rt_cli_print_help, rt_cli_print_version, rt_cli_version, rt_condition_probe, rt_contains,
            rt_decision_probe, rt_dict_clear, rt_dict_keys, rt_dict_remove, rt_dict_values, rt_env_all, rt_env_cwd,
            rt_env_exists, rt_env_get, rt_env_home, rt_env_remove, rt_env_set, rt_env_temp, rt_env_vars, rt_eprint_str,
            rt_eprint_value, rt_eprintln_str, rt_eprintln_value, rt_exit, rt_function_not_found, rt_get_env,
            rt_interp_call, rt_interp_eval, rt_is_debug_mode_enabled, rt_is_macro_trace_enabled, rt_is_some,
            rt_method_not_found, rt_len, rt_path_probe, rt_platform_name, rt_print_str, rt_print_value, rt_println_str,
            rt_println_value, rt_range, rt_range_inclusive, rt_string_char_at, rt_string_ends_with, rt_string_eq,
            rt_string_find, rt_string_index_of, rt_string_join, rt_string_replace, rt_string_rfind, rt_string_split,
            rt_string_starts_with, rt_string_to_int, rt_string_to_lower, rt_string_to_upper, rt_string_trim,
            rt_term_enable_ansi, rt_term_get_size, rt_process_execute, rt_process_is_running, rt_process_kill,
            rt_process_run, rt_process_spawn, rt_process_spawn_async, rt_process_wait, rt_set_debug_mode, rt_set_env,
            rt_set_macro_trace, rt_to_string, rt_unwrap_or_self, rt_value_compare, rt_value_eq, rt_value_to_string,
        };
        // File I/O operations
        use simple_runtime::value::{
            rt_file_exists, rt_file_stat, rt_file_canonicalize, rt_file_read_text, rt_file_read_text_rv,
            rt_file_write_text, rt_file_copy, rt_file_remove, rt_file_size, rt_file_rename, rt_file_read_lines, rt_file_append_text,
            rt_file_read_bytes, rt_bytes_from_raw, rt_bytes_to_text, rt_text_to_bytes, rt_file_write_bytes,
            rt_file_move, rt_dir_create, rt_dir_list, rt_dir_remove, rt_file_find, rt_dir_glob, rt_dir_create_all,
            rt_dir_walk, rt_current_dir, rt_set_current_dir, rt_dir_remove_all, rt_file_open, rt_file_get_size,
            rt_file_close, rt_path_basename, rt_path_dirname, rt_path_ext, rt_path_absolute, rt_path_separator,
            rt_path_stem, rt_path_relative, rt_path_join,
        };
        use simple_runtime::value::{
            rt_io_tcp_accept, rt_io_tcp_accept_timeout, rt_io_tcp_bind, rt_io_tcp_close, rt_io_tcp_connect,
            rt_io_tcp_connect_timeout, rt_io_tcp_flush, rt_io_tcp_local_addr, rt_io_tcp_peer_addr, rt_io_tcp_read,
            rt_io_tcp_read_line, rt_io_tcp_set_nodelay, rt_io_tcp_set_read_timeout, rt_io_tcp_set_write_timeout,
            rt_io_tcp_shutdown, rt_io_tcp_write, rt_io_tcp_write_text, rt_tls_client_close,
            rt_tls_client_config_add_root_cert, rt_tls_client_config_enable_sni, rt_tls_client_config_free,
            rt_tls_client_config_new, rt_tls_client_config_set_alpn, rt_tls_client_config_set_verify_mode,
            rt_tls_client_connect, rt_tls_client_connect_with_sni, rt_tls_client_read, rt_tls_client_write,
            rt_tls_free_cert, rt_tls_generate_self_signed_cert, rt_tls_get_cert_expiry, rt_tls_get_cert_issuer,
            rt_tls_get_cert_subject, rt_tls_get_cipher_suite, rt_tls_get_negotiated_alpn, rt_tls_get_peer_cert,
            rt_tls_get_protocol_version, rt_tls_hash_cert, rt_tls_is_handshake_complete, rt_tls_load_cert,
            rt_tls_load_key, rt_tls_server_accept, rt_tls_server_close_connection, rt_tls_server_config_free,
            rt_tls_server_config_new, rt_tls_server_config_require_client_cert, rt_tls_server_config_set_alpn,
            rt_tls_server_create, rt_tls_server_read, rt_tls_server_shutdown, rt_tls_server_write,
            rt_tls_server_write_bytes, rt_tls_verify_cert,
        };
        use simple_runtime::value::{
            rt_sha1_finish, rt_sha1_finish_base64, rt_sha1_finish_bytes, rt_sha1_free, rt_sha1_new, rt_sha1_reset,
            rt_sha1_write, rt_sha256_finish, rt_sha256_finish_bytes, rt_sha256_free, rt_sha256_new, rt_sha256_reset,
            rt_sha256_write, rt_xxhash_finish, rt_xxhash_free, rt_xxhash_new, rt_xxhash_new_with_seed, rt_xxhash_reset,
            rt_xxhash_write,
        };
        // Regex operations
        use simple_runtime::value::{
            ffi_regex_captures, ffi_regex_find, ffi_regex_find_all, ffi_regex_is_match, ffi_regex_replace,
            ffi_regex_replace_all, ffi_regex_split, ffi_regex_split_n,
        };
        // High-performance collections
        use simple_runtime::value::{
            // HashMap
            rt_hashmap_clear,
            rt_hashmap_contains_key,
            rt_hashmap_drop,
            rt_hashmap_entries,
            rt_hashmap_get,
            rt_hashmap_insert,
            rt_hashmap_keys,
            rt_hashmap_len,
            rt_hashmap_new,
            rt_hashmap_remove,
            rt_hashmap_values,
            // BTreeMap
            rt_btreemap_clear,
            rt_btreemap_contains_key,
            rt_btreemap_drop,
            rt_btreemap_entries,
            rt_btreemap_first_key,
            rt_btreemap_get,
            rt_btreemap_insert,
            rt_btreemap_keys,
            rt_btreemap_last_key,
            rt_btreemap_len,
            rt_btreemap_new,
            rt_btreemap_remove,
            rt_btreemap_values,
            // HashSet
            rt_hashset_clear,
            rt_hashset_contains,
            rt_hashset_difference,
            rt_hashset_drop,
            rt_hashset_insert,
            rt_hashset_intersection,
            rt_hashset_is_subset,
            rt_hashset_is_superset,
            rt_hashset_len,
            rt_hashset_new,
            rt_hashset_remove,
            rt_hashset_symmetric_difference,
            rt_hashset_to_array,
            rt_hashset_union,
            // BTreeSet
            rt_btreeset_clear,
            rt_btreeset_contains,
            rt_btreeset_difference,
            rt_btreeset_drop,
            rt_btreeset_first,
            rt_btreeset_insert,
            rt_btreeset_intersection,
            rt_btreeset_is_subset,
            rt_btreeset_is_superset,
            rt_btreeset_last,
            rt_btreeset_len,
            rt_btreeset_new,
            rt_btreeset_remove,
            rt_btreeset_symmetric_difference,
            rt_btreeset_to_array,
            rt_btreeset_union,
        };
        // Sandbox operations
        use simple_runtime::value::{
            rt_sandbox_reset, rt_sandbox_set_cpu_time, rt_sandbox_set_memory, rt_sandbox_set_fd_limit,
            rt_sandbox_set_thread_limit, rt_sandbox_disable_network, rt_sandbox_set_network_allowlist,
            rt_sandbox_set_network_blocklist, rt_sandbox_add_allowed_domain, rt_sandbox_add_blocked_domain,
            rt_sandbox_set_fs_readonly, rt_sandbox_set_fs_restricted, rt_sandbox_set_fs_overlay,
            rt_sandbox_add_read_path, rt_sandbox_add_write_path, rt_sandbox_apply, rt_sandbox_cleanup,
            rt_sandbox_is_configured, rt_sandbox_get_cpu_time, rt_sandbox_get_memory, rt_sandbox_get_network_mode,
            rt_sandbox_get_fs_mode,
        };
        // SIMD vector operations
        use simple_runtime::value::{
            rt_neighbor_load, rt_vec_abs, rt_vec_all, rt_vec_any, rt_vec_blend, rt_vec_ceil, rt_vec_clamp,
            rt_vec_extract, rt_vec_floor, rt_vec_fma, rt_vec_gather, rt_vec_load, rt_vec_masked_load,
            rt_vec_masked_store, rt_vec_max, rt_vec_max_vec, rt_vec_min, rt_vec_min_vec, rt_vec_product, rt_vec_recip,
            rt_vec_round, rt_vec_scatter, rt_vec_select, rt_vec_shuffle, rt_vec_sqrt, rt_vec_store, rt_vec_sum,
            rt_vec_with,
        };
        // NOTE: Parser and compiler operations (rt_parse_simple_file, rt_api_surface_extract,
        // rt_symbol_usage_find) are not included to avoid cyclic dependency
        // (compiler -> native-loader -> compiler).
        use simple_runtime::*;

        match_runtime_symbol!(
            normalized,
            // AOP runtime operations
            rt_aop_invoke_around,
            rt_aop_proceed,
            // Array operations
            rt_array_new,
            rt_array_push,
            rt_array_get,
            rt_array_set,
            rt_array_pop,
            rt_array_first,
            rt_array_clear,
            rt_array_len,
            rt_range,
            rt_range_inclusive,
            // Tuple operations
            rt_tuple_new,
            rt_tuple_set,
            rt_tuple_get,
            rt_tuple_len,
            // Dict operations
            rt_dict_new,
            rt_dict_set,
            rt_dict_get,
            rt_dict_len,
            rt_dict_clear,
            rt_dict_keys,
            rt_dict_remove,
            rt_dict_values,
            // Index/slice operations
            rt_index_get,
            rt_index_set,
            rt_len,
            rt_slice,
            rt_contains,
            // String operations
            rt_string_new,
            rt_string_concat,
            rt_string_len,
            rt_string_data,
            rt_string_char_at,
            rt_string_split,
            rt_string_replace,
            rt_string_trim,
            rt_string_join,
            rt_string_to_upper,
            rt_string_to_lower,
            rt_string_to_int,
            rt_string_find,
            rt_string_rfind,
            rt_string_index_of,
            rt_string_eq,
            rt_string_starts_with,
            rt_string_ends_with,
            // Regex operations
            ffi_regex_is_match,
            ffi_regex_find,
            ffi_regex_find_all,
            ffi_regex_captures,
            ffi_regex_replace,
            ffi_regex_replace_all,
            ffi_regex_split,
            ffi_regex_split_n,
            // SIMD vector operations
            rt_neighbor_load,
            rt_vec_abs,
            rt_vec_all,
            rt_vec_any,
            rt_vec_blend,
            rt_vec_ceil,
            rt_vec_clamp,
            rt_vec_extract,
            rt_vec_floor,
            rt_vec_fma,
            rt_vec_gather,
            rt_vec_load,
            rt_vec_masked_load,
            rt_vec_masked_store,
            rt_vec_max,
            rt_vec_max_vec,
            rt_vec_min,
            rt_vec_min_vec,
            rt_vec_product,
            rt_vec_recip,
            rt_vec_round,
            rt_vec_scatter,
            rt_vec_select,
            rt_vec_shuffle,
            rt_vec_sqrt,
            rt_vec_store,
            rt_vec_sum,
            rt_vec_with,
            // Value creation/conversion
            rt_value_int,
            rt_value_float,
            rt_value_bool,
            rt_value_nil,
            rt_value_as_int,
            rt_value_as_float,
            rt_value_as_bool,
            rt_value_truthy,
            rt_value_is_nil,
            rt_value_is_int,
            rt_value_is_float,
            rt_value_is_bool,
            rt_value_is_heap,
            rt_is_some,
            rt_value_eq,
            rt_native_eq,
            rt_native_neq,
            rt_value_compare,
            // Object operations
            rt_object_new,
            rt_object_field_get,
            rt_object_field_set,
            rt_object_class_id,
            rt_object_field_count,
            // Closure operations
            rt_closure_new,
            rt_closure_set_capture,
            rt_closure_get_capture,
            rt_closure_func_ptr,
            // Enum operations
            rt_enum_new,
            rt_enum_discriminant,
            rt_enum_payload,
            // Raw memory allocation
            rt_alloc,
            rt_free,
            rt_ptr_to_value,
            rt_value_to_ptr,
            // Raw pointer operations
            rt_ptr_read_i64,
            rt_ptr_write_u8,
            rt_ptr_write_i32,
            rt_ptr_write_i64,
            rt_memset,
            rt_memcpy,
            // Async/concurrency operations
            rt_wait,
            rt_future_new,
            rt_future_await,
            rt_thread_spawn_isolated,
            rt_thread_spawn_isolated2,
            rt_thread_join,
            rt_thread_is_done,
            rt_thread_id,
            rt_thread_free,
            rt_thread_available_parallelism,
            rt_thread_sleep,
            rt_thread_yield,
            rt_thread_spawn_limited,
            rt_thread_spawn_limited2,
            rt_thread_join_limited,
            rt_thread_was_killed,
            rt_thread_get_violation_type,
            rt_thread_get_violation_value,
            rt_thread_is_done_limited,
            rt_thread_id_limited,
            rt_thread_free_limited,
            rt_actor_spawn,
            rt_actor_send,
            rt_actor_recv,
            // Generator operations
            rt_generator_new,
            rt_generator_next,
            rt_generator_get_state,
            rt_generator_set_state,
            rt_generator_store_slot,
            rt_generator_load_slot,
            rt_generator_get_ctx,
            rt_generator_mark_done,
            // Interpreter bridge FFI
            rt_interp_call,
            rt_interp_eval,
            // Error handling
            rt_function_not_found,
            rt_method_not_found,
            rt_unwrap_or_self,
            // I/O operations
            rt_print_str,
            rt_println_str,
            rt_eprint_str,
            rt_eprintln_str,
            rt_print_value,
            rt_println_value,
            rt_to_string,
            rt_value_to_string,
            rt_eprint_value,
            rt_eprintln_value,
            rt_capture_stdout_start,
            rt_capture_stderr_start,
            // Environment & Process operations
            rt_env_get,
            rt_env_set,
            rt_get_env,
            rt_set_env,
            rt_env_cwd,
            rt_env_all,
            rt_env_vars,
            rt_env_exists,
            rt_env_remove,
            rt_env_home,
            rt_env_temp,
            rt_exit,
            rt_process_run,
            rt_process_spawn,
            rt_process_execute,
            rt_io_tcp_bind,
            rt_io_tcp_accept,
            rt_io_tcp_accept_timeout,
            rt_io_tcp_connect,
            rt_io_tcp_connect_timeout,
            rt_io_tcp_read,
            rt_io_tcp_read_line,
            rt_io_tcp_write,
            rt_io_tcp_write_text,
            rt_io_tcp_flush,
            rt_io_tcp_close,
            rt_io_tcp_local_addr,
            rt_io_tcp_peer_addr,
            rt_io_tcp_set_nodelay,
            rt_io_tcp_set_read_timeout,
            rt_io_tcp_set_write_timeout,
            rt_io_tcp_shutdown,
            rt_tls_client_close,
            rt_tls_client_config_add_root_cert,
            rt_tls_client_config_enable_sni,
            rt_tls_client_config_free,
            rt_tls_client_config_new,
            rt_tls_client_config_set_alpn,
            rt_tls_client_config_set_verify_mode,
            rt_tls_client_connect,
            rt_tls_client_connect_with_sni,
            rt_tls_client_read,
            rt_tls_client_write,
            rt_tls_free_cert,
            rt_tls_generate_self_signed_cert,
            rt_tls_get_cert_expiry,
            rt_tls_get_cert_issuer,
            rt_tls_get_cert_subject,
            rt_tls_get_cipher_suite,
            rt_tls_get_negotiated_alpn,
            rt_tls_get_peer_cert,
            rt_tls_get_protocol_version,
            rt_tls_hash_cert,
            rt_tls_is_handshake_complete,
            rt_tls_load_cert,
            rt_tls_load_key,
            rt_tls_server_accept,
            rt_tls_server_close_connection,
            rt_tls_server_config_free,
            rt_tls_server_config_new,
            rt_tls_server_config_require_client_cert,
            rt_tls_server_config_set_alpn,
            rt_tls_server_create,
            rt_tls_server_read,
            rt_tls_server_shutdown,
            rt_tls_server_write,
            rt_tls_server_write_bytes,
            rt_tls_verify_cert,
            rt_platform_name,
            rt_term_enable_ansi,
            rt_term_get_size,
            rt_sleep_ms,
            rt_cli_get_args,
            rt_cli_print_help,
            rt_cli_print_version,
            rt_cli_version,
            rt_decision_probe,
            rt_condition_probe,
            rt_path_probe,
            // Runtime configuration
            rt_set_macro_trace,
            rt_is_macro_trace_enabled,
            rt_set_debug_mode,
            rt_is_debug_mode_enabled,
            // File I/O operations - metadata
            rt_file_exists,
            rt_file_stat,
            // File I/O operations - file ops
            rt_file_canonicalize,
            rt_file_read_text,
            rt_file_read_text_rv,
            rt_file_write_text,
            rt_file_copy,
            rt_file_remove,
            rt_file_size,
            rt_file_rename,
            rt_file_read_lines,
            rt_file_append_text,
            rt_file_read_bytes,
            rt_bytes_from_raw,
            rt_bytes_to_text,
            rt_text_to_bytes,
            rt_file_write_bytes,
            rt_file_move,
            rt_sha1_new,
            rt_sha1_write,
            rt_sha1_finish,
            rt_sha1_finish_base64,
            rt_sha1_finish_bytes,
            rt_sha1_reset,
            rt_sha1_free,
            rt_sha256_new,
            rt_sha256_write,
            rt_sha256_finish,
            rt_sha256_finish_bytes,
            rt_sha256_reset,
            rt_sha256_free,
            rt_xxhash_new,
            rt_xxhash_new_with_seed,
            rt_xxhash_write,
            rt_xxhash_finish,
            rt_xxhash_reset,
            rt_xxhash_free,
            // File I/O operations - directory
            rt_dir_create,
            rt_dir_list,
            rt_dir_remove,
            rt_file_find,
            rt_dir_glob,
            rt_dir_create_all,
            rt_dir_walk,
            rt_current_dir,
            rt_set_current_dir,
            rt_dir_remove_all,
            // File I/O operations - descriptor
            rt_file_open,
            rt_file_get_size,
            rt_file_close,
            // File I/O operations - path
            rt_path_basename,
            rt_path_dirname,
            rt_path_ext,
            rt_path_absolute,
            rt_path_separator,
            rt_path_stem,
            rt_path_relative,
            rt_path_join,
            // High-performance collections - HashMap
            rt_hashmap_new,
            rt_hashmap_insert,
            rt_hashmap_get,
            rt_hashmap_contains_key,
            rt_hashmap_remove,
            rt_hashmap_len,
            rt_hashmap_clear,
            rt_hashmap_keys,
            rt_hashmap_values,
            rt_hashmap_entries,
            rt_hashmap_drop,
            // High-performance collections - BTreeMap
            rt_btreemap_new,
            rt_btreemap_insert,
            rt_btreemap_get,
            rt_btreemap_contains_key,
            rt_btreemap_remove,
            rt_btreemap_len,
            rt_btreemap_clear,
            rt_btreemap_keys,
            rt_btreemap_values,
            rt_btreemap_entries,
            rt_btreemap_first_key,
            rt_btreemap_last_key,
            rt_btreemap_drop,
            // High-performance collections - HashSet
            rt_hashset_new,
            rt_hashset_insert,
            rt_hashset_contains,
            rt_hashset_remove,
            rt_hashset_len,
            rt_hashset_clear,
            rt_hashset_to_array,
            rt_hashset_union,
            rt_hashset_intersection,
            rt_hashset_difference,
            rt_hashset_symmetric_difference,
            rt_hashset_is_subset,
            rt_hashset_is_superset,
            rt_hashset_drop,
            // High-performance collections - BTreeSet
            rt_btreeset_new,
            rt_btreeset_insert,
            rt_btreeset_contains,
            rt_btreeset_remove,
            rt_btreeset_len,
            rt_btreeset_clear,
            rt_btreeset_to_array,
            rt_btreeset_first,
            rt_btreeset_last,
            rt_btreeset_union,
            rt_btreeset_intersection,
            rt_btreeset_difference,
            rt_btreeset_symmetric_difference,
            rt_btreeset_is_subset,
            rt_btreeset_is_superset,
            rt_btreeset_drop,
            // Sandbox operations
            rt_sandbox_reset,
            rt_sandbox_set_cpu_time,
            rt_sandbox_set_memory,
            rt_sandbox_set_fd_limit,
            rt_sandbox_set_thread_limit,
            rt_sandbox_disable_network,
            rt_sandbox_set_network_allowlist,
            rt_sandbox_set_network_blocklist,
            rt_sandbox_add_allowed_domain,
            rt_sandbox_add_blocked_domain,
            rt_sandbox_set_fs_readonly,
            rt_sandbox_set_fs_restricted,
            rt_sandbox_set_fs_overlay,
            rt_sandbox_add_read_path,
            rt_sandbox_add_write_path,
            rt_sandbox_apply,
            rt_sandbox_cleanup,
            rt_sandbox_is_configured,
            rt_sandbox_get_cpu_time,
            rt_sandbox_get_memory,
            rt_sandbox_get_network_mode,
            rt_sandbox_get_fs_mode,
        )
    }

    fn symbols(&self) -> &[&'static str] {
        RUNTIME_SYMBOL_NAMES
    }

    fn abi_version(&self) -> AbiVersion {
        AbiVersion::CURRENT
    }

    fn name(&self) -> &str {
        "static"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_static_provider_has_symbols() {
        let provider = StaticSymbolProvider::new();

        // Test some known symbols exist
        assert!(provider.get_symbol("rt_array_new").is_some());
        assert!(provider.get_symbol("_rt_array_new").is_some());
        assert!(provider.get_symbol("rt_println_value").is_some());
        assert!(provider.get_symbol("_rt_println_value").is_some());
        assert!(provider.get_symbol("rt_value_int").is_some());
        assert!(provider.get_symbol("_rt_interp_call").is_some());

        // Test unknown symbol returns None
        assert!(provider.get_symbol("rt_nonexistent").is_none());
    }

    #[test]
    fn test_static_provider_abi_version() {
        let provider = StaticSymbolProvider::new();
        assert_eq!(provider.abi_version(), AbiVersion::CURRENT);
    }

    #[test]
    fn test_static_provider_name() {
        let provider = StaticSymbolProvider::new();
        assert_eq!(provider.name(), "static");
    }
}
