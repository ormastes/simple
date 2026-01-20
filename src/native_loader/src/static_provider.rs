//! Static symbol provider - runtime functions compiled into the binary.
//!
//! This provider has zero runtime lookup cost since all function pointers
//! are resolved at compile time via direct references.

use simple_common::{AbiVersion, RuntimeSymbolProvider, RUNTIME_SYMBOL_NAMES};

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
        use simple_runtime::value::{
            rt_array_clear, rt_capture_stderr_start, rt_capture_stdout_start, rt_condition_probe, rt_contains,
            rt_decision_probe, rt_dict_clear, rt_dict_keys, rt_dict_values, rt_env_all, rt_env_cwd, rt_env_exists,
            rt_env_get, rt_env_home, rt_env_remove, rt_env_set, rt_env_temp, rt_env_vars, rt_eprint_str,
            rt_eprint_value, rt_eprintln_str, rt_eprintln_value, rt_exit, rt_function_not_found, rt_get_env,
            rt_interp_call, rt_interp_eval, rt_is_debug_mode_enabled, rt_is_macro_trace_enabled,
            rt_method_not_found, rt_path_probe, rt_platform_name, rt_print_str, rt_print_value, rt_println_str,
            rt_println_value, rt_process_execute, rt_process_run, rt_process_spawn, rt_set_debug_mode,
            rt_set_env, rt_set_macro_trace, rt_value_eq,
        };
        // File I/O operations
        use simple_runtime::value::{
            rt_file_exists, rt_file_stat, rt_file_canonicalize, rt_file_read_text, rt_file_write_text,
            rt_file_copy, rt_file_remove, rt_file_rename, rt_dir_create, rt_dir_list, rt_dir_remove,
            rt_file_find, rt_dir_glob, rt_file_open, rt_file_get_size, rt_file_close,
            rt_path_basename, rt_path_dirname, rt_path_ext, rt_path_absolute, rt_path_separator,
        };
        // Regex operations
        use simple_runtime::value::{
            ffi_regex_captures, ffi_regex_find, ffi_regex_find_all, ffi_regex_is_match,
            ffi_regex_replace, ffi_regex_replace_all, ffi_regex_split, ffi_regex_split_n,
        };
        use simple_runtime::*;

        match_runtime_symbol!(
            name,
            // AOP runtime operations
            rt_aop_invoke_around,
            rt_aop_proceed,
            // Array operations
            rt_array_new,
            rt_array_push,
            rt_array_get,
            rt_array_set,
            rt_array_pop,
            rt_array_clear,
            rt_array_len,
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
            rt_dict_values,
            // Index/slice operations
            rt_index_get,
            rt_index_set,
            rt_slice,
            rt_contains,
            // String operations
            rt_string_new,
            rt_string_concat,
            rt_string_len,
            rt_string_data,
            // Regex operations
            ffi_regex_is_match,
            ffi_regex_find,
            ffi_regex_find_all,
            ffi_regex_captures,
            ffi_regex_replace,
            ffi_regex_replace_all,
            ffi_regex_split,
            ffi_regex_split_n,
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
            rt_value_eq,
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
            // Async/concurrency operations
            rt_wait,
            rt_future_new,
            rt_future_await,
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
            // I/O operations
            rt_print_str,
            rt_println_str,
            rt_eprint_str,
            rt_eprintln_str,
            rt_print_value,
            rt_println_value,
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
            rt_platform_name,
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
            rt_file_write_text,
            rt_file_copy,
            rt_file_remove,
            rt_file_rename,
            // File I/O operations - directory
            rt_dir_create,
            rt_dir_list,
            rt_dir_remove,
            rt_file_find,
            rt_dir_glob,
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
        assert!(provider.get_symbol("rt_println_value").is_some());
        assert!(provider.get_symbol("rt_value_int").is_some());

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
