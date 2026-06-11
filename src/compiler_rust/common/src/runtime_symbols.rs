//! Runtime symbol resolution abstraction.
//!
//! Provides a unified interface for resolving runtime SFFI symbols,
//! supporting both static linking (compiled into binary) and dynamic
//! loading (.so/.dylib/.dll).

/// Runtime ABI version for compatibility checking.
///
/// Uses semantic versioning where:
/// - `major`: Breaking changes (signature changes, removed symbols)
/// - `minor`: Additive changes (new symbols only)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbiVersion {
    pub major: u16,
    pub minor: u16,
}

impl AbiVersion {
    /// Current ABI version of the runtime.
    pub const CURRENT: Self = Self { major: 1, minor: 4 };

    /// Create a new ABI version.
    pub const fn new(major: u16, minor: u16) -> Self {
        Self { major, minor }
    }

    /// Check if this version is compatible with the required version.
    ///
    /// Compatible means:
    /// - Same major version (no breaking changes)
    /// - Same or higher minor version (additive changes OK)
    pub fn is_compatible_with(&self, required: &AbiVersion) -> bool {
        self.major == required.major && self.minor >= required.minor
    }

    /// Create from a packed u32 representation.
    pub fn from_u32(v: u32) -> Self {
        Self {
            major: (v >> 16) as u16,
            minor: (v & 0xFFFF) as u16,
        }
    }

    /// Convert to a packed u32 representation.
    pub fn to_u32(&self) -> u32 {
        ((self.major as u32) << 16) | (self.minor as u32)
    }
}

impl std::fmt::Display for AbiVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.major, self.minor)
    }
}

impl Default for AbiVersion {
    fn default() -> Self {
        Self::CURRENT
    }
}

/// Trait for resolving runtime SFFI symbols.
///
/// This trait abstracts over different symbol resolution strategies:
/// - `StaticSymbolProvider`: Compiled-in function pointers (zero runtime cost)
/// - `DynamicSymbolProvider`: Loaded from shared library (.so/.dylib/.dll)
/// - `ChainedProvider`: Multiple providers, first match wins (plugin support)
pub trait RuntimeSymbolProvider: Send + Sync {
    /// Get function pointer for a runtime symbol by name.
    ///
    /// Returns `None` if the symbol is not found.
    fn get_symbol(&self, name: &str) -> Option<*const u8>;

    /// Check if a symbol exists without retrieving it.
    fn has_symbol(&self, name: &str) -> bool {
        self.get_symbol(name).is_some()
    }

    /// Get list of all available symbol names.
    fn symbols(&self) -> &[&'static str];

    /// Get the ABI version of this provider.
    fn abi_version(&self) -> AbiVersion;

    /// Get the provider name (for logging/debugging).
    fn name(&self) -> &str;
}

/// Runtime symbol tier, matching the standard library hierarchy.
///
/// Used to filter which runtime symbols are available for a given target
/// configuration (e.g., baremetal targets only get Core + Alloc).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeSymbolTier {
    /// Tier 0: Value types, enums, errors, contracts — no alloc, no OS
    Core,
    /// Tier 1: Collections, strings, objects, closures, pointers, memory
    Alloc,
    /// Tier 2: I/O, files, env, process, networking, regex, sandbox, CLI
    Sys,
    /// Tier 3: Futures, actors, channels, executor, threads, generators
    Async,
    /// Tier 4: SIMD, GPU, Vulkan, Cranelift self-hosting
    Ext,
}

/// Runtime ABI classification used by native lane selection.
///
/// `CoreRequired` is the narrow ABI that a `simple-core` archive must provide
/// before automatic native-build selection can prefer that lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeSymbolClass {
    CoreRequired,
    HostedOnly,
    Unported,
}

pub const CORE_REQUIRED_RUNTIME_SYMBOLS: &[&str] = &[
    "__simple_runtime_init",
    "__simple_runtime_shutdown",
    "rt_alloc",
    "rt_free",
    "rt_realloc",
    "rt_memcpy",
    "rt_memset",
    "rt_array_new",
    "rt_byte_array_new",
    "rt_byte_array_new_len",
    "rt_array_get",
    "rt_array_get_text",
    "rt_array_data_ptr_text",
    "rt_array_data_ptr_u8",
    "rt_array_set",
    "rt_array_set_text",
    "rt_array_set_len_known_text",
    "rt_array_push",
    "rt_array_pop",
    "rt_array_len",
    "rt_bytes_u32_le_at",
    "rt_bytes_u64_le_at",
    "rt_typed_bytes_u8_push",
    "rt_typed_words_u32_at",
    "rt_typed_words_u32_push",
    "rt_typed_words_u32_set",
    "rt_string_new",
    "rt_string_len",
    "rt_string_data",
    "rt_string_concat",
    "rt_len",
    "rt_to_string",
    "rt_str_hash",
    "rt_native_eq",
    "rt_native_neq",
    "rt_slice",
    "rt_string_starts_with",
    "rt_string_ends_with",
    "rt_string_replace",
    "rt_string_trim",
    "rt_string_to_int",
    "stdin_read_char",
    "print_raw",
    "rt_stdout_write",
    "rt_stdout_flush",
    "rt_stderr_write",
    "rt_stderr_flush",
    "rt_exit",
    "rt_time_now_unix",
    "rt_time_now_nanos",
    "rt_time_now_micros",
    "rt_time_now_unix_micros",
    "rt_entropy_hardware_ready",
    "rt_sleep_ms",
    "rt_value_int",
    "rt_value_float",
    "rt_value_bool",
    "rt_value_nil",
    "rt_panic",
];

pub fn symbol_class_of(name: &str) -> RuntimeSymbolClass {
    if CORE_REQUIRED_RUNTIME_SYMBOLS.contains(&name) {
        return RuntimeSymbolClass::CoreRequired;
    }
    match symbol_tier_of(name) {
        RuntimeSymbolTier::Sys | RuntimeSymbolTier::Async | RuntimeSymbolTier::Ext => RuntimeSymbolClass::HostedOnly,
        RuntimeSymbolTier::Core | RuntimeSymbolTier::Alloc => RuntimeSymbolClass::Unported,
    }
}

/// Classify a runtime symbol name into its tier.
pub fn symbol_tier_of(name: &str) -> RuntimeSymbolTier {
    use RuntimeSymbolTier::*;

    // Tier 4: Ext
    if name.starts_with("rt_vec_")
        || name.starts_with("rt_simd_")
        || name.starts_with("rt_numeric_")
        || name.starts_with("rt_aes_")
        || name.starts_with("rt_aes128_")
        || name.starts_with("rt_tls13_")
        || name.starts_with("rt_neighbor_load")
        || name.starts_with("rt_gpu_")
        || name.starts_with("rt_cuda_")
        || name.starts_with("rt_vk_")
        || name.starts_with("rt_metal_")
        || name.starts_with("rt_cranelift_")
        || name.starts_with("rt_par_")
    {
        return Ext;
    }

    // Tier 3: Async
    if name.starts_with("rt_future_")
        || name.starts_with("rt_async_")
        || name.starts_with("rt_actor_")
        || name.starts_with("rt_channel_")
        || name.starts_with("rt_executor_")
        || name.starts_with("rt_thread_")
        || name.starts_with("rt_generator_")
        || name == "rt_wait"
    {
        return Async;
    }

    // Tier 2: Sys
    if name.starts_with("rt_print_")
        || name.starts_with("rt_println_")
        || name.starts_with("rt_eprint_")
        || name.starts_with("rt_eprintln_")
        || name.starts_with("rt_capture_")
        || name.starts_with("rt_env_")
        || name.starts_with("rt_get_env")
        || name.starts_with("rt_set_env")
        || name.starts_with("rt_get_args")
        || name.starts_with("rt_platform_name")
        || name.starts_with("rt_term_enable_ansi")
        || name.starts_with("rt_term_get_size")
        || name.starts_with("rt_exit")
        || name.starts_with("rt_file_")
        || name.starts_with("rt_dir_")
        || name.starts_with("rt_path_")
        || name.starts_with("rt_current_dir")
        || name.starts_with("rt_set_current_dir")
        || name.starts_with("rt_process_")
        || name.starts_with("rt_pty_")
        || name.starts_with("rt_exec")
        || name.starts_with("rt_write_file")
        || name.starts_with("rt_getpid")
        || name.starts_with("rt_hostname")
        || name.starts_with("rt_system_")
        || name.starts_with("rt_time_")
        || name.starts_with("sffi_regex_")
        || name.starts_with("rt_sdn_")
        || name.starts_with("rt_sandbox_")
        || name.starts_with("rt_security_")
        || name.starts_with("rt_coverage_")
        || name.starts_with("rt_decision_probe")
        || name.starts_with("rt_condition_probe")
        || name.starts_with("rt_path_probe")
        || name.starts_with("rt_bdd_")
        || name.starts_with("rt_cli_")
        || name.starts_with("rt_fault_")
        || name.starts_with("rt_interp_")
        || name.starts_with("rt_set_macro_trace")
        || name.starts_with("rt_is_macro_trace")
        || name.starts_with("rt_set_debug_mode")
        || name.starts_with("rt_is_debug_mode")
        || name.starts_with("rt_settlement_")
        || name.starts_with("rt_context_")
        || name.starts_with("rt_test_")
        || name.starts_with("rt_sffi_")
        || name.starts_with("rt_random_")
        || name.starts_with("rt_rsa_")
        || name.starts_with("rt_ed25519_")
        || name.starts_with("rt_ecdsa_")
        || name.starts_with("rt_dh_")
        || name.starts_with("doctest_")
        || name.starts_with("native_tcp_")
        || name.starts_with("native_udp_")
        || name.starts_with("native_http_")
    {
        return Sys;
    }

    // Tier 1: Alloc
    if name.starts_with("rt_array_")
        || name.starts_with("rt_tuple_")
        || name.starts_with("rt_db_table_")
        || name.starts_with("rt_db_put")
        || name.starts_with("rt_db_get")
        || name.starts_with("rt_db_scan")
        || name.starts_with("rt_db_delete")
        || name.starts_with("rt_db_row_")
        || name.starts_with("rt_db_col_")
        || name.starts_with("rt_dict_")
        || name.starts_with("rt_index_")
        || name.starts_with("rt_slice")
        || name.starts_with("rt_contains")
        || name.starts_with("rt_len")
        || name.starts_with("rt_string_")
        || name.starts_with("rt_utf8_")
        || name == "rt_text_count_codepoints"
        || name.starts_with("rt_swi_")
        || name.starts_with("rt_rank_")
        || name == "rt_select_query"
        || name.starts_with("rt_to_string")
        || name == "rt_raw_u64_to_string"
        || name.starts_with("rt_cstring_to_text")
        || name.starts_with("rt_object_")
        || name.starts_with("rt_closure_")
        || name.starts_with("rt_unique_")
        || name.starts_with("rt_shared_")
        || name.starts_with("rt_weak_")
        || name.starts_with("rt_handle_")
        || name.starts_with("rt_hashmap_")
        || name.starts_with("rt_btreemap_")
        || name.starts_with("rt_hashset_")
        || name.starts_with("rt_btreeset_")
        || name.starts_with("rt_alloc")
        || name.starts_with("rt_free")
        || name.starts_with("rt_ptr_to_value")
        || name.starts_with("rt_value_to_ptr")
    {
        return Alloc;
    }

    // Tier 0: Core
    Core
}

/// Get runtime symbol names filtered for a given target.
///
/// Baremetal targets only get Core + Alloc symbols.
pub fn runtime_symbols_for_baremetal(is_baremetal: bool) -> Vec<&'static str> {
    RUNTIME_SYMBOL_NAMES
        .iter()
        .copied()
        .filter(|name| match symbol_tier_of(name) {
            RuntimeSymbolTier::Core | RuntimeSymbolTier::Alloc => true,
            RuntimeSymbolTier::Sys | RuntimeSymbolTier::Async => !is_baremetal,
            RuntimeSymbolTier::Ext => true,
        })
        .collect()
}

/// List of all runtime SFFI symbols.
///
/// These are the extern "C" functions exported by the runtime library
/// that can be called from compiled Simple code.
pub const RUNTIME_SYMBOL_NAMES: &[&str] = &[
    // AOP runtime operations
    "rt_aop_invoke_around",
    "rt_aop_proceed",
    // Array operations
    "rt_array_new",
    "rt_byte_array_new",
    "rt_byte_array_new_len",
    "rt_array_push",
    "rt_array_get",
    "rt_array_get_text",
    "rt_array_data_ptr_text",
    "rt_array_data_ptr_u8",
    "rt_array_set",
    "rt_array_set_text",
    "rt_array_set_len_known_text",
    "rt_bytes_u8_at",
    "rt_bytes_u32_le_at",
    "rt_bytes_u64_le_at",
    "rt_typed_bytes_u8_push",
    "rt_typed_words_u32_at",
    "rt_typed_words_u32_push",
    "rt_typed_words_u32_set",
    "rt_array_pop",
    "rt_array_first",
    "rt_array_clear",
    "rt_array_len",
    "rt_range",
    "rt_range_inclusive",
    // Tuple operations
    "rt_tuple_new",
    "rt_tuple_set",
    "rt_tuple_get",
    "rt_tuple_len",
    // Dict operations
    "rt_dict_new",
    "rt_dict_set",
    "rt_dict_get",
    "rt_dict_len",
    "rt_dict_clear",
    "rt_dict_keys",
    "rt_dict_values",
    // for-in iteration over dicts/arrays (cranelift for-loop lowering)
    "rt_dict_entries",
    "rt_for_iterable",
    // Fast DB operations (runtime_db.c)
    "rt_db_table_create",
    "rt_db_table_destroy",
    "rt_db_put",
    "rt_db_put_value_int",
    "rt_db_put_value_text",
    "rt_db_get",
    "rt_db_get_int",
    "rt_db_get_text",
    "rt_db_scan_range",
    "rt_db_scan_result",
    "rt_db_delete",
    "rt_db_row_count",
    "rt_db_col_count",
    // Batched DB operations (reduce extern call overhead)
    "rt_db_put_row3",
    "rt_db_get_int_by_pk",
    "rt_db_update_int",
    "rt_db_update_text",
    // Hosted linalg matrix-handle ABI.
    "__simple_runtime_matrix_f64_new",
    "__simple_runtime_matrix_f64_free",
    "__simple_runtime_matrix_f64_rows",
    "__simple_runtime_matrix_f64_cols",
    "__simple_runtime_matrix_f64_get",
    "__simple_runtime_gemm_add",
    // Integer-PK DB operations (zero string alloc from caller)
    "rt_db_iput3",
    "rt_db_iget_int",
    "rt_db_iupdate_int",
    "rt_db_idelete",
    // Index/slice operations
    "rt_index_get",
    "rt_index_set",
    "rt_slice",
    "rt_contains",
    // String operations
    "rt_string_new",
    "rt_string_concat",
    "rt_string_len",
    "rt_string_data",
    "rt_cstring_to_text",
    "rt_string_char_at",
    "rt_string_split",
    "rt_string_replace",
    "rt_string_trim",
    "rt_string_join",
    "rt_string_to_upper",
    "rt_string_to_lower",
    "rt_string_to_int",
    "rt_string_find",
    "rt_string_rfind",
    "rt_string_index_of",
    "rt_string_eq",
    "rt_string_starts_with",
    "rt_string_ends_with",
    "rt_utf8_count_codepoints",
    "rt_utf8_validate",
    "rt_utf8_find_invalid",
    "rt_text_count_codepoints",
    "rt_swi_build",
    "rt_swi_char_to_byte",
    "rt_swi_byte_to_char",
    "rt_swi_free",
    "rt_rank_select_build",
    "rt_rank_query",
    "rt_select_query",
    "rt_rank_select_free",
    "rt_hash_text",
    // Regex operations
    "sffi_regex_is_match",
    "sffi_regex_find",
    "sffi_regex_find_all",
    "sffi_regex_captures",
    "sffi_regex_replace",
    "sffi_regex_replace_all",
    "sffi_regex_split",
    "sffi_regex_split_n",
    // Value creation/conversion
    "rt_value_int",
    "rt_value_float",
    "rt_value_bool",
    "rt_value_nil",
    // Object operations
    "rt_object_new",
    "rt_object_field_get",
    "rt_object_field_set",
    // Closure operations
    "rt_closure_new",
    "rt_closure_set_capture",
    "rt_closure_get_capture",
    "rt_closure_func_ptr",
    // Enum operations
    "rt_enum_check_discriminant",
    "rt_enum_new",
    "rt_enum_discriminant",
    "rt_enum_payload",
    // Raw memory allocation
    "rt_alloc",
    "rt_free",
    "rt_ptr_to_value",
    "rt_value_to_ptr",
    // Raw pointer operations
    "rt_ptr_read_i64",
    "rt_ptr_write_u8",
    "rt_ptr_write_i32",
    "rt_ptr_write_i64",
    "rt_dyn_torch_tensor_from_bits_1d",
    "rt_memset",
    "rt_memcpy",
    // Async/concurrency operations
    "rt_wait",
    "rt_future_new",
    "rt_future_await",
    "rt_thread_spawn_isolated",
    "rt_thread_spawn_isolated_with_args",
    "rt_pool_submit",
    "rt_pool_join",
    "rt_pool_is_done",
    "rt_pool_set_parallelism",
    "rt_pool_get_parallelism",
    "rt_pool_uses_global_fifo_queue",
    "rt_pool_uses_work_stealing",
    "rt_thread_join",
    "rt_thread_is_done",
    "rt_thread_id",
    "rt_thread_free",
    "rt_thread_available_parallelism",
    "spl_thread_cpu_count",
    "rt_thread_sleep",
    "rt_thread_yield",
    "rt_thread_spawn_limited",
    "rt_thread_spawn_limited_with_args",
    "rt_thread_join_limited",
    "rt_thread_was_killed",
    "rt_thread_get_violation_type",
    "rt_thread_get_violation_value",
    "rt_thread_is_done_limited",
    "rt_thread_id_limited",
    "rt_thread_free_limited",
    "rt_actor_spawn",
    "rt_actor_send",
    "rt_actor_recv",
    // Generator operations
    "rt_generator_new",
    "rt_generator_next",
    "rt_generator_get_state",
    "rt_generator_set_state",
    "rt_generator_store_slot",
    "rt_generator_load_slot",
    "rt_generator_get_ctx",
    "rt_generator_mark_done",
    // Interpreter bridge SFFI
    "rt_interp_call",
    "rt_interp_eval",
    // Error handling
    "rt_function_not_found",
    "rt_method_not_found",
    // I/O operations
    "rt_print_str",
    "rt_println_str",
    "rt_eprint_str",
    "rt_eprintln_str",
    "rt_stdout_write",
    "rt_stdout_flush",
    "rt_stderr_write",
    "rt_stderr_flush",
    "rt_print_value",
    "rt_println_value",
    "rt_eprint_value",
    "rt_eprintln_value",
    "rt_capture_stdout_start",
    "rt_capture_stderr_start",
    // Environment & Process operations
    "rt_env_get",
    "rt_env_get_i64",
    "rt_env_set",
    "rt_get_env",
    "rt_set_env",
    "rt_env_cwd",
    "rt_env_all",
    "rt_env_vars",
    "rt_env_exists",
    "rt_env_remove",
    "rt_env_home",
    "rt_env_temp",
    "rt_exit",
    "rt_process_run",
    "rt_process_spawn",
    "rt_process_spawn_async",
    "rt_process_is_running",
    "rt_process_wait",
    "rt_process_kill",
    "rt_process_execute",
    "rt_pty_open",
    "rt_pty_spawn",
    "rt_io_tcp_bind",
    "rt_io_tcp_accept",
    "rt_io_tcp_accept_timeout",
    "rt_io_tcp_connect",
    "rt_io_tcp_connect_timeout",
    "rt_dns_lookup",
    "rt_io_tcp_read",
    "rt_io_tcp_read_exact",
    "rt_io_tcp_read_exact_len",
    "rt_io_tcp_read_line",
    "rt_io_tcp_drain_line",
    "rt_io_tcp_write",
    "rt_io_tcp_write_text",
    "rt_io_tcp_write_text_read_exact_len",
    "rt_io_tcp_flush",
    "rt_io_tcp_close",
    "rt_io_tcp_local_addr",
    "rt_io_tcp_peer_addr",
    "rt_io_tcp_set_nodelay",
    "rt_io_tcp_set_read_timeout",
    "rt_io_tcp_set_write_timeout",
    "rt_io_tcp_shutdown",
    "rt_tls_client_connect",
    "rt_tls_client_connect_with_sni",
    "rt_tls_client_write",
    "rt_tls_client_read",
    "rt_tls_client_close",
    "rt_tls_get_protocol_version",
    "rt_platform_name",
    "rt_term_enable_ansi",
    "rt_term_get_size",
    "rt_terminal_get_size",
    "rt_terminal_enable_raw_mode",
    "rt_terminal_disable_raw_mode",
    "rt_stdin_read_byte",
    "rt_cli_get_args",
    "rt_cli_print_help",
    "rt_cli_print_version",
    "rt_cli_version",
    "rt_cli_dispatch_rust",
    "rt_cli_exit",
    "rt_cli_file_exists",
    "rt_cli_read_file",
    "rt_cli_watch_file",
    "rt_cli_handle_compile",
    "rt_cli_handle_run",
    "rt_cli_handle_web",
    "rt_cli_handle_diagram",
    "rt_cli_handle_linkers",
    "rt_cli_run_file",
    "rt_cli_run_code",
    "rt_cli_run_repl",
    "rt_cli_run_tests",
    "rt_cli_run_verify",
    "rt_cli_run_check",
    "rt_cli_run_lint",
    "rt_cli_run_fmt",
    "rt_cli_run_fix",
    "rt_cli_run_lex",
    "rt_cli_run_migrate",
    "rt_cli_run_query",
    "rt_cli_run_sffi_gen",
    "rt_cli_run_gen_lean",
    "rt_compile_to_native",
    "rt_compile_to_native_with_opt",
    "rt_compile_to_llvm_ir",
    "rt_decision_probe",
    "rt_condition_probe",
    "rt_path_probe",
    "rt_simd_has_sse",
    "rt_simd_has_avx",
    "rt_simd_has_avx2",
    "rt_simd_has_neon",
    "rt_simd_has_rvv",
    "rt_simd_fill_row_u32",
    "rt_simd_copy_row_u32",
    "rt_simd_engine2d_neon_hits",
    "rt_simd_engine2d_neon_reset",
    "rt_simd_detect_profile",
    "rt_simd_profile_name",
    // Phase 1 SIMD int bitwise / shift externs.
    "rt_simd_xor_i32x4",
    "rt_simd_and_i32x4",
    "rt_simd_or_i32x4",
    "rt_simd_shl_i32x4",
    "rt_simd_shr_i32x4",
    "rt_simd_xor_i32x8",
    "rt_simd_and_i32x8",
    "rt_simd_or_i32x8",
    "rt_simd_shl_i32x8",
    "rt_simd_shr_i32x8",
    // Phase 2 seed — Vec16u8 byte ops.
    "rt_simd_add_u8x16",
    // Phase 2 — AES-NI / NEON / scalar AES round intrinsics.
    "rt_simd_aes_round_u8x16",
    "rt_simd_aes_round_last_u8x16",
    "rt_simd_str_search",
    "rt_simd_str_last_index_of",
    "rt_simd_str_equal",
    "rt_engine2d_simd_fill_u32",
    "rt_engine2d_simd_copy_u32",
    "rt_engine2d_simd_fill_row_u32",
    "rt_engine2d_simd_copy_row_u32",
    "rt_engine2d_simd_blend_row_u32",
    "rt_opencl_is_available",
    "rt_opencl_platform_count",
    "rt_opencl_create_context",
    "rt_opencl_create_queue",
    "rt_opencl_create_program",
    "rt_opencl_build_program",
    "rt_opencl_create_kernel",
    "rt_opencl_mem_alloc",
    "rt_opencl_mem_free",
    "rt_opencl_write_buffer",
    "rt_opencl_read_buffer",
    "rt_opencl_set_kernel_arg_i64",
    "rt_opencl_set_kernel_arg_buffer",
    "rt_opencl_enqueue_ndrange",
    "rt_opencl_finish",
    "rt_opencl_release_kernel",
    "rt_opencl_release_program",
    "rt_opencl_release_queue",
    "rt_opencl_release_context",
    "rt_text_to_lower_ascii",
    "rt_text_to_upper_ascii",
    "rt_numeric_active_simd_tier",
    "rt_numeric_add_f32",
    "rt_numeric_mul_f32",
    "rt_numeric_fma_f32",
    "rt_numeric_dot_f32",
    "rt_numeric_sum_f32",
    "rt_numeric_min_f32",
    "rt_numeric_max_f32",
    "rt_numeric_add_f64",
    "rt_numeric_mul_f64",
    "rt_numeric_fma_f64",
    "rt_numeric_sum_f64",
    "rt_numeric_dot_f64",
    "rt_numeric_xor_sum_u64",
    "rt_numeric_contains_u64",
    "rt_aes_encrypt_block_with_expanded",
    "rt_aes_decrypt_block_with_expanded",
    "rt_aes_sbox",
    "rt_aes_rcon",
    "rt_aes128_encrypt_block_into",
    "rt_aes128_encrypt_block_pure",
    "rt_aes128_decrypt_block_pure",
    "rt_tls13_sha256",
    "rt_tls13_hkdf_extract",
    "rt_tls13_hkdf_extract_into",
    "rt_tls13_hkdf_expand_into",
    "rt_tls13_hkdf_expand_label",
    "rt_tls13_hkdf_expand_label_into",
    "rt_tls13_hkdf_expand_label_derived",
    "rt_tls13_hkdf_expand_label_key",
    "rt_tls13_hkdf_expand_label_iv",
    "rt_tls13_hkdf_expand_label_finished",
    "rt_tls13_hkdf_expand_label_client_hs",
    "rt_tls13_hkdf_expand_label_server_hs",
    "rt_tls13_hkdf_expand_label_client_app",
    "rt_tls13_hkdf_expand_label_server_app",
    "rt_tls13_aes128_gcm_encrypt",
    // Runtime configuration
    "rt_set_macro_trace",
    "rt_is_macro_trace_enabled",
    "rt_set_debug_mode",
    "rt_is_debug_mode_enabled",
    // File I/O operations - metadata
    "rt_file_exists",
    "rt_file_stat",
    // File I/O operations - file ops
    "rt_file_canonicalize",
    "rt_file_read_text",
    "rt_file_read_text_rv",
    "rt_file_write_text",
    "rt_file_fsync",
    "rt_file_fsync_cached",
    "rt_file_copy",
    "rt_file_remove",
    "rt_file_size",
    "rt_file_hash_sha256",
    "rt_file_lock",
    "rt_file_unlock",
    "rt_file_rename",
    "rt_file_read_lines",
    "rt_file_append_text",
    "rt_file_read_bytes",
    "rt_file_mmap_read_text",
    "rt_file_mmap_len",
    "rt_file_mmap_read_text_rv",
    "rt_file_mmap_read_bytes",
    "rt_file_mmap_read_bytes_rv",
    "rt_file_read_text_at",
    "rt_file_write_text_at",
    "rt_file_write_text_at_cached",
    "rt_file_write_text_at_cached_repeat",
    "rt_bytes_from_raw",
    "rt_simple_sandbox_section_start",
    "rt_simple_sandbox_section_end",
    "rt_bytes_to_text",
    "rt_text_to_bytes",
    "rt_file_write_bytes",
    "rt_file_wrap_smf_dynlib",
    "rt_file_extract_smf_dynlib",
    "rt_file_move",
    "rt_mmap",
    "rt_munmap",
    "rt_madvise",
    "rt_msync",
    // Async I/O driver
    "rt_driver_create",
    "rt_driver_destroy",
    "rt_driver_submit_accept",
    "rt_driver_submit_connect",
    "rt_driver_submit_recv",
    "rt_driver_submit_send",
    "rt_driver_submit_sendfile",
    "rt_driver_submit_read",
    "rt_driver_submit_write",
    "rt_driver_submit_open",
    "rt_driver_submit_close",
    "rt_driver_submit_fsync",
    "rt_driver_submit_timeout",
    "rt_driver_flush",
    "rt_driver_poll",
    "rt_driver_poll_id",
    "rt_driver_poll_result",
    "rt_driver_poll_flags",
    "rt_driver_poll_data",
    "rt_driver_poll_data_len",
    "rt_driver_cancel",
    "rt_driver_backend_name",
    "rt_driver_supports_sendfile",
    "rt_driver_supports_zero_copy",
    // Random operations
    "rt_random_hex",
    // Hash operations
    "rt_sha1_new",
    "rt_sha1_write",
    "rt_sha1_finish",
    "rt_sha1_finish_base64",
    "rt_sha1_finish_bytes",
    "rt_sha1_reset",
    "rt_sha1_free",
    "rt_sha256_new",
    "rt_sha256_write",
    "rt_sha256_finish",
    "rt_sha256_finish_bytes",
    "rt_sha256_reset",
    "rt_sha256_free",
    "rt_xxhash_new",
    "rt_xxhash_new_with_seed",
    "rt_xxhash_write",
    "rt_xxhash_finish",
    "rt_xxhash_reset",
    "rt_xxhash_free",
    // File I/O operations - directory
    "rt_dir_create",
    "rt_dir_list",
    "rt_dir_remove",
    "rt_file_find",
    "rt_dir_glob",
    "rt_dir_create_all",
    "rt_dir_walk",
    "rt_current_dir",
    "rt_set_current_dir",
    "rt_dir_remove_all",
    // File I/O operations - descriptor
    "rt_file_open",
    "rt_file_get_size",
    "rt_file_close",
    // File I/O operations - path
    "rt_path_basename",
    "rt_path_dirname",
    "rt_path_ext",
    "rt_path_absolute",
    "rt_path_separator",
    "rt_path_stem",
    "rt_path_relative",
    "rt_path_join",
    // File locking
    "rt_file_lock",
    "rt_file_unlock",
    // System info
    "rt_getpid",
    "rt_process_exists",
    "rt_hostname",
    "rt_system_cpu_count",
    "rt_time_now_monotonic_ms",
    // High-performance collections (HashMap)
    "rt_hashmap_new",
    "rt_hashmap_insert",
    "rt_hashmap_get",
    "rt_hashmap_contains_key",
    "rt_hashmap_remove",
    "rt_hashmap_len",
    "rt_hashmap_clear",
    "rt_hashmap_keys",
    "rt_hashmap_values",
    "rt_hashmap_entries",
    "rt_hashmap_drop",
    // High-performance collections (BTreeMap)
    "rt_btreemap_new",
    "rt_btreemap_insert",
    "rt_btreemap_get",
    "rt_btreemap_contains_key",
    "rt_btreemap_remove",
    "rt_btreemap_len",
    "rt_btreemap_clear",
    "rt_btreemap_keys",
    "rt_btreemap_values",
    "rt_btreemap_entries",
    "rt_btreemap_first_key",
    "rt_btreemap_last_key",
    "rt_btreemap_drop",
    // High-performance collections (HashSet)
    "rt_hashset_new",
    "rt_hashset_insert",
    "rt_hashset_contains",
    "rt_hashset_remove",
    "rt_hashset_len",
    "rt_hashset_clear",
    "rt_hashset_to_array",
    "rt_hashset_union",
    "rt_hashset_intersection",
    "rt_hashset_difference",
    "rt_hashset_symmetric_difference",
    "rt_hashset_is_subset",
    "rt_hashset_is_superset",
    "rt_hashset_drop",
    // High-performance collections (BTreeSet)
    "rt_btreeset_new",
    "rt_btreeset_insert",
    "rt_btreeset_contains",
    "rt_btreeset_remove",
    "rt_btreeset_len",
    "rt_btreeset_clear",
    "rt_btreeset_to_array",
    "rt_btreeset_first",
    "rt_btreeset_last",
    "rt_btreeset_union",
    "rt_btreeset_intersection",
    "rt_btreeset_difference",
    "rt_btreeset_symmetric_difference",
    "rt_btreeset_is_subset",
    "rt_btreeset_is_superset",
    "rt_btreeset_drop",
    // Sandbox operations (Phase 13)
    "rt_sandbox_reset",
    "rt_sandbox_set_cpu_time",
    "rt_sandbox_set_memory",
    "rt_sandbox_set_fd_limit",
    "rt_sandbox_set_thread_limit",
    "rt_sandbox_disable_network",
    "rt_sandbox_set_network_allowlist",
    "rt_sandbox_set_network_blocklist",
    "rt_sandbox_add_allowed_domain",
    "rt_sandbox_add_blocked_domain",
    "rt_sandbox_set_fs_readonly",
    "rt_sandbox_set_fs_restricted",
    "rt_sandbox_set_fs_overlay",
    "rt_sandbox_add_read_path",
    "rt_sandbox_add_write_path",
    "rt_sandbox_apply",
    "rt_sandbox_cleanup",
    "rt_sandbox_is_configured",
    "rt_sandbox_get_cpu_time",
    "rt_sandbox_get_memory",
    "rt_sandbox_get_network_mode",
    "rt_sandbox_get_fs_mode",
    // Security gate AOP runtime operations
    "rt_security_enter_gate",
    "rt_security_exit_gate",
    "rt_security_require_policy",
    "rt_security_enter_sandbox",
    "rt_security_exit_sandbox",
    "rt_security_audit_start",
    "rt_security_audit_success",
    "rt_security_audit_failure",
    "rt_security_reset_counters",
    "rt_security_gate_depth",
    "rt_security_policy_checks",
    "rt_security_audit_events",
    "rt_security_last_gate_id",
    "rt_security_last_policy_id",
    "rt_security_last_sandbox_id",
    "rt_security_last_audit_id",
    "rt_security_load_registry_sdn",
    "rt_security_loaded_registry_entries",
    "rt_security_register_policy",
    "rt_security_policy_allowed",
    "rt_security_register_sandbox",
    "rt_security_sandbox_registered",
    "rt_security_host_import_allowed",
    "rt_security_last_host_import_allowed",
    "rt_security_host_import_denials",
    "rt_to_string",
    "rt_raw_u64_to_string",
    "rt_value_to_string",
    "rt_value_eq",
    "rt_native_eq",
    "rt_native_neq",
    "rt_value_compare",
    "rt_value_truthy",
    // Signature verification (RSA-SHA256/512, Ed25519, ECDSA-P256) for SSH host keys
    "rt_rsa_sha256_verify",
    "rt_rsa_sha512_verify",
    "rt_ed25519_verify",
    "rt_ecdsa_p256_verify",
    // Signature generation (RFC 8332 RSA + RFC 5656 ECDSA-P256) for SSH host keys
    "rt_rsa_sha256_sign",
    "rt_rsa_sha512_sign",
    "rt_ed25519_sign",
    "rt_ecdsa_p256_sign",
    // PBKDF2-HMAC native helpers (FR pbkdf2_native_runtime_helpers_2026-05-01)
    "rt_pbkdf2_hmac_sha1",
    "rt_pbkdf2_hmac_sha256",
    "rt_pbkdf2_hmac_sha384",
    "rt_pbkdf2_hmac_sha512",
    // Curve25519 DH key exchange for SSH KEX
    "rt_dh_curve25519_keypair",
    "rt_dh_curve25519_public_key",
    "rt_dh_curve25519_shared_secret",
    "rt_dh_curve25519_free",
    // TLS / X25519 helpers used by the baremetal SSH guest lane
    "rt_tls13_x25519_public_key",
    "rt_tls13_x25519_shared_secret",
    "rt_ssh_userauth_password_only_failure_payload",
    // Signal handling
    "rt_signal_install",
    "rt_signal_check",
    "rt_atexit_install",
    "rt_atexit_check",
    // CUDA runtime
    "rt_cuda_available",
    "rt_cuda_init",
    "rt_cuda_device_get",
    "rt_cuda_ctx_create",
    "rt_cuda_ctx_destroy",
    "rt_cuda_mem_alloc",
    "rt_cuda_mem_free",
    "rt_cuda_memset",
    "rt_cuda_memcpy_dtoh",
    "rt_cuda_module_load_data",
    "rt_cuda_module_unload",
    "rt_cuda_launch_kernel",
    "rt_cuda_sync",
    "rt_webgpu_is_available",
    "rt_webgpu_init",
    "rt_webgpu_shutdown",
    "rt_webgpu_create_surface",
    "rt_webgpu_destroy_surface",
    "rt_webgpu_upload_pixels",
    "rt_webgpu_present",
    "rt_webgpu_compute_draw",
    // Metal runtime (macOS) — needed for JIT-compiled code to resolve calls
    "rt_metal_init",
    "rt_metal_is_available",
    "rt_metal_device_count",
    "rt_metal_device_name",
    "rt_metal_device_memory",
    "rt_metal_create_device",
    "rt_metal_destroy_device",
    "rt_metal_create_command_queue",
    "rt_metal_destroy_command_queue",
    "rt_metal_create_command_buffer",
    "rt_metal_commit_command_buffer",
    "rt_metal_wait_completed",
    "rt_metal_alloc_buffer",
    "rt_metal_free_buffer",
    "rt_metal_buffer_upload",
    "rt_metal_buffer_download",
    "rt_metal_compile_shader",
    "rt_metal_destroy_shader",
    "rt_metal_create_compute_pipeline",
    "rt_metal_destroy_pipeline",
    "rt_metal_create_compute_encoder",
    "rt_metal_end_compute_encoder",
    "rt_metal_set_buffer",
    "rt_metal_set_bytes",
    "rt_metal_dispatch_compute",
    "rt_metal_get_last_error",
    "rt_metal_run_compute_frame",
    "rt_metal_run_blit_frame",
    // ---- Auto-completion: cfg-active exported runtime symbols ----
    // Symbols below carry #[no_mangle]/#[export_name] in runtime/src and are present
    // in the default bootstrap build's libsimple_runtime cdylib, but were previously
    // absent from this curated list. Listing them lets the Cranelift JIT register and
    // resolve any rt_* the compiled code references (e.g. rt_unwrap_or_self) instead of
    // panicking in finalize_definitions. cfg-gated families (vulkan, pytorch, monoio,
    // packaging-compression, bench-internals) are intentionally excluded.
    "rt_actor_id",
    "rt_actor_is_alive",
    "rt_actor_join",
    "rt_actor_reply",
    "rt_aes256_encrypt_block_into",
    "rt_aes256_encrypt_block_pure",
    "rt_arena_alloc",
    "rt_arena_capacity",
    "rt_arena_free",
    "rt_arena_new",
    "rt_arena_reset",
    "rt_arena_used",
    "rt_array_all_truthy",
    "rt_array_any_truthy",
    "rt_array_concat",
    "rt_array_copy",
    "rt_array_count",
    "rt_array_data_ptr",
    "rt_array_drop",
    "rt_array_enumerate",
    "rt_array_extend_i64",
    "rt_array_fill",
    "rt_array_flatten",
    "rt_array_free",
    "rt_array_header_ptr",
    "rt_array_index_of",
    "rt_array_join",
    "rt_array_last",
    "rt_array_last_index_of",
    "rt_array_max",
    "rt_array_min",
    "rt_array_new_with_cap",
    "rt_array_new_with_cap_bool",
    "rt_array_new_with_cap_i64",
    "rt_array_new_with_cap_js_value",
    "rt_array_new_with_cap_text",
    "rt_array_new_with_cap_u64",
    "rt_array_push_grow",
    "rt_array_push_no_grow",
    "rt_array_range",
    "rt_array_repeat",
    "rt_array_reverse",
    "rt_array_reversed",
    "rt_array_set_len_known",
    "rt_array_sort",
    "rt_array_sort_desc",
    "rt_array_sorted",
    "rt_array_sum",
    "rt_array_take",
    "rt_array_unique",
    "rt_array_zip",
    "rt_async_current_task_id",
    "rt_async_get_ctx",
    "rt_async_get_state",
    "rt_async_mark_done",
    "rt_async_poll_tasks",
    "rt_async_run_until_complete",
    "rt_async_schedule_await",
    "rt_async_set_state",
    "rt_async_spawn",
    "rt_async_spawn_task",
    "rt_atomic_bool_free",
    "rt_atomic_bool_load",
    "rt_atomic_bool_new",
    "rt_atomic_bool_store",
    "rt_atomic_bool_swap",
    "rt_atomic_compare_exchange",
    "rt_atomic_fetch_add",
    "rt_atomic_fetch_and",
    "rt_atomic_fetch_or",
    "rt_atomic_fetch_sub",
    "rt_atomic_flag_clear",
    "rt_atomic_flag_free",
    "rt_atomic_flag_new",
    "rt_atomic_flag_test_and_set",
    "rt_atomic_free",
    "rt_atomic_int_compare_exchange",
    "rt_atomic_int_fetch_add",
    "rt_atomic_int_fetch_and",
    "rt_atomic_int_fetch_or",
    "rt_atomic_int_fetch_sub",
    "rt_atomic_int_fetch_xor",
    "rt_atomic_int_free",
    "rt_atomic_int_load",
    "rt_atomic_int_new",
    "rt_atomic_int_store",
    "rt_atomic_int_swap",
    "rt_atomic_load",
    "rt_atomic_new",
    "rt_atomic_store",
    "rt_atomic_swap",
    "rt_barrier_free",
    "rt_barrier_new",
    "rt_barrier_thread_count",
    "rt_barrier_wait",
    "rt_bdd_after_each",
    "rt_bdd_before_each",
    "rt_bdd_clear_state",
    "rt_bdd_describe_end",
    "rt_bdd_describe_start",
    "rt_bdd_describe_start_rv",
    "rt_bdd_expect_eq",
    "rt_bdd_expect_eq_rv",
    "rt_bdd_expect_fail",
    "rt_bdd_expect_truthy",
    "rt_bdd_expect_truthy_rv",
    "rt_bdd_format_results",
    "rt_bdd_has_failure",
    "rt_bdd_it_end",
    "rt_bdd_it_start",
    "rt_bdd_it_start_rv",
    "rt_bytes_u8_set",
    "rt_cargo_build",
    "rt_cargo_check",
    "rt_cargo_clean",
    "rt_cargo_test",
    "rt_channel_close",
    "rt_channel_free",
    "rt_channel_id",
    "rt_channel_is_closed",
    "rt_channel_new",
    "rt_channel_recv",
    "rt_channel_recv_timeout",
    "rt_channel_send",
    "rt_channel_try_recv",
    "rt_pool_is_done",
    "rt_pool_join",
    "rt_pool_get_parallelism",
    "rt_pool_set_parallelism",
    "rt_pool_submit",
    "rt_pool_uses_global_fifo_queue",
    "rt_pool_uses_work_stealing",
    "rt_clear_args",
    "rt_cli_handle_add",
    "rt_cli_handle_build",
    "rt_cli_handle_cache",
    "rt_cli_handle_env",
    "rt_cli_handle_init",
    "rt_cli_handle_install",
    "rt_cli_handle_list",
    "rt_cli_handle_lock",
    "rt_cli_handle_remove",
    "rt_cli_handle_targets",
    "rt_cli_handle_tree",
    "rt_cli_handle_update",
    "rt_cli_run_brief",
    "rt_cli_run_constr",
    "rt_cli_run_context",
    "rt_cli_run_diff",
    "rt_cli_run_feature_gen",
    "rt_cli_run_i18n",
    "rt_cli_run_info",
    "rt_cli_run_mcp",
    "rt_cli_run_qualify_ignore",
    "rt_cli_run_replay",
    "rt_cli_run_spec_coverage",
    "rt_cli_run_spec_gen",
    "rt_cli_run_spipe_docgen",
    "rt_cli_run_task_gen",
    "rt_cli_run_todo_gen",
    "rt_cli_run_todo_scan",
    "rt_closure_free",
    "rt_concurrent_map_clear",
    "rt_concurrent_map_contains",
    "rt_concurrent_map_free",
    "rt_concurrent_map_get",
    "rt_concurrent_map_insert",
    "rt_concurrent_map_len",
    "rt_concurrent_map_new",
    "rt_concurrent_map_remove",
    "rt_concurrent_queue_free",
    "rt_concurrent_queue_is_empty",
    "rt_concurrent_queue_len",
    "rt_concurrent_queue_new",
    "rt_concurrent_queue_pop",
    "rt_concurrent_queue_push",
    "rt_concurrent_stack_free",
    "rt_concurrent_stack_is_empty",
    "rt_concurrent_stack_len",
    "rt_concurrent_stack_new",
    "rt_concurrent_stack_pop",
    "rt_concurrent_stack_push",
    "rt_condvar_free",
    "rt_condvar_new",
    "rt_condvar_notify_all",
    "rt_condvar_notify_one",
    "rt_condvar_wait",
    "rt_condvar_wait_timeout",
    "rt_context_generate",
    "rt_context_stats",
    "rt_contract_violation_free",
    "rt_contract_violation_func_name",
    "rt_contract_violation_kind",
    "rt_contract_violation_message",
    "rt_contract_violation_new",
    "rt_coverage_clear",
    "rt_coverage_condition_probe",
    "rt_coverage_decision_probe",
    "rt_coverage_dump_sdn",
    "rt_coverage_enabled",
    "rt_coverage_free_sdn",
    "rt_coverage_path_finalize",
    "rt_coverage_path_probe",
    "rt_cuda_ctx_synchronize",
    "rt_cuda_device_compute_capability",
    "rt_cuda_device_count",
    "rt_cuda_device_name",
    "rt_cuda_f64_binary_op",
    "rt_cuda_f64_minmax",
    "rt_cuda_f64_scalar_div",
    "rt_cuda_f64_slice_1d",
    "rt_cuda_f64_slice_2d",
    "rt_cuda_f64_sum",
    "rt_cuda_f64_sum_axis",
    "rt_cuda_get_error_string",
    "rt_cuda_memcpy_dtod",
    "rt_cuda_memcpy_htod",
    "rt_cuda_module_get_function",
    "rt_cuda_module_load",
    "rt_current_task_id",
    "rt_db_accel_bitmap_and_words",
    "rt_db_accel_bitmap_or_words",
    "rt_debug_add_breakpoint",
    "rt_debug_continue",
    "rt_debug_current_file",
    "rt_debug_current_line",
    "rt_debug_is_active",
    "rt_debug_list_breakpoints",
    "rt_debug_locals",
    "rt_debug_pause",
    "rt_debug_remove_all_breakpoints",
    "rt_debug_remove_breakpoint",
    "rt_debug_set_active",
    "rt_debug_set_step_mode",
    "rt_debug_stack_depth",
    "rt_debug_stack_trace",
    "rt_diagram_arch_entity_count",
    "rt_diagram_clear",
    "rt_diagram_clear_context",
    "rt_diagram_disable",
    "rt_diagram_enable",
    "rt_diagram_event_count",
    "rt_diagram_free_string",
    "rt_diagram_generate_arch",
    "rt_diagram_generate_class",
    "rt_diagram_generate_sequence",
    "rt_diagram_is_architectural",
    "rt_diagram_is_enabled",
    "rt_diagram_mark_architectural",
    "rt_diagram_set_context",
    "rt_diagram_trace_call",
    "rt_diagram_trace_method",
    "rt_diagram_trace_method_with_args",
    "rt_diagram_trace_return",
    "rt_dict_free",
    "rt_dict_remove",
    "rt_executor_current_task_id",
    "rt_executor_get_mode",
    "rt_executor_is_manual",
    "rt_executor_pending_count",
    "rt_executor_poll",
    "rt_executor_poll_all",
    "rt_executor_set_mode",
    "rt_executor_set_workers",
    "rt_executor_shutdown",
    "rt_executor_start",
    "rt_fault_set_execution_limit",
    "rt_fault_set_max_recursion_depth",
    "rt_fault_set_stack_overflow_detection",
    "rt_fault_set_timeout",
    "rt_fiber_current_task_id",
    "rt_fiber_enter_task_id",
    "rt_fiber_exit_task_id",
    "rt_file_exists_str",
    "rt_file_hash",
    "rt_file_madvise",
    "rt_file_mmap",
    "rt_file_msync",
    "rt_file_munmap",
    "rt_future_all",
    "rt_future_free",
    "rt_future_get_result",
    "rt_future_is_ready",
    "rt_future_race",
    "rt_future_reject",
    "rt_future_resolve",
    "rt_generator_free",
    "rt_get_argc",
    "rt_gpu_atomic_add_i64",
    "rt_gpu_atomic_add_u32",
    "rt_gpu_atomic_and_i64",
    "rt_gpu_atomic_and_u32",
    "rt_gpu_atomic_cmpxchg_i64",
    "rt_gpu_atomic_cmpxchg_u32",
    "rt_gpu_atomic_max_i64",
    "rt_gpu_atomic_max_u32",
    "rt_gpu_atomic_min_i64",
    "rt_gpu_atomic_min_u32",
    "rt_gpu_atomic_or_i64",
    "rt_gpu_atomic_or_u32",
    "rt_gpu_atomic_sub_i64",
    "rt_gpu_atomic_sub_u32",
    "rt_gpu_atomic_xchg_i64",
    "rt_gpu_atomic_xchg_u32",
    "rt_gpu_atomic_xor_i64",
    "rt_gpu_atomic_xor_u32",
    "rt_gpu_backend_available",
    "rt_gpu_backend_get",
    "rt_gpu_backend_is_available",
    "rt_gpu_backend_name",
    "rt_gpu_backend_set",
    "rt_gpu_barrier",
    "rt_gpu_global_id",
    "rt_gpu_global_size",
    "rt_gpu_group_id",
    "rt_gpu_launch",
    "rt_gpu_launch_1d",
    "rt_gpu_local_id",
    "rt_gpu_local_size",
    "rt_gpu_mem_fence",
    "rt_gpu_num_groups",
    "rt_gpu_shared_alloc",
    "rt_gpu_shared_reset",
    "rt_handle_free",
    "rt_handle_get",
    "rt_handle_is_valid",
    "rt_handle_new",
    "rt_handle_set",
    "rt_is_contract_violation",
    "rt_is_none",
    "rt_is_some",
    "rt_log_clear_scope_levels",
    "rt_log_debug",
    "rt_log_emit",
    "rt_log_emit_rv",
    "rt_log_error",
    "rt_log_fatal",
    "rt_log_get_global_level",
    "rt_log_get_scope_level",
    "rt_log_info",
    "rt_log_is_enabled",
    "rt_log_level_name",
    "rt_log_set_global_level",
    "rt_log_set_scope_level",
    "rt_log_trace",
    "rt_log_verbose",
    "rt_log_warn",
    "rt_metal_begin_render_pass",
    "rt_metal_create_render_pipeline",
    "rt_metal_create_sampler",
    "rt_metal_create_swapchain",
    "rt_metal_create_texture",
    "rt_metal_destroy_render_pipeline",
    "rt_metal_destroy_sampler",
    "rt_metal_destroy_swapchain",
    "rt_metal_draw_indexed",
    "rt_metal_draw_primitives",
    "rt_metal_end_render_pass",
    "rt_metal_free_texture",
    "rt_metal_present",
    "rt_metal_set_scissor",
    "rt_metal_set_viewport",
    "rt_mutex_free",
    "rt_mutex_id",
    "rt_mutex_lock",
    "rt_mutex_new",
    "rt_mutex_try_lock",
    "rt_mutex_unlock",
    "rt_net_free_addr_string",
    "rt_object_class_id",
    "rt_object_field_count",
    "rt_object_free",
    "rt_once_call",
    "rt_once_free",
    "rt_once_is_completed",
    "rt_once_new",
    "rt_option_map",
    "rt_package_chmod",
    "rt_package_copy_file",
    "rt_package_create_symlink",
    "rt_package_create_tarball",
    "rt_package_exists",
    "rt_package_extract_tarball",
    "rt_package_file_size",
    "rt_package_free_string",
    "rt_package_is_dir",
    "rt_package_mkdir_all",
    "rt_package_remove_dir_all",
    "rt_package_sha256",
    "rt_par_atomic_add_i64",
    "rt_par_atomic_cmpxchg_i64",
    "rt_par_atomic_max_i64",
    "rt_par_atomic_min_i64",
    "rt_par_atomic_sub_i64",
    "rt_par_atomic_xchg_i64",
    "rt_par_barrier",
    "rt_par_global_id",
    "rt_par_global_size",
    "rt_par_group_id",
    "rt_par_launch",
    "rt_par_launch_1d",
    "rt_par_local_id",
    "rt_par_local_size",
    "rt_par_mem_fence",
    "rt_par_num_groups",
    "rt_par_shared_alloc",
    "rt_par_shared_reset",
    "rt_pool_acquire",
    "rt_pool_available",
    "rt_pool_capacity",
    "rt_pool_free",
    "rt_pool_new",
    "rt_pool_release",
    "rt_process_run_timeout",
    "rt_process_run_with_limits",
    "rt_profiler_is_active",
    "rt_profiler_record_call",
    "rt_profiler_record_return",
    "rt_ps_torch_tensor_from_bits_1d",
    "rt_read_file_str",
    "rt_read_stdin_line",
    "rt_resource_registry_clear",
    "rt_resource_registry_close_all",
    "rt_resource_registry_count",
    "rt_resource_registry_free_string",
    "rt_resource_registry_has_leaks",
    "rt_resource_registry_leak_report",
    "rt_resource_registry_register",
    "rt_resource_registry_unregister",
    "rt_rsa_pss_sha256_verify",
    "rt_rsa_pss_sha384_verify",
    "rt_rsa_pss_sha512_verify",
    "rt_rwlock_free",
    "rt_rwlock_new",
    "rt_rwlock_read",
    "rt_rwlock_set",
    "rt_rwlock_try_read",
    "rt_rwlock_try_write",
    "rt_rwlock_unlock_read",
    "rt_rwlock_unlock_write",
    "rt_rwlock_write",
    "rt_screenshot_capture_after_terminal",
    "rt_screenshot_capture_before_terminal",
    "rt_screenshot_capture_count",
    "rt_screenshot_clear_captures",
    "rt_screenshot_clear_context",
    "rt_screenshot_disable",
    "rt_screenshot_enable",
    "rt_screenshot_exists",
    "rt_screenshot_free_string",
    "rt_screenshot_get_output_dir",
    "rt_screenshot_get_path",
    "rt_screenshot_is_enabled",
    "rt_screenshot_is_refresh",
    "rt_screenshot_set_context",
    "rt_screenshot_set_output_dir",
    "rt_screenshot_set_refresh",
    "rt_sdn_check",
    "rt_sdn_fmt",
    "rt_sdn_from_json",
    "rt_sdn_get",
    "rt_sdn_set",
    "rt_sdn_to_json",
    "rt_sdn_version",
    "rt_security_last_sandbox_backend_id",
    "rt_security_last_sandbox_capability_allowed",
    "rt_security_last_sandbox_capability_handles",
    "rt_security_sandbox_capability_allowed",
    "rt_security_sandbox_capability_denials",
    "rt_semaphore_acquire",
    "rt_semaphore_acquire_timeout",
    "rt_semaphore_count",
    "rt_semaphore_free",
    "rt_semaphore_new",
    "rt_semaphore_release",
    "rt_semaphore_try_acquire",
    "rt_serial_close",
    "rt_serial_flush",
    "rt_serial_open",
    "rt_serial_read",
    "rt_serial_relay",
    "rt_serial_set_timeout",
    "rt_serial_write",
    "rt_set_args",
    "rt_settlement_main",
    "rt_sffi_call_method",
    "rt_sffi_clear_registry",
    "rt_sffi_clone",
    "rt_sffi_drop",
    "rt_sffi_has_method",
    "rt_sffi_is_type",
    "rt_sffi_new",
    "rt_sffi_object_call_method",
    "rt_sffi_object_free",
    "rt_sffi_object_handle",
    "rt_sffi_object_has_method",
    "rt_sffi_object_is_ffi",
    "rt_sffi_object_new",
    "rt_sffi_object_type_id",
    "rt_sffi_object_type_name",
    "rt_sffi_object_vtable",
    "rt_sffi_type_id",
    "rt_sffi_type_name",
    "rt_sffi_type_register",
    "rt_shared_clone",
    "rt_shared_downgrade",
    "rt_shared_get",
    "rt_shared_needs_trace",
    "rt_shared_new",
    "rt_shared_ref_count",
    "rt_shared_release",
    "rt_simd_add_i32x4",
    "rt_simd_add_i32x8",
    "rt_simd_aes_round_last_u8x16_lanes",
    "rt_simd_aes_round_u8x16_lanes",
    "rt_simd_clmul_hi_u64",
    "rt_simd_clmul_lo_u64",
    "rt_simd_mul_i32x4",
    "rt_simd_mul_i32x8",
    "rt_simd_sub_i32x4",
    "rt_simd_sub_i32x8",
    "rt_simd_xor_u64x2",
    "rt_simd_xor_u8x16",
    "rt_spin_loop_hint",
    "rt_string_char_code_at",
    "rt_string_to_float",
    "rt_test_db_cleanup_stale_runs",
    "rt_test_db_enable_validation",
    "rt_test_db_validate",
    "rt_test_run_is_stale",
    "rt_text_find",
    "rt_thread_local_free",
    "rt_thread_local_get",
    "rt_thread_local_new",
    "rt_thread_local_set",
    "rt_tls13_aes128_gcm_decrypt",
    "rt_tls13_aes256_gcm_decrypt",
    "rt_tls13_aes256_gcm_encrypt",
    "rt_tls_clear",
    "rt_tls_client_config_add_root_cert",
    "rt_tls_client_config_enable_sni",
    "rt_tls_client_config_free",
    "rt_tls_client_config_new",
    "rt_tls_client_config_set_alpn",
    "rt_tls_client_config_set_verify_mode",
    "rt_tls_free",
    "rt_tls_free_cert",
    "rt_tls_generate_self_signed_cert",
    "rt_tls_get",
    "rt_tls_get_cert_expiry",
    "rt_tls_get_cert_issuer",
    "rt_tls_get_cert_subject",
    "rt_tls_get_cipher_suite",
    "rt_tls_get_negotiated_alpn",
    "rt_tls_get_peer_cert",
    "rt_tls_hash_cert",
    "rt_tls_is_handshake_complete",
    "rt_tls_load_cert",
    "rt_tls_load_key",
    "rt_tls_new",
    "rt_tls_remove",
    "rt_tls_server_accept",
    "rt_tls_server_close_connection",
    "rt_tls_server_config_free",
    "rt_tls_server_config_new",
    "rt_tls_server_config_require_client_cert",
    "rt_tls_server_config_set_alpn",
    "rt_tls_server_create",
    "rt_tls_server_create_from_der",
    "rt_tls_server_read",
    "rt_tls_server_shutdown",
    "rt_tls_server_write",
    "rt_tls_server_write_bytes",
    "rt_tls_set",
    "rt_tls_verify_cert",
    "rt_tuple_free",
    "rt_typed_bytes_u8_data_at",
    "rt_typed_words_u32_data_at",
    "rt_typed_words_u32_push_known_at",
    "rt_typed_words_u32_push_known_data_at",
    "rt_typed_words_u32_store_known_data_at",
    "rt_typed_words_u32_unchecked",
    "rt_typed_words_u64_at",
    "rt_typed_words_u64_data_at",
    "rt_typed_words_u64_data_at_checked",
    "rt_typed_words_u64_push",
    "rt_typed_words_u64_push_known_at",
    "rt_typed_words_u64_push_known_data_at",
    "rt_typed_words_u64_raw_data_at",
    "rt_typed_words_u64_set",
    "rt_typed_words_u64_store_known_data_at",
    "rt_typed_words_u64_unchecked",
    "rt_unique_free",
    "rt_unique_get",
    "rt_unique_needs_trace",
    "rt_unique_new",
    "rt_unique_set",
    "rt_unix_socket_accept",
    "rt_unix_socket_close",
    "rt_unix_socket_connect",
    "rt_unix_socket_free_buf",
    "rt_unix_socket_listen",
    "rt_unix_socket_recv",
    "rt_unix_socket_send",
    "rt_unwrap_or_self",
    "rt_value_format_string",
    "rt_vec_abs",
    "rt_vec_all",
    "rt_vec_any",
    "rt_vec_blend",
    "rt_vec_ceil",
    "rt_vec_clamp",
    "rt_vec_extract",
    "rt_vec_floor",
    "rt_vec_fma",
    "rt_vec_gather",
    "rt_vec_load",
    "rt_vec_masked_load",
    "rt_vec_masked_store",
    "rt_vec_max",
    "rt_vec_max_vec",
    "rt_vec_min",
    "rt_vec_min_vec",
    "rt_vec_product",
    "rt_vec_recip",
    "rt_vec_round",
    "rt_vec_scatter",
    "rt_vec_select",
    "rt_vec_shuffle",
    "rt_vec_sqrt",
    "rt_vec_store",
    "rt_vec_sum",
    "rt_vec_with",
    "rt_vulkan_acquire_next_image",
    "rt_vulkan_alloc_buffer",
    "rt_vulkan_begin_compute",
    "rt_vulkan_begin_render_pass_gfx",
    "rt_vulkan_bind_buffer",
    "rt_vulkan_bind_descriptors",
    "rt_vulkan_bind_graphics_pipeline",
    "rt_vulkan_bind_index_buffer",
    "rt_vulkan_bind_pipeline",
    "rt_vulkan_bind_texture",
    "rt_vulkan_bind_vertex_buffer",
    "rt_vulkan_compile_glsl",
    "rt_vulkan_compile_spirv",
    "rt_vulkan_copy_buffer",
    "rt_vulkan_copy_from_buffer",
    "rt_vulkan_copy_to_buffer",
    "rt_vulkan_create_compute_pipeline",
    "rt_vulkan_create_descriptor_set",
    "rt_vulkan_create_fence",
    "rt_vulkan_create_framebuffer",
    "rt_vulkan_create_graphics_pipeline",
    "rt_vulkan_create_image",
    "rt_vulkan_create_render_pass",
    "rt_vulkan_create_sampler",
    "rt_vulkan_create_swapchain",
    "rt_vulkan_destroy_descriptor_set",
    "rt_vulkan_destroy_fence",
    "rt_vulkan_destroy_framebuffer",
    "rt_vulkan_destroy_graphics_pipeline",
    "rt_vulkan_destroy_image",
    "rt_vulkan_destroy_pipeline",
    "rt_vulkan_destroy_render_pass",
    "rt_vulkan_destroy_sampler",
    "rt_vulkan_destroy_shader",
    "rt_vulkan_destroy_swapchain",
    "rt_vulkan_device_count",
    "rt_vulkan_device_memory",
    "rt_vulkan_device_name",
    "rt_vulkan_device_type",
    "rt_vulkan_dispatch",
    "rt_vulkan_draw",
    "rt_vulkan_draw_indexed",
    "rt_vulkan_end_compute",
    "rt_vulkan_end_render_pass_gfx",
    "rt_vulkan_free_buffer",
    "rt_vulkan_get_device",
    "rt_vulkan_get_last_error",
    "rt_vulkan_init",
    "rt_vulkan_is_available",
    "rt_vulkan_map_memory",
    "rt_vulkan_present",
    "rt_vulkan_push_constants",
    "rt_vulkan_reset_fence",
    "rt_vulkan_select_device",
    "rt_vulkan_set_scissor",
    "rt_vulkan_set_viewport",
    "rt_vulkan_shutdown",
    "rt_vulkan_submit_and_wait",
    "rt_vulkan_unmap_memory",
    "rt_vulkan_wait_fence",
    "rt_vulkan_wait_idle",
    "rt_weak_free",
    "rt_weak_is_valid",
    "rt_weak_new",
    "rt_weak_upgrade",
    "rt_ws_mask_bytes",
    // ---- Codegen aliases (resolved via #[export_name] wrappers in runtime/src) ----
    // The compiler emits these Simple-facing names; the AOT loader rewrites them, but the
    // Cranelift JIT registers symbols by exact name, so each is exported as a real symbol
    // forwarding to its canonical target (see runtime/src/value/sffi/{file_io,io_print}).
    "rt_file_delete", // -> rt_file_remove
    "rt_print",       // -> rt_print_value
    "rt_println",     // -> rt_println_value
    "sys_get_args",   // -> rt_get_args
    "sys_exit",       // -> rt_exit
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abi_version_compatibility() {
        let v1_0 = AbiVersion::new(1, 0);
        let v1_1 = AbiVersion::new(1, 1);
        let v2_0 = AbiVersion::new(2, 0);

        // Same version is compatible
        assert!(v1_0.is_compatible_with(&v1_0));

        // Higher minor is compatible
        assert!(v1_1.is_compatible_with(&v1_0));

        // Lower minor is NOT compatible
        assert!(!v1_0.is_compatible_with(&v1_1));

        // Different major is NOT compatible
        assert!(!v2_0.is_compatible_with(&v1_0));
        assert!(!v1_0.is_compatible_with(&v2_0));
    }

    #[test]
    fn test_abi_version_u32_roundtrip() {
        let v = AbiVersion::new(1, 5);
        let packed = v.to_u32();
        let unpacked = AbiVersion::from_u32(packed);
        assert_eq!(v, unpacked);
    }

    #[test]
    fn test_abi_version_display() {
        let v = AbiVersion::new(1, 2);
        assert_eq!(format!("{}", v), "1.2");
    }

    #[test]
    fn test_symbol_list_not_empty() {
        // Verify the list has a reasonable number of symbols
        assert!(RUNTIME_SYMBOL_NAMES.len() > 10);
        assert!(RUNTIME_SYMBOL_NAMES.contains(&"rt_array_new"));
        assert!(RUNTIME_SYMBOL_NAMES.contains(&"rt_byte_array_new"));
        assert!(RUNTIME_SYMBOL_NAMES.contains(&"rt_println_value"));
    }

    #[test]
    fn test_symbol_classification_marks_core_abi_and_hosted_symbols() {
        assert_eq!(symbol_class_of("rt_alloc"), RuntimeSymbolClass::CoreRequired);
        assert_eq!(symbol_class_of("rt_byte_array_new"), RuntimeSymbolClass::CoreRequired);
        assert_eq!(symbol_class_of("rt_stdout_flush"), RuntimeSymbolClass::CoreRequired);
        assert_eq!(symbol_class_of("rt_file_read_text"), RuntimeSymbolClass::HostedOnly);
        assert_eq!(
            symbol_class_of("rt_security_enter_gate"),
            RuntimeSymbolClass::HostedOnly
        );
        assert_eq!(symbol_class_of("rt_array_clear"), RuntimeSymbolClass::Unported);
    }
}
