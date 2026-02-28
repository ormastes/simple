//! Runtime symbol resolution abstraction.
//!
//! Provides a unified interface for resolving runtime FFI symbols,
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
    pub const CURRENT: Self = Self { major: 1, minor: 1 };

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

/// Trait for resolving runtime FFI symbols.
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

/// Classify a runtime symbol name into its tier.
pub fn symbol_tier_of(name: &str) -> RuntimeSymbolTier {
    use RuntimeSymbolTier::*;

    // Tier 4: Ext
    if name.starts_with("rt_vec_")
        || name.starts_with("rt_neighbor_load")
        || name.starts_with("rt_gpu_")
        || name.starts_with("rt_vk_")
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
        || name.starts_with("rt_exit")
        || name.starts_with("rt_file_")
        || name.starts_with("rt_dir_")
        || name.starts_with("rt_path_")
        || name.starts_with("rt_current_dir")
        || name.starts_with("rt_set_current_dir")
        || name.starts_with("rt_process_")
        || name.starts_with("rt_exec")
        || name.starts_with("rt_write_file")
        || name.starts_with("rt_getpid")
        || name.starts_with("rt_hostname")
        || name.starts_with("rt_system_")
        || name.starts_with("rt_time_")
        || name.starts_with("ffi_regex_")
        || name.starts_with("rt_sdn_")
        || name.starts_with("rt_sandbox_")
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
        || name.starts_with("rt_ffi_")
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
        || name.starts_with("rt_dict_")
        || name.starts_with("rt_index_")
        || name.starts_with("rt_slice")
        || name.starts_with("rt_contains")
        || name.starts_with("rt_len")
        || name.starts_with("rt_string_")
        || name.starts_with("rt_to_string")
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

/// List of all runtime FFI symbols.
///
/// These are the extern "C" functions exported by the runtime library
/// that can be called from compiled Simple code.
pub const RUNTIME_SYMBOL_NAMES: &[&str] = &[
    // AOP runtime operations
    "rt_aop_invoke_around",
    "rt_aop_proceed",
    // Array operations
    "rt_array_new",
    "rt_array_push",
    "rt_array_get",
    "rt_array_set",
    "rt_array_pop",
    "rt_array_clear",
    "rt_array_len",
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
    // Index/slice operations
    "rt_index_get",
    "rt_index_set",
    "rt_slice",
    "rt_contains",
    // String operations
    "rt_string_new",
    "rt_string_concat",
    "rt_cstring_to_text",
    // Regex operations
    "ffi_regex_is_match",
    "ffi_regex_find",
    "ffi_regex_find_all",
    "ffi_regex_captures",
    "ffi_regex_replace",
    "ffi_regex_replace_all",
    "ffi_regex_split",
    "ffi_regex_split_n",
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
    // Async/concurrency operations
    "rt_wait",
    "rt_future_new",
    "rt_future_await",
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
    // Interpreter bridge FFI
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
    "rt_print_value",
    "rt_println_value",
    "rt_eprint_value",
    "rt_eprintln_value",
    "rt_capture_stdout_start",
    "rt_capture_stderr_start",
    // Environment & Process operations
    "rt_env_get",
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
    "rt_process_execute",
    "rt_platform_name",
    "rt_decision_probe",
    "rt_condition_probe",
    "rt_path_probe",
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
    "rt_file_write_text",
    "rt_file_copy",
    "rt_file_remove",
    "rt_file_rename",
    "rt_file_read_lines",
    "rt_file_append_text",
    "rt_file_read_bytes",
    "rt_file_write_bytes",
    "rt_file_move",
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
    "rt_value_to_string",
    "rt_value_eq",
    "rt_value_compare",
    "rt_value_truthy",
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
        assert!(RUNTIME_SYMBOL_NAMES.contains(&"rt_println_value"));
    }
}
