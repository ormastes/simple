//! Runtime SFFI function declarations for codegen.
//!
//! This module provides a shared specification of runtime functions that
//! both AOT (cranelift.rs) and JIT (jit.rs) compilers need to declare.
//!
//! Functions are organized into tiers matching the standard library hierarchy:
//! - **Core**: Value types, enums, errors, contracts — no alloc, no OS
//! - **Alloc**: Collections, strings, objects, closures, pointers, memory
//! - **Sys**: I/O, files, env, process, networking, regex, sandbox, CLI
//! - **Async**: Futures, actors, channels, executor, threads, generators
//! - **Ext**: SIMD, GPU, Vulkan, Cranelift self-hosting

use cranelift_codegen::ir::{types, AbiParam, Signature};
use cranelift_codegen::isa::CallConv;

/// Runtime function tier, matching the standard library hierarchy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeFuncTier {
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

/// Classify a runtime function name into its tier.
pub fn tier_of(name: &str) -> RuntimeFuncTier {
    use RuntimeFuncTier::*;

    // Tier 4: Ext — SIMD, GPU, Vulkan, Cranelift
    if name.starts_with("rt_vec_")
        || name.starts_with("rt_neighbor_load")
        || name.starts_with("rt_gpu_")
        || name.starts_with("rt_host_gpu_")
        || name.starts_with("rt_vk_")
        || name.starts_with("rt_metal_")
        || name.starts_with("rt_cranelift_")
        || name.starts_with("rt_par_")
        || name.starts_with("rt_simd_")
    {
        return Ext;
    }

    // Tier 3: Async — futures, actors, channels, executor, threads, generators
    if name.starts_with("rt_future_")
        || name.starts_with("rt_async_")
        || name.starts_with("rt_actor_")
        || name.starts_with("rt_channel_")
        || name.starts_with("rt_executor_")
        || name.starts_with("rt_fiber_")
        || name.starts_with("rt_pool_")
        || name.starts_with("rt_thread_")
        || name.starts_with("rt_generator_")
        || name == "rt_current_task_id"
        || name == "rt_wait"
    {
        return Async;
    }

    // Tier 2: Sys — I/O, files, env, process, networking, CLI, sandbox, etc.
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
        || name.starts_with("rt_exec")
        || name.starts_with("rt_write_file")
        || name.starts_with("rt_getpid")
        || name.starts_with("rt_hostname")
        || name.starts_with("rt_system_")
        || name.starts_with("rt_time_")
        || name.starts_with("sffi_regex_")
        || name.starts_with("rt_sdn_")
        || name.starts_with("rt_sandbox_")
        || name.starts_with("rt_coverage_")
        || name.starts_with("rt_perf_")
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
        || name.starts_with("doctest_")
        || name.starts_with("native_tcp_")
        || name.starts_with("native_udp_")
        || name.starts_with("native_http_")
        || name.starts_with("rt_io_tcp_")
        || name.starts_with("spl_dl")
        || name.starts_with("spl_wffi_")
    {
        return Sys;
    }

    // Tier 1: Alloc — collections, strings, objects, closures, pointers, memory
    if name.starts_with("rt_array_")
        || name.starts_with("rt_tuple_")
        || name.starts_with("rt_db_")
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

    // Tier 0: Core — everything else (value types, enums, errors, contracts, profiler)
    Core
}

/// Get all runtime function specs for a given target.
///
/// - Baremetal targets get Core + Alloc only (no OS, no I/O)
/// - Normal targets get Core + Alloc + Sys + Async
/// - Ext tier (SIMD, GPU, Cranelift) is always included for now
///   (individual features are opt-in at the Simple source level)
pub fn runtime_funcs_for_target(_target: &simple_common::target::Target) -> Vec<&'static RuntimeFuncSpec> {
    // Declare all runtime functions as imports for every target.
    // Baremetal OS kernels (SimpleOS) provide shim implementations;
    // truly bare targets get linker errors for unresolved symbols.
    RUNTIME_FUNCS.iter().collect()
}

/// Specification for a runtime SFFI function signature.
#[derive(Debug, Clone)]
pub struct RuntimeFuncSpec {
    /// Function name (e.g., "rt_array_new")
    pub name: &'static str,
    /// Parameter types
    pub params: &'static [types::Type],
    /// Return types (empty for void)
    pub returns: &'static [types::Type],
}

impl RuntimeFuncSpec {
    pub const fn new(name: &'static str, params: &'static [types::Type], returns: &'static [types::Type]) -> Self {
        Self { name, params, returns }
    }

    /// Get the tier this function belongs to.
    pub fn tier(&self) -> RuntimeFuncTier {
        tier_of(self.name)
    }

    /// Build a Cranelift signature from this spec.
    pub fn build_signature(&self, call_conv: CallConv) -> Signature {
        let mut sig = Signature::new(call_conv);
        for &ty in self.params {
            sig.params.push(AbiParam::new(ty));
        }
        for &ty in self.returns {
            sig.returns.push(AbiParam::new(ty));
        }
        sig
    }
}

// Type aliases for readability
const I8: types::Type = types::I8;
const I32: types::Type = types::I32;
const I64: types::Type = types::I64;
const F64: types::Type = types::F64;

/// All runtime SFFI function specifications.
pub static RUNTIME_FUNCS: &[RuntimeFuncSpec] = &[
    // =========================================================================
    // AOP runtime operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_aop_invoke_around", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_aop_proceed", &[I64], &[I64]),
    // =========================================================================
    // Code coverage & instrumentation probes
    // =========================================================================
    RuntimeFuncSpec::new("rt_decision_probe", &[I64, I8], &[]),
    RuntimeFuncSpec::new("rt_condition_probe", &[I64, I32, I8], &[]),
    RuntimeFuncSpec::new("rt_path_probe", &[I64, I32], &[]),
    // =========================================================================
    // Array operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_array_new", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_byte_array_new", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_byte_array_new_len", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_bytes_to_text", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_new_with_cap_u64", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_push", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_get", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_get_text", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_set", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_set_text", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_pop", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_clear", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_extend_i64", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_len", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_len_safe", &[I64], &[I64]),
    // FR-COMPILER-012: array-repeat for `[value; count]` syntax in JIT
    RuntimeFuncSpec::new("rt_array_repeat", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_first", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_last", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_filter", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_find", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_reverse", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_sort", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_len", &[I64], &[I64]), // Generic length for any collection
    // =========================================================================
    // Tuple operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_tuple_new", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_tuple_set", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_tuple_get", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_tuple_len", &[I64], &[I64]),
    // =========================================================================
    // Dict operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_dict_new", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_dict_set", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_dict_get", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_dict_len", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_dict_clear", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_dict_keys", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_dict_values", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_dict_insert", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_dict_contains", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_dict_remove", &[I64, I64], &[I8]),
    // =========================================================================
    // Fast DB operations (runtime_db.c)
    // =========================================================================
    RuntimeFuncSpec::new("rt_db_table_create", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_table_destroy", &[I64], &[]),
    RuntimeFuncSpec::new("rt_db_put", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_put_value_int", &[I64, I64, I64, I64], &[]),
    RuntimeFuncSpec::new("rt_db_put_value_text", &[I64, I64, I64, I64], &[]),
    RuntimeFuncSpec::new("rt_db_get", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_get_int", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_get_text", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_scan_range", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_scan_result", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_delete", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_row_count", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_col_count", &[I64], &[I64]),
    // Batched DB operations (reduce extern call overhead)
    RuntimeFuncSpec::new("rt_db_put_row3", &[I64, I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_get_int_by_pk", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_update_int", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_update_text", &[I64, I64, I64, I64], &[I64]),
    // Integer-PK DB operations (zero string alloc from caller)
    RuntimeFuncSpec::new("rt_db_iput3", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_iget_int", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_iupdate_int", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_db_idelete", &[I64, I64], &[I64]),
    // =========================================================================
    // Index/slice operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_index_get", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_index_set", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_slice", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_contains", &[I64, I64], &[I8]),
    // =========================================================================
    // Vector reduction operations (SIMD)
    // =========================================================================
    RuntimeFuncSpec::new("rt_vec_sum", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vec_product", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vec_min", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vec_max", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vec_all", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_vec_any", &[I64], &[I8]),
    // Lane access operations (SIMD)
    RuntimeFuncSpec::new("rt_vec_extract", &[I64, I64], &[I64]), // (vector, index) -> element
    RuntimeFuncSpec::new("rt_vec_with", &[I64, I64, I64], &[I64]), // (vector, index, value) -> new_vector
    // Element-wise math operations (SIMD)
    RuntimeFuncSpec::new("rt_vec_sqrt", &[I64], &[I64]), // (vector) -> vector with sqrt applied
    RuntimeFuncSpec::new("rt_vec_abs", &[I64], &[I64]),  // (vector) -> vector with abs applied
    RuntimeFuncSpec::new("rt_vec_floor", &[I64], &[I64]), // (vector) -> vector with floor applied
    RuntimeFuncSpec::new("rt_vec_ceil", &[I64], &[I64]), // (vector) -> vector with ceil applied
    RuntimeFuncSpec::new("rt_vec_round", &[I64], &[I64]), // (vector) -> vector with round applied
    RuntimeFuncSpec::new("rt_vec_shuffle", &[I64, I64], &[I64]), // (vector, indices) -> shuffled vector
    RuntimeFuncSpec::new("rt_vec_blend", &[I64, I64, I64], &[I64]), // (vec1, vec2, indices) -> blended vector
    RuntimeFuncSpec::new("rt_vec_select", &[I64, I64, I64], &[I64]), // (mask, if_true, if_false) -> selected vector
    // SIMD load/store operations
    RuntimeFuncSpec::new("rt_vec_load", &[I64, I64, I64], &[I64]), // (array, offset, lanes) -> vector
    RuntimeFuncSpec::new("rt_vec_store", &[I64, I64, I64], &[]),   // (vector, array, offset) -> ()
    RuntimeFuncSpec::new("rt_vec_gather", &[I64, I64], &[I64]),    // (array, indices) -> vector
    RuntimeFuncSpec::new("rt_vec_scatter", &[I64, I64, I64], &[]), // (vector, array, indices) -> ()
    // SIMD advanced operations
    RuntimeFuncSpec::new("rt_vec_fma", &[I64, I64, I64], &[I64]), // (a, b, c) -> a * b + c
    RuntimeFuncSpec::new("rt_vec_recip", &[I64], &[I64]),         // (vector) -> 1.0 / vector
    RuntimeFuncSpec::new("rt_vec_masked_load", &[I64, I64, I64, I64], &[I64]), // (array, offset, mask, default) -> vector
    RuntimeFuncSpec::new("rt_vec_masked_store", &[I64, I64, I64, I64], &[]),   // (vector, array, offset, mask) -> ()
    RuntimeFuncSpec::new("rt_vec_min_vec", &[I64, I64], &[I64]),               // (a, b) -> element-wise min
    RuntimeFuncSpec::new("rt_vec_max_vec", &[I64, I64], &[I64]),               // (a, b) -> element-wise max
    RuntimeFuncSpec::new("rt_vec_clamp", &[I64, I64, I64], &[I64]),            // (vec, lo, hi) -> clamped
    RuntimeFuncSpec::new("rt_neighbor_load", &[I64, I64], &[I64]),             // (array, direction) -> value
    // =========================================================================
    // GPU Atomic operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_atomic_add", &[I64, I64], &[I64]), // (ptr, val) -> old value
    RuntimeFuncSpec::new("rt_gpu_atomic_sub", &[I64, I64], &[I64]), // (ptr, val) -> old value
    RuntimeFuncSpec::new("rt_gpu_atomic_min", &[I64, I64], &[I64]), // (ptr, val) -> old value
    RuntimeFuncSpec::new("rt_gpu_atomic_max", &[I64, I64], &[I64]), // (ptr, val) -> old value
    RuntimeFuncSpec::new("rt_gpu_atomic_and", &[I64, I64], &[I64]), // (ptr, val) -> old value
    RuntimeFuncSpec::new("rt_gpu_atomic_or", &[I64, I64], &[I64]),  // (ptr, val) -> old value
    RuntimeFuncSpec::new("rt_gpu_atomic_xor", &[I64, I64], &[I64]), // (ptr, val) -> old value
    RuntimeFuncSpec::new("rt_gpu_atomic_exchange", &[I64, I64], &[I64]), // (ptr, val) -> old value
    RuntimeFuncSpec::new("rt_gpu_atomic_cmpxchg", &[I64, I64, I64], &[I64]), // (ptr, expected, desired) -> old value
    // =========================================================================
    // String operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_string_new", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_concat", &[I64, I64], &[I64]),
    // ANY+ANY dynamic add: two RuntimeValue args, one RuntimeValue return (all
    // i64-sized). Emitted by MIR lowering for ANY-typed operands. Without this
    // spec, get_runtime_return_type() returns None so the call's result is never
    // captured — the native/.smf path silently yields 0 for erased addition.
    RuntimeFuncSpec::new("rt_any_add", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_builder_new", &[], &[I64]),
    RuntimeFuncSpec::new("rt_string_builder_push", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_builder_finish", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_builder_len", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_builder_free", &[I64], &[]),
    RuntimeFuncSpec::new("rt_string_starts_with", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_ends_with", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_hash_text", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_str_hash", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_eq", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_len", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_data", &[I64], &[I64]), // RuntimeValue string -> raw ptr
    RuntimeFuncSpec::new("rt_string_char_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_char_code_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_split", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_bytes", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_chars", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_replace", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_trim", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_trim_start", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_trim_end", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_join", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_to_upper", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_to_lower", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_to_int", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_to_int_lenient", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_index_of", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_find", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_string_rfind", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_utf8_count_codepoints", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_utf8_validate", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_utf8_find_invalid", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_text_count_codepoints", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_swi_build", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_swi_char_to_byte", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_swi_byte_to_char", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_swi_free", &[I64], &[]),
    RuntimeFuncSpec::new("rt_rank_select_build", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_rank_query", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_select_query", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_rank_select_free", &[I64], &[]),
    RuntimeFuncSpec::new("rt_aes_encrypt_block_with_expanded", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_aes_decrypt_block_with_expanded", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_aes_sbox", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_aes_rcon", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_aes128_encrypt_block_into", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_tls13_aes128_gcm_encrypt", &[I64, I64, I64, I64], &[I64]),
    // =========================================================================
    // SIMD AES round intrinsics (Vec16u8 -> Vec16u8, RuntimeValue handles)
    // =========================================================================
    RuntimeFuncSpec::new("rt_simd_aes_round_u8x16", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_simd_aes_round_last_u8x16", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_simd_str_search", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_simd_str_last_index_of", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_simd_str_equal", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_text_to_lower_ascii", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_text_to_upper_ascii", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_to_string", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cstring_to_text", &[I64], &[I64]),
    // =========================================================================
    // Value creation/conversion
    // =========================================================================
    RuntimeFuncSpec::new("rt_value_int", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_float", &[F64], &[I64]),
    RuntimeFuncSpec::new("rt_value_bool", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_nil", &[], &[I64]),
    RuntimeFuncSpec::new("rt_value_as_int", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_as_float", &[I64], &[F64]),
    RuntimeFuncSpec::new("rt_value_raw_i64", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_raw_u64_to_string", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_to_string", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_format_string", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_eq", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_compare", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_native_eq", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_native_neq", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_truthy", &[I64], &[I8]),
    // =========================================================================
    // Math shims (C ABI: f64 in/out — see runtime/src/value/sffi/math.rs).
    // Without these specs, extern declarations fall back to the uniform
    // i64 signature and float call results fail Cranelift verification
    // (fdemote of an i64), forcing interpreter fallback on hot math paths.
    // =========================================================================
    RuntimeFuncSpec::new("rt_math_pow", &[F64, F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_log", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_log10", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_log2", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_exp", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_sqrt", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_cbrt", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_sin", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_cos", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_tan", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_asin", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_acos", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_atan", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_atan2", &[F64, F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_sinh", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_cosh", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_tanh", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_floor", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_ceil", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_round", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_trunc", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_abs", &[F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_hypot", &[F64, F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_gcd", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_math_min", &[F64, F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_max", &[F64, F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_clamp", &[F64, F64, F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_fma", &[F64, F64, F64], &[F64]),
    RuntimeFuncSpec::new("rt_math_nan", &[], &[F64]),
    RuntimeFuncSpec::new("rt_math_inf", &[], &[F64]),
    RuntimeFuncSpec::new("rt_math_is_nan", &[F64], &[I8]),
    RuntimeFuncSpec::new("rt_math_is_inf", &[F64], &[I8]),
    RuntimeFuncSpec::new("rt_math_is_finite", &[F64], &[I8]),
    // =========================================================================
    // Object operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_object_new", &[I32, I32], &[I64]),
    RuntimeFuncSpec::new("rt_object_field_get", &[I64, I32], &[I64]),
    RuntimeFuncSpec::new("rt_object_field_set", &[I64, I32, I64], &[I8]),
    // =========================================================================
    // Closure operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_closure_new", &[I64, I32], &[I64]),
    RuntimeFuncSpec::new("rt_closure_set_capture", &[I64, I32, I64], &[I8]),
    RuntimeFuncSpec::new("rt_closure_get_capture", &[I64, I32], &[I64]),
    RuntimeFuncSpec::new("rt_closure_func_ptr", &[I64], &[I64]),
    // =========================================================================
    // Enum operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_enum_new", &[I32, I32, I64], &[I64]),
    RuntimeFuncSpec::new("rt_enum_check_discriminant", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_enum_id", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_enum_discriminant", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_enum_payload", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_unwrap_or_self", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_is_none", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_is_some", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_option_map", &[I64, I64], &[I64]),
    // =========================================================================
    // Unique pointer operations (GC-collaborative manual memory)
    // =========================================================================
    RuntimeFuncSpec::new("rt_unique_new", &[I64], &[I64]), // value -> unique ptr
    RuntimeFuncSpec::new("rt_unique_get", &[I64], &[I64]), // unique -> value
    RuntimeFuncSpec::new("rt_unique_set", &[I64, I64], &[I64]), // unique, new_value -> success
    RuntimeFuncSpec::new("rt_unique_free", &[I64], &[]),   // unique -> ()
    RuntimeFuncSpec::new("rt_unique_needs_trace", &[I64], &[I64]), // unique -> bool
    // =========================================================================
    // Shared pointer operations (reference-counted, GC-collaborative)
    // =========================================================================
    RuntimeFuncSpec::new("rt_shared_new", &[I64], &[I64]), // value -> shared ptr
    RuntimeFuncSpec::new("rt_shared_get", &[I64], &[I64]), // shared -> value
    RuntimeFuncSpec::new("rt_shared_clone", &[I64], &[I64]), // shared -> shared (inc refcount)
    RuntimeFuncSpec::new("rt_shared_ref_count", &[I64], &[I64]), // shared -> count
    RuntimeFuncSpec::new("rt_shared_release", &[I64], &[I64]), // shared -> freed?
    RuntimeFuncSpec::new("rt_shared_needs_trace", &[I64], &[I64]), // shared -> bool
    RuntimeFuncSpec::new("rt_shared_downgrade", &[I64], &[I64]), // shared -> weak
    // =========================================================================
    // Weak pointer operations (non-owning reference to shared)
    // =========================================================================
    RuntimeFuncSpec::new("rt_weak_new", &[I64, I64], &[I64]), // shared_value, addr -> weak
    RuntimeFuncSpec::new("rt_weak_upgrade", &[I64], &[I64]),  // weak -> shared or NIL
    RuntimeFuncSpec::new("rt_weak_is_valid", &[I64], &[I64]), // weak -> bool
    RuntimeFuncSpec::new("rt_weak_free", &[I64], &[]),        // weak -> ()
    // =========================================================================
    // Handle pointer operations (pool-allocated, index-based)
    // =========================================================================
    RuntimeFuncSpec::new("rt_handle_new", &[I64], &[I64]), // value -> handle
    RuntimeFuncSpec::new("rt_handle_get", &[I64], &[I64]), // handle -> value
    RuntimeFuncSpec::new("rt_handle_set", &[I64, I64], &[I64]), // handle, new_value -> success
    RuntimeFuncSpec::new("rt_handle_free", &[I64], &[]),   // handle -> ()
    RuntimeFuncSpec::new("rt_handle_is_valid", &[I64], &[I64]), // handle -> bool
    // =========================================================================
    // Raw memory allocation (zero-cost struct support)
    // =========================================================================
    RuntimeFuncSpec::new("rt_alloc", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_free", &[I64], &[]),
    RuntimeFuncSpec::new("rt_ptr_to_value", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_to_ptr", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_dyn_torch_tensor_from_bits_1d", &[I64, I64], &[I64]),
    // =========================================================================
    // Port I/O (baremetal x86 — classified as Core by tier_of fallthrough)
    // =========================================================================
    RuntimeFuncSpec::new("rt_port_inb", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_port_outb", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_port_inw", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_port_outw", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_port_inl", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_port_outl", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_port_io_wait", &[], &[I64]),
    // =========================================================================
    // CPU control registers / interrupts (baremetal — Core tier)
    // =========================================================================
    RuntimeFuncSpec::new("rt_cli", &[], &[I64]),
    RuntimeFuncSpec::new("rt_sti", &[], &[I64]),
    RuntimeFuncSpec::new("rt_hlt", &[], &[I64]),
    RuntimeFuncSpec::new("rt_lgdt", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_lidt", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_ltr", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_read_cr2", &[], &[I64]),
    RuntimeFuncSpec::new("rt_read_cr3", &[], &[I64]),
    RuntimeFuncSpec::new("rt_write_cr3", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_invlpg", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_read_msr", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_write_msr", &[I64, I64], &[I64]),
    // =========================================================================
    // MMIO (memory-mapped I/O — Core tier for baremetal device drivers)
    // =========================================================================
    RuntimeFuncSpec::new("rt_mmio_read_u8", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_mmio_write_u8", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_mmio_read_u16", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_mmio_write_u16", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_mmio_read_u32", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_mmio_write_u32", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_mmio_read_u32", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_mmio_read_u64", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_mmio_write_u32", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_virtq_desc_write", &[I64, I64, I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_dma_bytes_to_array", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_data_ptr", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_data_ptr_text", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_data_ptr_u8", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_header_ptr", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_set_len_known", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_set_len_known_text", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_bytes_u8_unchecked", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_bytes_u8_data_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_bytes_u64_le_unchecked", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_bytes_u8_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_bytes_u32_le_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_bytes_u64_le_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_bytes_u8_set", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_bytes_u8_push", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u32_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_words_u32_unchecked", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_words_u32_data_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_words_u32_push", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u32_push_known_at", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u32_push_known_data_at", &[I64, I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u32_store_known_data_at", &[I64, I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u32_set", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u64_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_words_u64_unchecked", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_words_u64_data_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_words_u64_data_at_checked", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_words_u64_raw_data_at", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_numeric_xor_sum_u64_data", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_numeric_xor_sum_u64_repeated_data", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_typed_words_u64_push", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u64_push_known_at", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u64_push_known_data_at", &[I64, I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u64_store_known_data_at", &[I64, I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_typed_words_u64_set", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_memory_barrier", &[], &[]),
    RuntimeFuncSpec::new("rt_load_barrier", &[], &[]),
    RuntimeFuncSpec::new("rt_store_barrier", &[], &[]),
    RuntimeFuncSpec::new("rt_arm_virtq_base", &[], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_queue_base", &[], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_dma_base", &[], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_configure_queue", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtq_used_idx", &[], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtq_reset", &[], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtq_push_avail", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_wait_completion", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_status_u8", &[], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_prepare_read", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_read_sector_direct", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_read_prefix", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_read_hello_smf", &[], &[I64]),
    RuntimeFuncSpec::new("rt_arm_virtio_blk_sector_bytes", &[], &[I64]),
    RuntimeFuncSpec::new("rt_array_get_byte_raw", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_array_len_u32", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_array_get_byte_u32", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_array_get_u16_le", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_array_get_u32_le", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_arm_array_append_bytes", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("arm_fs_exec_print_success_marker", &[], &[I64]),
    // =========================================================================
    // Async/concurrency operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_wait", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_future_new", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_future_await", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_future_is_ready", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_future_get_result", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_future_all", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_future_race", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_future_resolve", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_future_reject", &[I64], &[I64]),
    // Async state machine support (similar to generators)
    RuntimeFuncSpec::new("rt_async_get_state", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_async_set_state", &[I64, I64], &[]),
    RuntimeFuncSpec::new("rt_async_get_ctx", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_async_mark_done", &[I64], &[]),
    RuntimeFuncSpec::new("rt_actor_spawn", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_actor_send", &[I64, I64], &[]),
    RuntimeFuncSpec::new("rt_actor_recv", &[], &[I64]),
    RuntimeFuncSpec::new("rt_actor_join", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_actor_reply", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_actor_id", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_actor_is_alive", &[I64], &[I64]),
    // =========================================================================
    // Channel operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_channel_new", &[], &[I64]),
    RuntimeFuncSpec::new("rt_channel_send", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_channel_recv", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_channel_try_recv", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_channel_recv_timeout", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_channel_close", &[I64], &[]),
    RuntimeFuncSpec::new("rt_channel_is_closed", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_channel_id", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_channel_free", &[I64], &[]),
    // =========================================================================
    // Executor operations (thread pool / manual mode)
    // =========================================================================
    RuntimeFuncSpec::new("rt_executor_set_mode", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_executor_get_mode", &[], &[I64]),
    RuntimeFuncSpec::new("rt_executor_start", &[], &[]),
    RuntimeFuncSpec::new("rt_executor_set_workers", &[I64], &[]),
    RuntimeFuncSpec::new("rt_executor_poll", &[], &[I64]),
    RuntimeFuncSpec::new("rt_executor_poll_all", &[], &[I64]),
    RuntimeFuncSpec::new("rt_executor_pending_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_executor_shutdown", &[], &[]),
    RuntimeFuncSpec::new("rt_executor_is_manual", &[], &[I64]),
    RuntimeFuncSpec::new("rt_executor_current_task_id", &[], &[I64]),
    RuntimeFuncSpec::new("rt_fiber_enter_task_id", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_fiber_exit_task_id", &[I64], &[]),
    RuntimeFuncSpec::new("rt_fiber_current_task_id", &[], &[I64]),
    RuntimeFuncSpec::new("rt_current_task_id", &[], &[I64]),
    // =========================================================================
    // Async runtime scheduler (cooperative scheduling)
    // =========================================================================
    RuntimeFuncSpec::new("rt_async_spawn", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_async_schedule_await", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_async_run_until_complete", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_async_spawn_task", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_async_poll_tasks", &[], &[I64]),
    RuntimeFuncSpec::new("rt_async_current_task_id", &[], &[I64]),
    // =========================================================================
    // Isolated Thread operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_thread_spawn_isolated", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_spawn_isolated_with_args", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_join", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_is_done", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_id", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_free", &[I64], &[]),
    RuntimeFuncSpec::new("rt_pool_submit", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_pool_join", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_pool_is_done", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_pool_set_parallelism", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_pool_get_parallelism", &[], &[I64]),
    RuntimeFuncSpec::new("rt_pool_uses_global_fifo_queue", &[], &[I64]),
    RuntimeFuncSpec::new("rt_pool_uses_work_stealing", &[], &[I64]),
    RuntimeFuncSpec::new("rt_pool_safepoint", &[], &[I64]),
    RuntimeFuncSpec::new("rt_pool_submitted_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_pool_completed_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_pool_pending_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_pool_busy_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_pool_blocked_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_thread_available_parallelism", &[], &[I64]),
    RuntimeFuncSpec::new("spl_thread_cpu_count", &[], &[I64]),
    RuntimeFuncSpec::new("spl_thread_create", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("spl_thread_join", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_thread_detach", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_thread_current_id", &[], &[I64]),
    RuntimeFuncSpec::new("spl_thread_sleep", &[I64], &[]),
    RuntimeFuncSpec::new("spl_thread_yield", &[], &[]),
    RuntimeFuncSpec::new("spl_mutex_create", &[], &[I64]),
    RuntimeFuncSpec::new("spl_mutex_lock", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_mutex_try_lock", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_mutex_unlock", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_mutex_destroy", &[I64], &[]),
    RuntimeFuncSpec::new("spl_condvar_create", &[], &[I64]),
    RuntimeFuncSpec::new("spl_condvar_wait", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("spl_condvar_wait_timeout", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("spl_condvar_signal", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_condvar_broadcast", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_condvar_destroy", &[I64], &[]),
    RuntimeFuncSpec::new("rt_thread_sleep", &[I64], &[]),
    RuntimeFuncSpec::new("rt_thread_yield", &[], &[]),
    // =========================================================================
    // Async I/O driver (epoll/kqueue/IOCP backend)
    // =========================================================================
    RuntimeFuncSpec::new("rt_driver_create", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_destroy", &[I64], &[]),
    RuntimeFuncSpec::new("rt_driver_submit_accept", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_connect", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_recv", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_send", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_sendfile", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_read", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_write", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_open", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_close", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_fsync", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_submit_timeout", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_flush", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_poll", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_poll_id", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_poll_result", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_poll_flags", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_poll_data", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_poll_data_len", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_cancel", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_backend_name", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_supports_sendfile", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_driver_supports_zero_copy", &[I64], &[I64]),
    // =========================================================================
    // Generator operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_generator_new", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_generator_next", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_generator_get_state", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_generator_set_state", &[I64, I64], &[]),
    RuntimeFuncSpec::new("rt_generator_store_slot", &[I64, I64, I64], &[]),
    RuntimeFuncSpec::new("rt_generator_load_slot", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_generator_get_ctx", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_generator_mark_done", &[I64], &[]),
    // =========================================================================
    // Interpreter bridge SFFI (for hybrid execution)
    // =========================================================================
    // rt_interp_call(func_name_ptr: i64, func_name_len: i64, argc: i64, argv: i64) -> i64
    RuntimeFuncSpec::new("rt_interp_call", &[I64, I64, I64, I64], &[I64]),
    // rt_interp_eval(expr_index: i64) -> i64
    RuntimeFuncSpec::new("rt_interp_eval", &[I64], &[I64]),
    // =========================================================================
    // Error handling
    // =========================================================================
    RuntimeFuncSpec::new("rt_function_not_found", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_method_not_found", &[I64, I64, I64, I64], &[I64]),
    // =========================================================================
    // Contract checking (Design by Contract)
    // =========================================================================
    // simple_contract_check(condition: i64, kind: i64, func_name_ptr: i64, func_name_len: i64)
    RuntimeFuncSpec::new("simple_contract_check", &[I64, I64, I64, I64], &[]),
    // simple_contract_check_msg(condition: i64, kind: i64, func_name_ptr: i64, func_name_len: i64, msg_ptr: i64, msg_len: i64)
    RuntimeFuncSpec::new("simple_contract_check_msg", &[I64, I64, I64, I64, I64, I64], &[]),
    // Contract violation object functions (CTR-050-054)
    // rt_contract_violation_new(kind: i64, func_name_ptr: i64, func_name_len: i64, msg_ptr: i64, msg_len: i64) -> RuntimeValue
    RuntimeFuncSpec::new("rt_contract_violation_new", &[I64, I64, I64, I64, I64], &[I64]),
    // rt_contract_violation_kind(violation: RuntimeValue) -> i64
    RuntimeFuncSpec::new("rt_contract_violation_kind", &[I64], &[I64]),
    // rt_contract_violation_func_name(violation: RuntimeValue) -> RuntimeValue (string)
    RuntimeFuncSpec::new("rt_contract_violation_func_name", &[I64], &[I64]),
    // rt_contract_violation_message(violation: RuntimeValue) -> RuntimeValue (string or NIL)
    RuntimeFuncSpec::new("rt_contract_violation_message", &[I64], &[I64]),
    // rt_is_contract_violation(value: RuntimeValue) -> i64 (1=yes, 0=no)
    RuntimeFuncSpec::new("rt_is_contract_violation", &[I64], &[I64]),
    // rt_contract_violation_free(violation: RuntimeValue)
    RuntimeFuncSpec::new("rt_contract_violation_free", &[I64], &[]),
    // =========================================================================
    // I/O operations (print, capture)
    // =========================================================================
    RuntimeFuncSpec::new("rt_print_str", &[I64, I64], &[]), // ptr, len
    RuntimeFuncSpec::new("rt_println_str", &[I64, I64], &[]), // ptr, len
    RuntimeFuncSpec::new("rt_eprint_str", &[I64, I64], &[]), // ptr, len
    RuntimeFuncSpec::new("rt_eprintln_str", &[I64, I64], &[]), // ptr, len
    RuntimeFuncSpec::new("rt_print_value", &[I64], &[]),    // RuntimeValue
    RuntimeFuncSpec::new("rt_println_value", &[I64], &[]),  // RuntimeValue
    RuntimeFuncSpec::new("rt_eprint_value", &[I64], &[]),   // RuntimeValue
    RuntimeFuncSpec::new("rt_eprintln_value", &[I64], &[]), // RuntimeValue
    RuntimeFuncSpec::new("rt_read_stdin_line", &[], &[I64]), // -> RuntimeValue (string)
    RuntimeFuncSpec::new("rt_capture_stdout_start", &[], &[]),
    RuntimeFuncSpec::new("rt_capture_stderr_start", &[], &[]),
    // =========================================================================
    // Doctest I/O operations (file discovery)
    // =========================================================================
    RuntimeFuncSpec::new("doctest_read_file", &[I64], &[I64]), // path -> content (RuntimeValue)
    RuntimeFuncSpec::new("doctest_path_exists", &[I64], &[I64]), // path -> bool (RuntimeValue)
    RuntimeFuncSpec::new("doctest_is_file", &[I64], &[I64]),   // path -> bool (RuntimeValue)
    RuntimeFuncSpec::new("doctest_is_dir", &[I64], &[I64]),    // path -> bool (RuntimeValue)
    RuntimeFuncSpec::new("doctest_walk_directory", &[I64, I64, I64], &[I64]), // root, include, exclude -> array (RuntimeValue)
    RuntimeFuncSpec::new("doctest_path_has_extension", &[I64, I64], &[I64]),  // path, ext -> bool (RuntimeValue)
    RuntimeFuncSpec::new("doctest_path_contains", &[I64, I64], &[I64]),       // path, pattern -> bool (RuntimeValue)
    // =========================================================================
    // GPU work item identification
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_global_id", &[I32], &[I64]), // dim -> id
    RuntimeFuncSpec::new("rt_gpu_local_id", &[I32], &[I64]),  // dim -> id
    RuntimeFuncSpec::new("rt_gpu_group_id", &[I32], &[I64]),  // dim -> id
    RuntimeFuncSpec::new("rt_gpu_global_size", &[I32], &[I64]), // dim -> size
    RuntimeFuncSpec::new("rt_gpu_local_size", &[I32], &[I64]), // dim -> size
    RuntimeFuncSpec::new("rt_gpu_num_groups", &[I32], &[I64]), // dim -> count
    // =========================================================================
    // GPU synchronization
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_barrier", &[], &[]),      // () -> ()
    RuntimeFuncSpec::new("rt_gpu_mem_fence", &[I32], &[]), // scope -> ()
    // =========================================================================
    // GPU atomic operations (i64)
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_atomic_add_i64", &[I64, I64], &[I64]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_sub_i64", &[I64, I64], &[I64]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_xchg_i64", &[I64, I64], &[I64]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_cmpxchg_i64", &[I64, I64, I64], &[I64]), // ptr, expected, new -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_min_i64", &[I64, I64], &[I64]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_max_i64", &[I64, I64], &[I64]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_and_i64", &[I64, I64], &[I64]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_or_i64", &[I64, I64], &[I64]),  // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_xor_i64", &[I64, I64], &[I64]), // ptr, value -> old
    // =========================================================================
    // GPU atomic operations (u32)
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_atomic_add_u32", &[I64, I32], &[I32]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_sub_u32", &[I64, I32], &[I32]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_xchg_u32", &[I64, I32], &[I32]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_cmpxchg_u32", &[I64, I32, I32], &[I32]), // ptr, expected, new -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_min_u32", &[I64, I32], &[I32]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_max_u32", &[I64, I32], &[I32]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_and_u32", &[I64, I32], &[I32]), // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_or_u32", &[I64, I32], &[I32]),  // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_xor_u32", &[I64, I32], &[I32]), // ptr, value -> old
    // =========================================================================
    // GPU shared memory
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_shared_alloc", &[I64], &[I64]), // size -> ptr
    RuntimeFuncSpec::new("rt_gpu_shared_reset", &[], &[]),       // () -> ()
    RuntimeFuncSpec::new("rt_host_gpu_lane_event", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_lane_reset", &[], &[]),
    RuntimeFuncSpec::new("rt_host_gpu_lane_event_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_lane_begin_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_lane_end_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_lane_last_lane", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_lane_last_phase", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_reset", &[], &[]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_emit", &[I64, I64, I64, I64], &[I64]),
    // Native Draw IR queue packets carry their serialized payload across the
    // runtime boundary as a text pointer (the C facade owns the storage).
    RuntimeFuncSpec::new("rt_host_gpu_queue_emit_payload_text", &[I64, I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_drain", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_submit", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_complete", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_packet_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_submitted_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_completed_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_in_flight_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_last_status", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_last_backend_handle", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_last_device_time_us", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_last_payload_size", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_last_payload_hash", &[], &[I64]),
    RuntimeFuncSpec::new("rt_host_gpu_queue_last_payload_text", &[], &[I64]),
    // =========================================================================
    // GPU kernel launch
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_launch", &[I64, I32, I32, I32, I32, I32, I32], &[I32]), // kernel, gx,gy,gz, lx,ly,lz -> status
    RuntimeFuncSpec::new("rt_gpu_launch_1d", &[I64, I32, I32], &[I32]), // kernel, global, local -> status
    // =========================================================================
    // Vulkan GPU backend operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_vk_available", &[], &[I32]), // () -> available (1=yes, 0=no)
    RuntimeFuncSpec::new("rt_vk_device_create", &[], &[I64]), // () -> device_handle
    RuntimeFuncSpec::new("rt_vk_device_free", &[I64], &[I32]), // device_handle -> status
    RuntimeFuncSpec::new("rt_vk_device_sync", &[I64], &[I32]), // device_handle -> status
    RuntimeFuncSpec::new("rt_vk_buffer_alloc", &[I64, I64], &[I64]), // device_handle, size -> buffer_handle
    RuntimeFuncSpec::new("rt_vk_buffer_free", &[I64], &[I32]), // buffer_handle -> status
    RuntimeFuncSpec::new("rt_vk_buffer_upload", &[I64, I64, I64], &[I32]), // buffer_handle, data_ptr, size -> status
    RuntimeFuncSpec::new("rt_vk_buffer_download", &[I64, I64, I64], &[I32]), // buffer_handle, data_ptr, size -> status
    RuntimeFuncSpec::new("rt_vk_kernel_compile", &[I64, I64, I64], &[I64]), // device_handle, spirv_ptr, spirv_len -> pipeline_handle
    RuntimeFuncSpec::new("rt_vk_kernel_free", &[I64], &[I32]),              // pipeline_handle -> status
    RuntimeFuncSpec::new(
        "rt_vk_kernel_launch",
        &[I64, I64, I64, I32, I32, I32, I32, I32, I32],
        &[I32],
    ), // pipeline, buffers_ptr, count, gx,gy,gz, lx,ly,lz -> status
    RuntimeFuncSpec::new("rt_vk_kernel_launch_1d", &[I64, I64, I64, I32], &[I32]), // pipeline, buffers_ptr, count, global_size -> status
    // =========================================================================
    // Vulkan Graphics Pipeline operations
    // =========================================================================
    // Render Pass
    RuntimeFuncSpec::new("rt_vk_render_pass_create_simple", &[I64, I32], &[I64]), // device, color_format -> handle
    RuntimeFuncSpec::new("rt_vk_render_pass_create_with_depth", &[I64, I32, I32], &[I64]), // device, color_format, depth_format -> handle
    RuntimeFuncSpec::new("rt_vk_render_pass_free", &[I64], &[I32]),                        // handle -> status
    RuntimeFuncSpec::new("rt_vk_render_pass_get_color_format", &[I64], &[I32]),            // handle -> format
    // Shader Module
    RuntimeFuncSpec::new("rt_vk_shader_module_create", &[I64, I64, I64], &[I64]), // device, spirv_ptr, spirv_len -> handle
    RuntimeFuncSpec::new("rt_vk_shader_module_free", &[I64], &[I32]),             // handle -> status
    // Graphics Pipeline
    RuntimeFuncSpec::new(
        "rt_vk_graphics_pipeline_create",
        &[I64, I64, I64, I64, I32, I32],
        &[I64],
    ), // device, rp, vert, frag, w, h -> handle
    RuntimeFuncSpec::new("rt_vk_graphics_pipeline_free", &[I64], &[I32]), // handle -> status
    // Framebuffer
    RuntimeFuncSpec::new("rt_vk_framebuffer_create", &[I64, I64, I64, I32, I32], &[I64]), // device, rp, view, w, h -> handle
    RuntimeFuncSpec::new(
        "rt_vk_framebuffer_create_for_swapchain",
        &[I64, I64, I64, I64, I32],
        &[I32],
    ), // device, rp, sc, out, max -> count
    RuntimeFuncSpec::new("rt_vk_framebuffer_free", &[I64], &[I32]),                       // handle -> status
    RuntimeFuncSpec::new("rt_vk_framebuffer_get_dimensions", &[I64, I64, I64], &[I32]), // handle, w_ptr, h_ptr -> status
    // =========================================================================
    // Vulkan Image operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_vk_image_create_2d", &[I64, I32, I32, I32, I32], &[I64]), // device, w, h, fmt, usage -> handle
    RuntimeFuncSpec::new("rt_vk_image_free", &[I64], &[I32]),                          // handle -> status
    RuntimeFuncSpec::new("rt_vk_image_upload", &[I64, I64, I64], &[I32]),              // handle, data, len -> status
    RuntimeFuncSpec::new("rt_vk_image_download", &[I64, I64, I64], &[I32]),            // handle, data, len -> status
    RuntimeFuncSpec::new("rt_vk_image_get_view", &[I64], &[I64]),                      // handle -> view
    RuntimeFuncSpec::new("rt_vk_sampler_create", &[I64, I32, I32], &[I64]), // device, filter, addr_mode -> handle
    RuntimeFuncSpec::new("rt_vk_sampler_free", &[I64], &[I32]),             // handle -> status
    // =========================================================================
    // Vulkan Command Buffer operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_vk_command_buffer_begin", &[I64], &[I64]), // device -> handle
    RuntimeFuncSpec::new("rt_vk_command_buffer_end", &[I64], &[I32]),   // cmd -> status
    RuntimeFuncSpec::new("rt_vk_command_buffer_submit", &[I64], &[I32]), // cmd -> status
    RuntimeFuncSpec::new("rt_vk_command_buffer_free", &[I64], &[I32]),  // cmd -> status
    RuntimeFuncSpec::new(
        "rt_vk_cmd_begin_render_pass",
        &[I64, I64, I64, F64, F64, F64, F64],
        &[I32],
    ), // cmd, rp, fb, r, g, b, a -> status
    RuntimeFuncSpec::new("rt_vk_cmd_end_render_pass", &[I64], &[I32]),  // cmd -> status
    RuntimeFuncSpec::new("rt_vk_cmd_bind_pipeline", &[I64, I64], &[I32]), // cmd, pipeline -> status
    RuntimeFuncSpec::new("rt_vk_cmd_bind_vertex_buffer", &[I64, I64, I32], &[I32]), // cmd, buffer, binding -> status
    RuntimeFuncSpec::new("rt_vk_cmd_bind_index_buffer", &[I64, I64, I32], &[I32]), // cmd, buffer, index_type -> status
    RuntimeFuncSpec::new("rt_vk_cmd_draw", &[I64, I32, I32, I32, I32], &[I32]), // cmd, vert, inst, first_vert, first_inst -> status
    RuntimeFuncSpec::new("rt_vk_cmd_draw_indexed", &[I64, I32, I32, I32, I32, I32], &[I32]), // cmd, idx, inst, first_idx, vert_off, first_inst -> status
    RuntimeFuncSpec::new("rt_vk_cmd_set_viewport", &[I64, F64, F64, F64, F64], &[I32]), // cmd, x, y, w, h -> status
    RuntimeFuncSpec::new("rt_vk_cmd_set_scissor", &[I64, I32, I32, I32, I32], &[I32]),  // cmd, x, y, w, h -> status
    // Metal GPU backend operations
    RuntimeFuncSpec::new("rt_metal_init", &[], &[I64]),
    RuntimeFuncSpec::new("rt_metal_is_available", &[], &[I64]),
    RuntimeFuncSpec::new("rt_metal_device_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_metal_device_name", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_device_memory", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_create_device", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_device", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_alloc_buffer", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_free_buffer", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_buffer_upload", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_buffer_download", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_compile_shader", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_shader", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_create_compute_pipeline", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_pipeline", &[I64], &[I64]),
    RuntimeFuncSpec::new(
        "rt_metal_dispatch_compute",
        &[I64, I64, I64, I64, I64, I64, I64, I64],
        &[I64],
    ),
    RuntimeFuncSpec::new("rt_metal_create_render_pipeline", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_render_pipeline", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_create_texture", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_free_texture", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_begin_render_pass", &[I64, I64, F64, F64, F64, F64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_end_render_pass", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_draw_indexed", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_draw_primitives", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_create_command_queue", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_command_queue", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_create_command_buffer", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_command_buffer", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_commit_command_buffer", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_wait_completed", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_create_compute_encoder", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_end_compute_encoder", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_compute_encoder", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_set_buffer", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_set_bytes", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_get_last_error", &[], &[I64]),
    RuntimeFuncSpec::new("rt_metal_create_sampler", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_sampler", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_set_viewport", &[I64, F64, F64, F64, F64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_set_scissor", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_create_swapchain", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_destroy_swapchain", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_metal_present", &[I64], &[I64]),
    RuntimeFuncSpec::new(
        "rt_metal_run_blit_frame",
        &[I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64],
        &[I64],
    ),
    RuntimeFuncSpec::new(
        "rt_metal_run_compute_frame",
        &[I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64, I64],
        &[I64],
    ),
    RuntimeFuncSpec::new(
        "rt_directx_execute_readback_checked",
        &[I64, I64, I64, I64, I64, I64],
        &[I64],
    ),
    RuntimeFuncSpec::new("rt_directx_hardware_adapter_identity", &[], &[I64]),
    // =========================================================================
    // Parallel iterator operations (#415)
    // =========================================================================
    // rt_par_map(input_ptr, input_len, closure_ptr, backend) -> result_ptr
    RuntimeFuncSpec::new("rt_par_map", &[I64, I64, I64, I32], &[I64]),
    // rt_par_reduce(input_ptr, input_len, initial, closure_ptr, backend) -> result
    RuntimeFuncSpec::new("rt_par_reduce", &[I64, I64, I64, I64, I32], &[I64]),
    // rt_par_filter(input_ptr, input_len, predicate_ptr, backend) -> result_ptr
    RuntimeFuncSpec::new("rt_par_filter", &[I64, I64, I64, I32], &[I64]),
    // rt_par_for_each(input_ptr, input_len, closure_ptr, backend) -> ()
    RuntimeFuncSpec::new("rt_par_for_each", &[I64, I64, I64, I32], &[]),
    // =========================================================================
    // TCP networking operations
    // =========================================================================
    // native_tcp_bind(addr_ptr: i64, addr_len: i64) -> (handle: i64, error_code: i64)
    RuntimeFuncSpec::new("native_tcp_bind", &[I64, I64], &[I64, I64]),
    // native_tcp_accept(handle: i64) -> (stream_handle: i64, peer_addr_ptr: i64, error_code: i64)
    RuntimeFuncSpec::new("native_tcp_accept", &[I64], &[I64, I64, I64]),
    // native_tcp_connect(addr_ptr: i64, addr_len: i64) -> (handle: i64, local_addr_ptr: i64, error_code: i64)
    RuntimeFuncSpec::new("native_tcp_connect", &[I64, I64], &[I64, I64, I64]),
    // native_tcp_connect_timeout(addr_ptr: i64, addr_len: i64, timeout_ns: i64) -> (handle: i64, local_addr_ptr: i64, error_code: i64)
    RuntimeFuncSpec::new("native_tcp_connect_timeout", &[I64, I64, I64], &[I64, I64, I64]),
    // native_tcp_read(handle: i64, buf_ptr: i64, buf_len: i64) -> (bytes_read: i64, error_code: i64)
    RuntimeFuncSpec::new("native_tcp_read", &[I64, I64, I64], &[I64, I64]),
    // native_tcp_write(handle: i64, data_ptr: i64, data_len: i64) -> (bytes_written: i64, error_code: i64)
    RuntimeFuncSpec::new("native_tcp_write", &[I64, I64, I64], &[I64, I64]),
    // native_tcp_flush(handle: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_tcp_flush", &[I64], &[I64]),
    // native_tcp_shutdown(handle: i64, how: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_tcp_shutdown", &[I64, I64], &[I64]),
    // native_tcp_close(handle: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_tcp_close", &[I64], &[I64]),
    // native_tcp_set_backlog(handle: i64, backlog: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_tcp_set_backlog", &[I64, I64], &[I64]),
    // native_tcp_set_nodelay(handle: i64, nodelay: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_tcp_set_nodelay", &[I64, I64], &[I64]),
    // native_tcp_set_keepalive(handle: i64, keepalive_ns: i64) -> error_code: i64 (0 = disabled, >0 = enabled with timeout)
    RuntimeFuncSpec::new("native_tcp_set_keepalive", &[I64, I64], &[I64]),
    // native_tcp_set_read_timeout(handle: i64, timeout_ns: i64) -> error_code: i64 (0 = no timeout)
    RuntimeFuncSpec::new("native_tcp_set_read_timeout", &[I64, I64], &[I64]),
    // native_tcp_set_write_timeout(handle: i64, timeout_ns: i64) -> error_code: i64 (0 = no timeout)
    RuntimeFuncSpec::new("native_tcp_set_write_timeout", &[I64, I64], &[I64]),
    // native_tcp_get_nodelay(handle: i64) -> (nodelay: i64, error_code: i64)
    RuntimeFuncSpec::new("native_tcp_get_nodelay", &[I64], &[I64, I64]),
    // native_tcp_peek(handle: i64, buf_ptr: i64, buf_len: i64) -> (bytes_peeked: i64, error_code: i64)
    RuntimeFuncSpec::new("native_tcp_peek", &[I64, I64, I64], &[I64, I64]),
    // rt_io_tcp_read_exact(handle: i64, size: i64) -> [u8]
    RuntimeFuncSpec::new("rt_io_tcp_read_exact", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_io_tcp_read_exact_len", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_io_tcp_drain_line", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_io_tcp_write_text_read_exact_len", &[I64, I64], &[I64]),
    // rt_io_tcp_socket_create(family: i64) -> fd: i64
    RuntimeFuncSpec::new("rt_io_tcp_socket_create", &[I64], &[I64]),
    // rt_io_tcp_set_reuseaddr(fd: i64, enabled: i64) -> ok: i64
    RuntimeFuncSpec::new("rt_io_tcp_set_reuseaddr", &[I64, I64], &[I64]),
    // rt_io_tcp_set_reuseport(fd: i64, enabled: i64) -> ok: i64
    RuntimeFuncSpec::new("rt_io_tcp_set_reuseport", &[I64, I64], &[I64]),
    // rt_io_tcp_set_nonblocking(fd: i64, enabled: i64) -> ok: i64
    RuntimeFuncSpec::new("rt_io_tcp_set_nonblocking", &[I64, I64], &[I64]),
    // rt_io_tcp_set_nodelay(fd: i64, enabled: i64) -> ok: i64
    RuntimeFuncSpec::new("rt_io_tcp_set_nodelay", &[I64, I64], &[I64]),
    // rt_io_tcp_bind_fd(fd: i64, addr_ptr: i64) -> ok: i64
    RuntimeFuncSpec::new("rt_io_tcp_bind_fd", &[I64, I64], &[I64]),
    // rt_io_tcp_listen(fd: i64, backlog: i64) -> ok: i64
    RuntimeFuncSpec::new("rt_io_tcp_listen", &[I64, I64], &[I64]),
    // rt_io_tcp_accept(fd: i64) -> client_fd: i64
    RuntimeFuncSpec::new("rt_io_tcp_accept", &[I64], &[I64]),
    // rt_io_tcp_read(fd: i64, size: i64) -> array_ptr: i64
    RuntimeFuncSpec::new("rt_io_tcp_read", &[I64, I64], &[I64]),
    // rt_io_tcp_write_text(fd: i64, data_ptr: i64) -> bytes_written: i64
    RuntimeFuncSpec::new("rt_io_tcp_write_text", &[I64, I64], &[I64]),
    // rt_io_tcp_close(fd: i64) -> ok: i64
    RuntimeFuncSpec::new("rt_io_tcp_close", &[I64], &[I64]),
    // rt_event_loop_create() -> epfd: i64
    RuntimeFuncSpec::new("rt_event_loop_create", &[], &[I64]),
    // rt_event_loop_register(epfd: i64, fd: i64, interest: i64, token: i64, edge: i64) -> ok: i64
    RuntimeFuncSpec::new("rt_event_loop_register", &[I64, I64, I64, I64, I64], &[I64]),
    // rt_event_loop_poll(epfd: i64, max_events: i64, timeout_ms: i64) -> array_ptr: i64
    RuntimeFuncSpec::new("rt_event_loop_poll", &[I64, I64, I64], &[I64]),
    // rt_event_loop_poll_get_fd(index: i64) -> fd: i64
    RuntimeFuncSpec::new("rt_event_loop_poll_get_fd", &[I64], &[I64]),
    // =========================================================================
    // UDP networking operations
    // =========================================================================
    // native_udp_bind(addr_ptr: i64, addr_len: i64) -> (handle: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_bind", &[I64, I64], &[I64, I64]),
    // native_udp_connect(handle: i64, addr_ptr: i64, addr_len: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_connect", &[I64, I64, I64], &[I64]),
    // native_udp_recv_from(handle: i64, buf_ptr: i64, buf_len: i64) -> (bytes_recv: i64, peer_addr_ptr: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_recv_from", &[I64, I64, I64], &[I64, I64, I64]),
    // native_udp_recv(handle: i64, buf_ptr: i64, buf_len: i64) -> (bytes_recv: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_recv", &[I64, I64, I64], &[I64, I64]),
    // native_udp_send_to(handle: i64, data_ptr: i64, data_len: i64, addr_ptr: i64, addr_len: i64) -> (bytes_sent: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_send_to", &[I64, I64, I64, I64, I64], &[I64, I64]),
    // native_udp_send(handle: i64, data_ptr: i64, data_len: i64) -> (bytes_sent: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_send", &[I64, I64, I64], &[I64, I64]),
    // native_udp_peek_from(handle: i64, buf_ptr: i64, buf_len: i64) -> (bytes_peeked: i64, peer_addr_ptr: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_peek_from", &[I64, I64, I64], &[I64, I64, I64]),
    // native_udp_peek(handle: i64, buf_ptr: i64, buf_len: i64) -> (bytes_peeked: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_peek", &[I64, I64, I64], &[I64, I64]),
    // native_udp_peer_addr(handle: i64) -> (addr_ptr: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_peer_addr", &[I64], &[I64, I64]),
    // native_udp_set_broadcast(handle: i64, broadcast: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_set_broadcast", &[I64, I64], &[I64]),
    // native_udp_set_multicast_loop(handle: i64, on: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_set_multicast_loop", &[I64, I64], &[I64]),
    // native_udp_set_multicast_ttl(handle: i64, ttl: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_set_multicast_ttl", &[I64, I64], &[I64]),
    // native_udp_set_ttl(handle: i64, ttl: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_set_ttl", &[I64, I64], &[I64]),
    // native_udp_set_read_timeout(handle: i64, timeout_ns: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_set_read_timeout", &[I64, I64], &[I64]),
    // native_udp_set_write_timeout(handle: i64, timeout_ns: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_set_write_timeout", &[I64, I64], &[I64]),
    // native_udp_get_broadcast(handle: i64) -> (broadcast: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_get_broadcast", &[I64], &[I64, I64]),
    // native_udp_get_ttl(handle: i64) -> (ttl: i64, error_code: i64)
    RuntimeFuncSpec::new("native_udp_get_ttl", &[I64], &[I64, I64]),
    // native_udp_join_multicast_v4(handle: i64, multiaddr: i64, interface: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_join_multicast_v4", &[I64, I64, I64], &[I64]),
    // native_udp_leave_multicast_v4(handle: i64, multiaddr: i64, interface: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_leave_multicast_v4", &[I64, I64, I64], &[I64]),
    // native_udp_join_multicast_v6(handle: i64, multiaddr_ptr: i64, interface: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_join_multicast_v6", &[I64, I64, I64], &[I64]),
    // native_udp_leave_multicast_v6(handle: i64, multiaddr_ptr: i64, interface: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_leave_multicast_v6", &[I64, I64, I64], &[I64]),
    // native_udp_close(handle: i64) -> error_code: i64
    RuntimeFuncSpec::new("native_udp_close", &[I64], &[I64]),
    // =========================================================================
    // HTTP networking operations
    // =========================================================================
    // native_http_send(request_ptr: i64, timeout_ns: i64) -> (response_ptr: i64, error_code: i64)
    RuntimeFuncSpec::new("native_http_send", &[I64, I64], &[I64, I64]),
    // =========================================================================
    // Coverage instrumentation operations
    // =========================================================================
    // rt_coverage_decision_probe(decision_id: u32, result: bool, file: *const i8, line: u32, column: u32) -> ()
    RuntimeFuncSpec::new("rt_coverage_decision_probe", &[I32, I8, I64, I32, I32], &[]),
    // rt_coverage_condition_probe(decision_id: u32, condition_id: u32, result: bool, file: *const i8, line: u32, column: u32) -> ()
    RuntimeFuncSpec::new("rt_coverage_condition_probe", &[I32, I32, I8, I64, I32, I32], &[]),
    // rt_coverage_path_probe(path_id: u32, block_id: u32) -> ()
    RuntimeFuncSpec::new("rt_coverage_path_probe", &[I32, I32], &[]),
    // rt_coverage_path_finalize(path_id: u32) -> ()
    RuntimeFuncSpec::new("rt_coverage_path_finalize", &[I32], &[]),
    // rt_coverage_dump_sdn() -> *mut i8
    RuntimeFuncSpec::new("rt_coverage_dump_sdn", &[], &[I64]),
    // rt_coverage_free_sdn(ptr: *mut i8) -> ()
    RuntimeFuncSpec::new("rt_coverage_free_sdn", &[I64], &[]),
    // rt_coverage_clear() -> ()
    RuntimeFuncSpec::new("rt_coverage_clear", &[], &[]),
    // rt_coverage_enable() -> ()
    RuntimeFuncSpec::new("rt_coverage_enable", &[], &[]),
    // rt_coverage_enabled() -> bool
    RuntimeFuncSpec::new("rt_coverage_enabled", &[], &[I8]),
    // rt_coverage_enable_timed() -> ()
    RuntimeFuncSpec::new("rt_coverage_enable_timed", &[], &[]),
    // =========================================================================
    // Performance measurement operations
    // =========================================================================
    // rt_perf_clock_ns() -> i64
    RuntimeFuncSpec::new("rt_perf_clock_ns", &[], &[I64]),
    // rt_perf_rdtsc() -> i64
    RuntimeFuncSpec::new("rt_perf_rdtsc", &[], &[I64]),
    // rt_perf_cycles_to_ns(cycles: i64, freq_mhz: i64) -> i64
    RuntimeFuncSpec::new("rt_perf_cycles_to_ns", &[I64, I64], &[I64]),
    // rt_perf_enable() -> ()
    RuntimeFuncSpec::new("rt_perf_enable", &[], &[]),
    // rt_perf_enabled() -> bool
    RuntimeFuncSpec::new("rt_perf_enabled", &[], &[I8]),
    // rt_perf_region_enter(region_id: u32, file: *const i8, line: u32) -> ()
    RuntimeFuncSpec::new("rt_perf_region_enter", &[I32, I64, I32], &[]),
    // rt_perf_region_exit(region_id: u32, file: *const i8, line: u32) -> ()
    RuntimeFuncSpec::new("rt_perf_region_exit", &[I32, I64, I32], &[]),
    // rt_perf_dump_sdn() -> *mut i8
    RuntimeFuncSpec::new("rt_perf_dump_sdn", &[], &[I64]),
    // rt_perf_free_sdn(ptr: *mut i8) -> ()
    RuntimeFuncSpec::new("rt_perf_free_sdn", &[I64], &[]),
    // rt_perf_clear() -> ()
    RuntimeFuncSpec::new("rt_perf_clear", &[], &[]),
    // =========================================================================
    // SFFI Object System (object-based SFFI for extern class)
    // =========================================================================
    // Type registration: rt_sffi_type_register(name_ptr, name_len, vtable_ptr) -> type_id
    RuntimeFuncSpec::new("rt_sffi_type_register", &[I64, I64, I64], &[I64]),
    // Object creation: rt_sffi_new(type_id) -> RuntimeValue (FfiObject)
    RuntimeFuncSpec::new("rt_sffi_new", &[I64], &[I64]),
    // Object destruction: rt_sffi_drop(obj) -> bool (success)
    RuntimeFuncSpec::new("rt_sffi_drop", &[I64], &[I8]),
    // Type introspection: rt_sffi_type_id(obj) -> type_id
    RuntimeFuncSpec::new("rt_sffi_type_id", &[I64], &[I64]),
    // Type name: rt_sffi_type_name(obj) -> RuntimeValue (string)
    RuntimeFuncSpec::new("rt_sffi_type_name", &[I64], &[I64]),
    // Method call: rt_sffi_call_method(obj, name_ptr, name_len, argc, argv_ptr) -> RuntimeValue
    RuntimeFuncSpec::new("rt_sffi_call_method", &[I64, I64, I64, I64, I64], &[I64]),
    // Method check: rt_sffi_has_method(obj, name_ptr, name_len) -> bool
    RuntimeFuncSpec::new("rt_sffi_has_method", &[I64, I64, I64], &[I8]),
    // Object clone: rt_sffi_clone(obj) -> RuntimeValue (cloned FfiObject)
    RuntimeFuncSpec::new("rt_sffi_clone", &[I64], &[I64]),
    // Object-based SFFI - new object creation
    // rt_sffi_object_new(type_id, handle, vtable_ptr) -> RuntimeValue
    RuntimeFuncSpec::new("rt_sffi_object_new", &[I64, I64, I64], &[I64]),
    // rt_sffi_object_free(obj) -> bool
    RuntimeFuncSpec::new("rt_sffi_object_free", &[I64], &[I8]),
    // rt_sffi_object_call_method(obj, method_name_ptr, method_name_len, argc, argv) -> RuntimeValue
    RuntimeFuncSpec::new("rt_sffi_object_call_method", &[I64, I64, I64, I64, I64], &[I64]),
    // rt_sffi_object_has_method(obj, method_name_ptr, method_name_len) -> bool
    RuntimeFuncSpec::new("rt_sffi_object_has_method", &[I64, I64, I64], &[I8]),
    // rt_sffi_object_type_id(obj) -> type_id
    RuntimeFuncSpec::new("rt_sffi_object_type_id", &[I64], &[I64]),
    // rt_sffi_object_type_name(obj) -> RuntimeValue (string)
    RuntimeFuncSpec::new("rt_sffi_object_type_name", &[I64], &[I64]),
    // =========================================================================
    // Process execution
    // =========================================================================
    // Native libsimple_runtime.a process functions take (cmd_ptr, cmd_len, args: SplArray ptr).
    // These three real signatures are (cmd_ptr: *const u8, cmd_len: u64, args: RuntimeValue) —
    // the arity here MUST be 3, matching rt_process_spawn_async below, or the cranelift call
    // site drops cmd_len and shifts args into the wrong register (see bug: exit_group(-8)
    // crash on `simple -c` when the driver self-exec-guard shells out via rt_process_run).
    RuntimeFuncSpec::new("rt_process_run", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_process_spawn", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_process_execute", &[I64, I64, I64], &[I32]),
    RuntimeFuncSpec::new("rt_process_run_timeout", &[I64, I64, I64, I64], &[I64]),
    // rt_process_is_running(pid) -> bool (as i64: 0/1)
    RuntimeFuncSpec::new("rt_process_is_running", &[I64], &[I64]),
    // rt_process_wait(pid, timeout_ms) -> exit_code
    RuntimeFuncSpec::new("rt_process_wait", &[I64, I64], &[I64]),
    // rt_process_kill(pid) -> bool (as i64: 0/1)
    RuntimeFuncSpec::new("rt_process_kill", &[I64], &[I64]),
    // rt_process_spawn_async(cmd_ptr, cmd_len, args) -> pid (i64)
    RuntimeFuncSpec::new("rt_process_spawn_async", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_process_spawn_inherit", &[], &[I64]),
    // rt_process_run_with_limits(cmd_ptr, cmd_len, args, timeout_ms, memory_mb) -> RuntimeValue
    RuntimeFuncSpec::new("rt_process_run_with_limits", &[I64, I64, I64, I64, I64], &[I64]),
    // rt_process_exists(pid) -> bool (as i64: 0/1)
    RuntimeFuncSpec::new("rt_process_exists", &[I64], &[I64]),
    // rt_getpid() -> process id
    RuntimeFuncSpec::new("rt_getpid", &[], &[I64]),
    // =========================================================================
    // CLI SFFI functions (for Simple-based CLI)
    // =========================================================================
    // Version and help
    RuntimeFuncSpec::new("rt_cli_version", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cli_print_help", &[], &[]),
    RuntimeFuncSpec::new("rt_cli_print_version", &[], &[]),
    RuntimeFuncSpec::new("rt_cli_arg_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cli_arg_at", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_get_args", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cli_file_exists", &[I64], &[I8]),
    RuntimeFuncSpec::new("rt_cli_read_file", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_exit", &[I64], &[]),
    // Code execution
    RuntimeFuncSpec::new("rt_cli_run_code", &[I64, I8, I8], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_file", &[I64, I64, I8, I8], &[I64]),
    RuntimeFuncSpec::new("rt_cli_watch_file", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_repl", &[I8, I8], &[I64]),
    // Testing
    RuntimeFuncSpec::new("rt_cli_run_tests", &[I64, I8, I8], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_tests_process_args", &[I8, I8], &[I64]),
    RuntimeFuncSpec::new("rt_test_db_validate", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_test_db_enable_validation", &[I8], &[]),
    RuntimeFuncSpec::new("rt_test_run_is_stale", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_test_db_cleanup_stale_runs", &[I64], &[I64]),
    // Code quality
    RuntimeFuncSpec::new("rt_cli_run_lint", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_fmt", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_check", &[I64], &[I64]),
    // Verification
    RuntimeFuncSpec::new("rt_cli_run_verify", &[I64, I8, I8], &[I64]),
    // Migration and tooling
    RuntimeFuncSpec::new("rt_cli_run_migrate", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_mcp", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_diff", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_context", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_constr", &[I64], &[I64]),
    // Analysis
    RuntimeFuncSpec::new("rt_cli_run_query", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_info", &[I64], &[I64]),
    // Auditing
    RuntimeFuncSpec::new("rt_cli_run_spec_coverage", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_replay", &[I64], &[I64]),
    // Code generation
    RuntimeFuncSpec::new("rt_cli_run_gen_lean", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_feature_gen", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_task_gen", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_spec_gen", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_spipe_docgen", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_todo_scan", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_todo_gen", &[I64], &[I64]),
    // i18n
    RuntimeFuncSpec::new("rt_cli_run_i18n", &[I64], &[I64]),
    // Lexer and brief
    RuntimeFuncSpec::new("rt_cli_run_lex", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_run_brief", &[I64], &[I64]),
    // SFFI generation
    RuntimeFuncSpec::new("rt_cli_run_sffi_gen", &[I64], &[I64]),
    // Context pack generation
    RuntimeFuncSpec::new("rt_context_generate", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_context_stats", &[I64, I64], &[I64]),
    // Settlement stub
    RuntimeFuncSpec::new("rt_settlement_main", &[], &[I64]),
    // Compilation
    RuntimeFuncSpec::new("rt_native_build", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_compile", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_targets", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_linkers", &[], &[I64]),
    // Web framework
    RuntimeFuncSpec::new("rt_cli_handle_web", &[I64], &[I64]),
    // Diagram generation
    RuntimeFuncSpec::new("rt_cli_handle_diagram", &[I64], &[I64]),
    // Package management
    RuntimeFuncSpec::new("rt_cli_handle_init", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_add", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_remove", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_install", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_update", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_list", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_tree", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cli_handle_cache", &[I64], &[I64]),
    // Environment management
    RuntimeFuncSpec::new("rt_cli_handle_env", &[I64], &[I64]),
    // Lock file management
    RuntimeFuncSpec::new("rt_cli_handle_lock", &[I64], &[I64]),
    // Explicit run command
    RuntimeFuncSpec::new("rt_cli_handle_run", &[I64, I8, I8], &[I64]),
    RuntimeFuncSpec::new("rt_compile_to_native", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_compile_to_native_with_opt", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_compile_to_llvm_ir", &[I64], &[I64]),
    // Fault detection configuration
    RuntimeFuncSpec::new("rt_fault_set_stack_overflow_detection", &[I8], &[]),
    RuntimeFuncSpec::new("rt_fault_set_max_recursion_depth", &[I64], &[]),
    RuntimeFuncSpec::new("rt_fault_set_timeout", &[I64], &[]),
    RuntimeFuncSpec::new("rt_fault_set_execution_limit", &[I64], &[]),
    // Print utilities
    RuntimeFuncSpec::new("rt_cli_print", &[I64], &[]),
    RuntimeFuncSpec::new("rt_cli_println", &[I64], &[]),
    RuntimeFuncSpec::new("rt_cli_eprint", &[I64], &[]),
    RuntimeFuncSpec::new("rt_cli_eprintln", &[I64], &[]),
    // SDN operations
    RuntimeFuncSpec::new("rt_sdn_version", &[], &[I64]),
    RuntimeFuncSpec::new("rt_sdn_check", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_sdn_to_json", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_sdn_from_json", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_sdn_get", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_sdn_set", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_sdn_fmt", &[I64], &[I64]),
    // =========================================================================
    // Cranelift SFFI (Self-Hosting Compiler Support)
    // =========================================================================
    // Module management
    RuntimeFuncSpec::new("rt_cranelift_module_new", &[I64, I64], &[I64]), // name (RuntimeValue), target -> module_handle
    RuntimeFuncSpec::new("rt_cranelift_new_module", &[I64, I64, I64], &[I64]), // name_ptr, name_len, target -> module_handle (JIT)
    RuntimeFuncSpec::new("rt_cranelift_new_aot_module", &[I64, I64, I64], &[I64]), // name_ptr, name_len, target -> module_handle (AOT)
    RuntimeFuncSpec::new("rt_cranelift_finalize_module", &[I64], &[I64]),          // module -> success
    RuntimeFuncSpec::new("rt_cranelift_free_module", &[I64], &[]),                 // module -> ()
    // Signature building
    RuntimeFuncSpec::new("rt_cranelift_new_signature", &[I64], &[I64]), // call_conv -> sig_handle
    RuntimeFuncSpec::new("rt_cranelift_sig_add_param", &[I64, I64], &[]), // sig, type -> ()
    RuntimeFuncSpec::new("rt_cranelift_sig_set_return", &[I64, I64], &[]), // sig, type -> ()
    // Function building
    RuntimeFuncSpec::new("rt_cranelift_begin_function", &[I64, I64, I64, I64], &[I64]), // module, name_ptr, name_len, sig -> ctx
    RuntimeFuncSpec::new("rt_cranelift_end_function", &[I64], &[I64]),                  // ctx -> func_id
    RuntimeFuncSpec::new("rt_cranelift_define_function", &[I64, I64, I64], &[I8]), // module, func_id, ctx -> success (JIT)
    RuntimeFuncSpec::new("rt_cranelift_aot_define_function", &[I64, I64, I64, I64], &[I8]), // module, name_ptr, name_len, ctx -> success (AOT)
    // Block management
    RuntimeFuncSpec::new("rt_cranelift_create_block", &[I64], &[I64]), // ctx -> block
    RuntimeFuncSpec::new("rt_cranelift_switch_to_block", &[I64, I64], &[]), // ctx, block -> ()
    RuntimeFuncSpec::new("rt_cranelift_seal_block", &[I64, I64], &[]), // ctx, block -> ()
    RuntimeFuncSpec::new("rt_cranelift_seal_all_blocks", &[I64], &[]), // ctx -> ()
    // Value creation
    RuntimeFuncSpec::new("rt_cranelift_iconst", &[I64, I64, I64], &[I64]), // ctx, type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_fconst", &[I64, I64, F64], &[I64]), // ctx, type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_bconst", &[I64, I8], &[I64]),       // ctx, value -> val
    RuntimeFuncSpec::new("rt_cranelift_null", &[I64, I64], &[I64]),        // ctx, type -> val
    // Arithmetic
    RuntimeFuncSpec::new("rt_cranelift_iadd", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_isub", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_imul", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_sdiv", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_udiv", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_srem", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_urem", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_fadd", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_fsub", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_fmul", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_fdiv", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    // Bitwise
    RuntimeFuncSpec::new("rt_cranelift_band", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_bor", &[I64, I64, I64], &[I64]),  // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_bxor", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_bnot", &[I64, I64], &[I64]),      // ctx, a -> val
    RuntimeFuncSpec::new("rt_cranelift_ishl", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_sshr", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_ushr", &[I64, I64, I64], &[I64]), // ctx, a, b -> val
    // Comparison
    RuntimeFuncSpec::new("rt_cranelift_icmp", &[I64, I64, I64, I64], &[I64]), // ctx, cond, a, b -> val
    RuntimeFuncSpec::new("rt_cranelift_fcmp", &[I64, I64, I64, I64], &[I64]), // ctx, cond, a, b -> val
    // Memory
    RuntimeFuncSpec::new("rt_cranelift_load", &[I64, I64, I64, I64], &[I64]), // ctx, type, addr, offset -> val
    RuntimeFuncSpec::new("rt_cranelift_store", &[I64, I64, I64, I64], &[]),   // ctx, value, addr, offset -> ()
    RuntimeFuncSpec::new("rt_cranelift_stack_slot", &[I64, I64, I64], &[I64]), // ctx, size, align -> slot
    RuntimeFuncSpec::new("rt_cranelift_stack_addr", &[I64, I64, I64], &[I64]), // ctx, slot, offset -> addr
    // Control flow
    RuntimeFuncSpec::new("rt_cranelift_jump", &[I64, I64], &[]), // ctx, block -> ()
    RuntimeFuncSpec::new("rt_cranelift_brif", &[I64, I64, I64, I64], &[]), // ctx, cond, then_block, else_block -> ()
    RuntimeFuncSpec::new("rt_cranelift_return", &[I64, I64], &[]), // ctx, value -> ()
    RuntimeFuncSpec::new("rt_cranelift_return_void", &[I64], &[]), // ctx -> ()
    RuntimeFuncSpec::new("rt_cranelift_trap", &[I64, I64], &[]), // ctx, code -> ()
    // Function calls
    RuntimeFuncSpec::new("rt_cranelift_call_args_clear", &[I64], &[]),
    RuntimeFuncSpec::new("rt_cranelift_call_arg", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_cranelift_call", &[I64, I64, I64, I64], &[I64]), // ctx, func, args_ptr, args_len -> val
    RuntimeFuncSpec::new("rt_cranelift_call_indirect", &[I64, I64, I64, I64, I64], &[I64]), // ctx, sig, addr, args_ptr, args_len -> val
    RuntimeFuncSpec::new("rt_cranelift_declare_string_data", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_cranelift_declare_global_data", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_cranelift_data_addr_in_func", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_cranelift_function_addr_in_func", &[I64, I64, I64], &[I64]),
    // Type conversion
    RuntimeFuncSpec::new("rt_cranelift_sextend", &[I64, I64, I64], &[I64]), // ctx, to_type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_uextend", &[I64, I64, I64], &[I64]), // ctx, to_type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_ireduce", &[I64, I64, I64], &[I64]), // ctx, to_type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_fcvt_to_sint", &[I64, I64, I64], &[I64]), // ctx, to_type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_fcvt_to_uint", &[I64, I64, I64], &[I64]), // ctx, to_type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_fcvt_from_sint", &[I64, I64, I64], &[I64]), // ctx, to_type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_fcvt_from_uint", &[I64, I64, I64], &[I64]), // ctx, to_type, value -> val
    RuntimeFuncSpec::new("rt_cranelift_fpromote", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_cranelift_fdemote", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_cranelift_bitcast", &[I64, I64, I64], &[I64]), // ctx, to_type, value -> val
    // Block parameters
    RuntimeFuncSpec::new("rt_cranelift_append_block_param", &[I64, I64, I64], &[I64]), // ctx, block, type -> val
    RuntimeFuncSpec::new("rt_cranelift_block_param", &[I64, I64, I64], &[I64]),        // ctx, block, index -> val
    // JIT execution
    RuntimeFuncSpec::new("rt_cranelift_get_function_ptr", &[I64, I64, I64], &[I64]), // module, name_ptr, name_len -> ptr
    RuntimeFuncSpec::new("rt_cranelift_call_function_ptr", &[I64, I64, I64], &[I64]), // ptr, args_ptr, args_len -> result
    // Object file generation
    RuntimeFuncSpec::new("rt_cranelift_emit_object", &[I64, I64], &[I8]), // module, path (RuntimeValue) -> success
    RuntimeFuncSpec::new("rt_cranelift_emit_object_raw", &[I64, I64, I64], &[I8]),
    // =========================================================================
    // CUDA Runtime
    // =========================================================================
    RuntimeFuncSpec::new("rt_cuda_init", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_available", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_device_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_device_get", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_device_identity", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_device_name", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_device_compute_capability", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_is_available", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_device_count", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_device_driver_identity", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_device_name", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_selected_device_name", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_device_type", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_selected_device_driver_identity", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_selected_device_type", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_fence_submission_supported", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_submit_and_wait_fence", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_submit_graphics_and_wait_fence", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_wait_fence", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_destroy_fence", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_init", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_shutdown", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_select_device", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_get_device", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_alloc_buffer", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_free_buffer", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_copy_to_buffer", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_copy_from_buffer", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_compile_spirv", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_destroy_shader", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_begin_compute", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_begin_graphics", &[], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_end_compute", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_end_graphics", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_discard_command", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_discard_graphics_command", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_create_render_pass", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_create_offscreen_render_pass", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_destroy_render_pass", &[I64], &[I64]),
    RuntimeFuncSpec::new(
        "rt_vulkan_create_graphics_pipeline",
        &[I64, I64, I64, I64, I64, I64, I64, I64, I64, I64],
        &[I64],
    ),
    RuntimeFuncSpec::new("rt_vulkan_create_font_graphics_pipeline", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new(
        "rt_vulkan_create_font_world_graphics_pipeline",
        &[I64, I64, I64, I64],
        &[I64],
    ),
    RuntimeFuncSpec::new("rt_vulkan_destroy_graphics_pipeline", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_create_image", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_destroy_image", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_copy_to_image", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_copy_from_image", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_create_sampler", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_create_font_sampler", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_destroy_sampler", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_create_framebuffer", &[I64, I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_destroy_framebuffer", &[I64], &[I64]),
    RuntimeFuncSpec::new(
        "rt_vulkan_begin_render_pass_gfx",
        &[I64, I64, I64, F64, F64, F64, F64],
        &[I64],
    ),
    RuntimeFuncSpec::new("rt_vulkan_end_render_pass_gfx", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_bind_graphics_pipeline", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_bind_vertex_buffer", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_bind_index_buffer", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_bind_texture", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_bind_font_texture", &[I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_set_viewport", &[I64, F64, F64, F64, F64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_set_scissor", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_draw", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_vulkan_draw_indexed", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_ctx_create", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_ctx_destroy", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_mem_alloc", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_mem_free", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_memset", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_memcpy_dtoh", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_cuda_module_load_data", &[I64], &[I64]), // ptx_ptr (cstr) -> module
    RuntimeFuncSpec::new("rt_cuda_module_load_data_bytes", &[I64, I64], &[I64]), // ptx_ptr, ptx_len -> module
    RuntimeFuncSpec::new("rt_cuda_module_unload", &[I64], &[I64]),
    RuntimeFuncSpec::new(
        "rt_cuda_launch_kernel",
        &[I64, I64, I64, I64, I64, I64, I64, I64, I64],
        &[I64],
    ), // module, name_ptr, grid_xyz, block_xyz, args_ptr
    RuntimeFuncSpec::new(
        "rt_cuda_launch_kernel_name",
        &[I64, I64, I64, I64, I64, I64, I64, I64, I64, I64],
        &[I64],
    ), // module, name_ptr, name_len, grid_xyz, block_xyz, args_ptr
    RuntimeFuncSpec::new("rt_cuda_sync", &[], &[I64]),
    // =========================================================================
    // Bootstrap Self-Hosting SFFI
    // =========================================================================
    RuntimeFuncSpec::new("rt_exec", &[I64], &[I32]), // cmd -> exit_code
    RuntimeFuncSpec::new("rt_file_hash", &[I64], &[I64]), // path -> hash_text
    RuntimeFuncSpec::new("rt_write_file", &[I64, I64], &[I8]), // path, content -> success
    // =========================================================================
    // Environment Variable Operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_env_get", &[I64, I64], &[I64]), // name_ptr, name_len -> RuntimeValue
    RuntimeFuncSpec::new("rt_env_get_i64", &[I64, I64, I64], &[I64]), // name_ptr, name_len, default -> i64
    RuntimeFuncSpec::new("rt_lexer_source_set", &[I64, I64], &[I8]), // source_ptr, source_len -> bool
    RuntimeFuncSpec::new("rt_lexer_source_slice", &[I64, I64], &[I64]), // start, end -> RuntimeValue
    RuntimeFuncSpec::new("rt_get_env", &[I64, I64], &[I64]), // alias for rt_env_get
    RuntimeFuncSpec::new("rt_env_set", &[I64, I64, I64, I64], &[I8]), // name_ptr, name_len, val_ptr, val_len -> bool
    RuntimeFuncSpec::new("rt_set_env", &[I64, I64, I64, I64], &[]), // alias, no return
    RuntimeFuncSpec::new("rt_env_cwd", &[], &[I64]),         // () -> RuntimeValue
    RuntimeFuncSpec::new("rt_env_all", &[], &[I64]),         // () -> RuntimeValue (array of tuples)
    RuntimeFuncSpec::new("rt_env_vars", &[], &[I64]),        // alias for rt_env_all
    RuntimeFuncSpec::new("rt_env_exists", &[I64, I64], &[I8]), // name_ptr, name_len -> bool
    RuntimeFuncSpec::new("rt_env_remove", &[I64, I64], &[I8]), // name_ptr, name_len -> bool
    RuntimeFuncSpec::new("rt_env_home", &[], &[I64]),        // () -> RuntimeValue
    RuntimeFuncSpec::new("rt_env_temp", &[], &[I64]),        // () -> RuntimeValue
    RuntimeFuncSpec::new("rt_exit", &[I64], &[]),            // code -> ! (never returns)
    RuntimeFuncSpec::new("rt_time_now_unix", &[], &[I64]),
    RuntimeFuncSpec::new("rt_time_now_nanos", &[], &[I64]),
    RuntimeFuncSpec::new("rt_time_now_micros", &[], &[I64]),
    RuntimeFuncSpec::new("rt_time_now_monotonic_ms", &[], &[I64]),
    RuntimeFuncSpec::new("rt_time_now_unix_micros", &[], &[I64]),
    RuntimeFuncSpec::new("rt_entropy_hardware_ready", &[], &[I64]),
    RuntimeFuncSpec::new("rt_sleep_ms", &[I64], &[]),
    RuntimeFuncSpec::new("rt_panic", &[I64], &[]),
    RuntimeFuncSpec::new("rt_get_args", &[], &[I64]), // () -> RuntimeValue (array of args)
    RuntimeFuncSpec::new("rt_platform_name", &[], &[I64]), // () -> RuntimeValue
    RuntimeFuncSpec::new("rt_term_enable_ansi", &[], &[I64]), // () -> RuntimeValue (bool)
    RuntimeFuncSpec::new("rt_term_get_size", &[], &[I64]), // () -> RuntimeValue (tuple of i32, i32)
    RuntimeFuncSpec::new("rt_terminal_get_size", &[], &[I64]), // () -> RuntimeValue (tuple of i64, i64)
    RuntimeFuncSpec::new("rt_terminal_enable_raw_mode", &[], &[I64]), // () -> RuntimeValue (bool)
    RuntimeFuncSpec::new("rt_terminal_disable_raw_mode", &[], &[I64]), // () -> RuntimeValue (bool)
    RuntimeFuncSpec::new("rt_stdin_read_byte", &[], &[I64]), // () -> byte or -1
    RuntimeFuncSpec::new("stdin_read_char", &[], &[I64]), // legacy source-level char read -> RuntimeValue(text)
    RuntimeFuncSpec::new("rt_ssh_userauth_password_only_failure_payload", &[], &[I64]),
    // =========================================================================
    // File I/O Metadata Operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_file_exists", &[I64, I64], &[I8]), // path_ptr, path_len -> bool
    RuntimeFuncSpec::new("rt_dir_exists", &[I64, I64], &[I8]),  // path_ptr, path_len -> bool
    RuntimeFuncSpec::new("rt_file_stat", &[I64, I64], &[I64]),  // path_ptr, path_len -> i64 (mtime seconds)
    // =========================================================================
    // File I/O Operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_file_canonicalize", &[I64, I64], &[I64]), // path_ptr, path_len -> RuntimeValue
    RuntimeFuncSpec::new("rt_file_read_text", &[I64, I64], &[I64]),    // path_ptr, path_len -> RuntimeValue
    RuntimeFuncSpec::new("rt_file_read_text_rv", &[I64], &[I64]),      // RuntimeValue(string) -> RuntimeValue
    RuntimeFuncSpec::new("rt_file_mmap_read_text", &[I64, I64], &[I64]), // path_ptr, path_len -> RuntimeValue
    RuntimeFuncSpec::new("rt_file_mmap_len", &[I64, I64], &[I64]),     // path_ptr, path_len -> byte length
    RuntimeFuncSpec::new("rt_file_mmap_read_text_rv", &[I64], &[I64]), // RuntimeValue(string) -> RuntimeValue
    RuntimeFuncSpec::new("rt_file_mmap_read_bytes", &[I64, I64], &[I64]), // path_ptr, path_len -> RuntimeValue
    RuntimeFuncSpec::new("rt_file_mmap_read_bytes_rv", &[I64], &[I64]), // RuntimeValue(string) -> RuntimeValue
    RuntimeFuncSpec::new("rt_file_write_text", &[I64, I64, I64, I64], &[I8]), // path_ptr, path_len, content_ptr, content_len -> bool
    RuntimeFuncSpec::new("rt_file_fsync", &[I64, I64], &[I8]),                // path -> bool
    RuntimeFuncSpec::new("rt_file_fsync_cached", &[I64, I64], &[I8]),         // path -> bool, prefer write-at cache
    RuntimeFuncSpec::new("rt_crc32_text", &[I64, I64], &[I64]),               // text -> i64 (CRC32 checksum)
    RuntimeFuncSpec::new("rt_file_sync", &[I64, I64], &[I8]),                 // path -> bool (alias for fsync)
    RuntimeFuncSpec::new("rt_file_create_excl", &[I64, I64, I64, I64], &[I8]), // path, content -> bool (O_EXCL)
    RuntimeFuncSpec::new("rt_file_write_text_at", &[I64, I64, I64], &[I64]), // path RuntimeValue, offset, data RuntimeValue -> bytes written
    RuntimeFuncSpec::new("rt_file_write_text_at_cached", &[I64, I64], &[I64]), // offset, data RuntimeValue -> bytes written on prepared cache
    RuntimeFuncSpec::new("rt_file_write_text_at_cached_repeat", &[I64, I64], &[I64]), // iterations, data RuntimeValue -> bytes written on prepared cache
    RuntimeFuncSpec::new("rt_file_copy", &[I64, I64, I64, I64], &[I8]),               // src, dest -> bool
    RuntimeFuncSpec::new("rt_file_remove", &[I64, I64], &[I8]),                       // path -> bool
    RuntimeFuncSpec::new("rt_file_size", &[I64, I64], &[I64]),                        // path -> i64
    RuntimeFuncSpec::new("rt_file_hash_sha256", &[I64, I64], &[I64]),                 // path -> RuntimeValue
    RuntimeFuncSpec::new("rt_file_rename", &[I64, I64, I64, I64], &[I8]),             // old, new -> bool
    RuntimeFuncSpec::new("rt_file_read_lines", &[I64, I64], &[I64]),                  // path -> RuntimeValue (array)
    RuntimeFuncSpec::new("rt_file_append_text", &[I64, I64, I64, I64], &[I8]), // path_ptr, path_len, content_ptr, content_len -> bool
    RuntimeFuncSpec::new("rt_file_read_bytes", &[I64, I64], &[I64]),           // path -> RuntimeValue (array)
    RuntimeFuncSpec::new("rt_bytes_from_raw", &[I64, I64], &[I64]),            // ptr, len -> RuntimeValue (byte array)
    RuntimeFuncSpec::new("rt_u32s_from_raw", &[I64, I64], &[I64]),             // ptr, count -> RuntimeValue (u32 array)
    RuntimeFuncSpec::new("rt_file_write_bytes", &[I64, I64, I64, I64], &[I8]), // path, bytes -> bool
    RuntimeFuncSpec::new("rt_file_wrap_smf_dynlib", &[I64, I64, I64, I64, I64], &[I8]), // input, output, arch -> bool
    RuntimeFuncSpec::new("rt_file_extract_smf_dynlib", &[I64, I64, I64, I64], &[I8]), // input, output -> bool
    RuntimeFuncSpec::new("rt_file_move", &[I64, I64, I64, I64], &[I8]),        // src, dest -> bool
    // =========================================================================
    // Directory Operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_dir_create", &[I64, I64, I8], &[I8]), // path_ptr, path_len, recursive -> bool
    RuntimeFuncSpec::new("rt_dir_create_all", &[I64, I64], &[I8]), // path_ptr, path_len -> bool
    RuntimeFuncSpec::new("rt_dir_exists", &[I64, I64], &[I8]),     // path_ptr, path_len -> bool
    RuntimeFuncSpec::new("rt_dir_list", &[I64, I64], &[I64]),      // path -> RuntimeValue (array)
    RuntimeFuncSpec::new("rt_dir_remove", &[I64, I64, I8], &[I8]), // path_ptr, path_len, recursive -> bool
    RuntimeFuncSpec::new("rt_dir_remove_all", &[I64, I64], &[I8]), // path -> bool
    RuntimeFuncSpec::new("rt_file_find", &[I64, I64, I64, I64], &[I64]), // dir, pattern -> RuntimeValue
    RuntimeFuncSpec::new("rt_dir_glob", &[I64, I64], &[I64]),      // pattern -> RuntimeValue (array)
    RuntimeFuncSpec::new("rt_dir_walk", &[I64, I64], &[I64]),      // path -> RuntimeValue (array)
    RuntimeFuncSpec::new("rt_current_dir", &[], &[I64]),           // () -> RuntimeValue
    RuntimeFuncSpec::new("rt_set_current_dir", &[I64, I64], &[I8]), // path -> bool
    // =========================================================================
    // File Descriptor Operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_file_open", &[I64, I64, I64, I64], &[I32]), // path, mode -> fd
    RuntimeFuncSpec::new("rt_file_get_size", &[I32], &[I64]),            // fd -> size
    RuntimeFuncSpec::new("rt_file_close", &[I32], &[I8]),                // fd -> bool
    // =========================================================================
    // Path Operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_path_basename", &[I64, I64], &[I64]), // path -> RuntimeValue
    RuntimeFuncSpec::new("rt_path_dirname", &[I64, I64], &[I64]),  // path -> RuntimeValue
    RuntimeFuncSpec::new("rt_path_ext", &[I64, I64], &[I64]),      // path -> RuntimeValue
    RuntimeFuncSpec::new("rt_path_absolute", &[I64, I64], &[I64]), // path -> RuntimeValue
    RuntimeFuncSpec::new("rt_path_separator", &[], &[I64]),        // () -> RuntimeValue
    RuntimeFuncSpec::new("rt_path_stem", &[I64, I64], &[I64]),     // path -> RuntimeValue
    RuntimeFuncSpec::new("rt_path_relative", &[I64, I64, I64, I64], &[I64]), // from, to -> RuntimeValue
    RuntimeFuncSpec::new("rt_path_join", &[I64, I64, I64, I64], &[I64]), // path1, path2 -> RuntimeValue
    RuntimeFuncSpec::new("rt_path_parent", &[I64, I64], &[I64]),   // path -> RuntimeValue
    // =========================================================================
    // Runtime Configuration
    // =========================================================================
    RuntimeFuncSpec::new("rt_set_macro_trace", &[I8], &[]), // enable -> ()
    RuntimeFuncSpec::new("rt_is_macro_trace_enabled", &[], &[I8]), // () -> bool
    RuntimeFuncSpec::new("rt_set_debug_mode", &[I8], &[]),  // enable -> ()
    RuntimeFuncSpec::new("rt_is_debug_mode_enabled", &[], &[I8]), // () -> bool
    // =========================================================================
    // Regex Operations
    // =========================================================================
    RuntimeFuncSpec::new("sffi_regex_is_match", &[I64, I64, I64, I64], &[I8]), // pattern, text -> bool
    RuntimeFuncSpec::new("sffi_regex_find", &[I64, I64, I64, I64], &[I64]),    // pattern, text -> RuntimeValue
    RuntimeFuncSpec::new("sffi_regex_find_all", &[I64, I64, I64, I64], &[I64]), // pattern, text -> RuntimeValue
    RuntimeFuncSpec::new("sffi_regex_captures", &[I64, I64, I64, I64], &[I64]), // pattern, text -> RuntimeValue
    RuntimeFuncSpec::new("sffi_regex_replace", &[I64, I64, I64, I64, I64, I64], &[I64]), // pattern, text, replacement -> RuntimeValue
    RuntimeFuncSpec::new("sffi_regex_replace_all", &[I64, I64, I64, I64, I64, I64], &[I64]), // pattern, text, replacement -> RuntimeValue
    RuntimeFuncSpec::new("sffi_regex_split", &[I64, I64, I64, I64], &[I64]), // pattern, text -> RuntimeValue
    RuntimeFuncSpec::new("sffi_regex_split_n", &[I64, I64, I64, I64, I64], &[I64]), // pattern, text, n -> RuntimeValue
    // =========================================================================
    // BDD test framework SFFI (for native/SMF test execution modes)
    // =========================================================================
    RuntimeFuncSpec::new("rt_bdd_describe_start", &[I64, I64], &[]), // name_ptr, name_len
    RuntimeFuncSpec::new("rt_bdd_describe_end", &[], &[]),
    RuntimeFuncSpec::new("rt_bdd_it_start", &[I64, I64], &[]), // name_ptr, name_len
    RuntimeFuncSpec::new("rt_bdd_it_end", &[I64], &[]),        // passed
    RuntimeFuncSpec::new("rt_bdd_has_failure", &[], &[I64]),
    RuntimeFuncSpec::new("rt_bdd_expect_fail", &[I64, I64], &[]), // msg_ptr, msg_len
    RuntimeFuncSpec::new("rt_bdd_expect_eq", &[I64, I64], &[]),   // actual, expected
    RuntimeFuncSpec::new("rt_bdd_expect_truthy", &[I64], &[]),    // value
    RuntimeFuncSpec::new("rt_bdd_before_each", &[I64], &[]),      // block (fn ptr)
    RuntimeFuncSpec::new("rt_bdd_after_each", &[I64], &[]),       // block (fn ptr)
    RuntimeFuncSpec::new("rt_bdd_format_results", &[], &[I64]),   // -> failures count
    RuntimeFuncSpec::new("rt_bdd_clear_state", &[], &[]),
    // RuntimeValue-based BDD wrappers (for Cranelift codegen)
    RuntimeFuncSpec::new("rt_bdd_describe_start_rv", &[I64], &[]), // name as RuntimeValue string
    RuntimeFuncSpec::new("rt_bdd_it_start_rv", &[I64], &[]),       // name as RuntimeValue string
    RuntimeFuncSpec::new("rt_bdd_expect_eq_rv", &[I64, I64], &[]), // actual, expected as RuntimeValues
    RuntimeFuncSpec::new("rt_bdd_expect_truthy_rv", &[I64], &[]),  // value as RuntimeValue
    // Runtime profiler SFFI
    RuntimeFuncSpec::new("rt_profiler_record_call", &[I64], &[]), // name_ptr (C string)
    RuntimeFuncSpec::new("rt_profiler_record_return", &[], &[]),
    RuntimeFuncSpec::new("rt_profiler_is_active", &[], &[I32]),
    // =========================================================================
    // Dynamic Loading (WFFI)
    // =========================================================================
    RuntimeFuncSpec::new("spl_dlopen", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_dlsym", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("spl_dlclose", &[I64], &[I64]),
    RuntimeFuncSpec::new("spl_wffi_call_i64", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("spl_wffi_call_f64", &[I64, I64, I64], &[F64]),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_funcs_have_unique_names() {
        let mut names: Vec<&str> = RUNTIME_FUNCS.iter().map(|f| f.name).collect();
        names.sort();
        let original_len = names.len();
        names.dedup();
        assert_eq!(names.len(), original_len, "Duplicate function names found");
    }

    #[test]
    fn build_signature_works() {
        let spec = RuntimeFuncSpec::new("test", &[I64, I64], &[I64]);
        let sig = spec.build_signature(crate::codegen::shared::platform_call_conv());
        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.returns.len(), 1);
    }

    #[test]
    fn all_funcs_have_a_tier() {
        // Every function should be classified into exactly one tier
        for spec in RUNTIME_FUNCS {
            let _tier = tier_of(spec.name);
            // Just ensure it doesn't panic
        }
    }

    #[test]
    fn rt_getpid_is_registered() {
        let spec = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_getpid")
            .expect("rt_getpid must be registered for native codegen");
        assert!(spec.params.is_empty());
        assert_eq!(spec.returns, [I64]);
        assert_eq!(tier_of(spec.name), RuntimeFuncTier::Sys);
    }

    #[test]
    fn async_current_task_id_is_registered() {
        let spec = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_async_current_task_id")
            .expect("rt_async_current_task_id must be registered for native codegen");
        assert!(spec.params.is_empty());
        assert_eq!(spec.returns, [I64]);
        assert_eq!(tier_of(spec.name), RuntimeFuncTier::Async);
    }

    #[test]
    fn executor_current_task_id_is_registered() {
        let spec = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_executor_current_task_id")
            .expect("rt_executor_current_task_id must be registered for native codegen");
        assert!(spec.params.is_empty());
        assert_eq!(spec.returns, [I64]);
        assert_eq!(tier_of(spec.name), RuntimeFuncTier::Async);
    }

    #[test]
    fn array_extend_i64_is_registered_for_merge_lowering() {
        let spec = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_array_extend_i64")
            .expect("rt_array_extend_i64 must be registered for Array.merge lowering");
        assert_eq!(spec.params, [I64, I64, I64]);
        assert_eq!(spec.returns, [I8]);
        assert_eq!(tier_of(spec.name), RuntimeFuncTier::Alloc);
    }

    #[test]
    fn fiber_task_identity_functions_are_registered() {
        let enter = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_fiber_enter_task_id")
            .expect("rt_fiber_enter_task_id must be registered for native codegen");
        assert_eq!(enter.params, [I64]);
        assert_eq!(enter.returns, [I64]);
        assert_eq!(tier_of(enter.name), RuntimeFuncTier::Async);

        let exit = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_fiber_exit_task_id")
            .expect("rt_fiber_exit_task_id must be registered for native codegen");
        assert_eq!(exit.params, [I64]);
        assert!(exit.returns.is_empty());
        assert_eq!(tier_of(exit.name), RuntimeFuncTier::Async);

        let current = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_fiber_current_task_id")
            .expect("rt_fiber_current_task_id must be registered for native codegen");
        assert!(current.params.is_empty());
        assert_eq!(current.returns, [I64]);
        assert_eq!(tier_of(current.name), RuntimeFuncTier::Async);
    }

    #[test]
    fn unified_current_task_id_is_registered() {
        let spec = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_current_task_id")
            .expect("rt_current_task_id must be registered for native codegen");
        assert!(spec.params.is_empty());
        assert_eq!(spec.returns, [I64]);
        assert_eq!(tier_of(spec.name), RuntimeFuncTier::Async);
    }

    #[test]
    fn tier_classification_samples() {
        use RuntimeFuncTier::*;
        // Core
        assert_eq!(tier_of("rt_value_int"), Core);
        assert_eq!(tier_of("rt_enum_new"), Core);
        assert_eq!(tier_of("rt_function_not_found"), Core);
        assert_eq!(tier_of("simple_contract_check"), Core);
        assert_eq!(tier_of("rt_profiler_record_call"), Core);
        // Alloc
        assert_eq!(tier_of("rt_array_new"), Alloc);
        assert_eq!(tier_of("rt_string_concat"), Alloc);
        assert_eq!(tier_of("rt_object_new"), Alloc);
        assert_eq!(tier_of("rt_closure_new"), Alloc);
        assert_eq!(tier_of("rt_hashmap_new"), Alloc);
        assert_eq!(tier_of("rt_alloc"), Alloc);
        // Sys
        assert_eq!(tier_of("rt_print_str"), Sys);
        assert_eq!(tier_of("rt_file_read_text"), Sys);
        assert_eq!(tier_of("rt_env_get"), Sys);
        assert_eq!(tier_of("rt_process_run"), Sys);
        assert_eq!(tier_of("sffi_regex_is_match"), Sys);
        assert_eq!(tier_of("rt_cli_version"), Sys);
        assert_eq!(tier_of("native_tcp_bind"), Sys);
        // Async
        assert_eq!(tier_of("rt_future_new"), Async);
        assert_eq!(tier_of("rt_actor_spawn"), Async);
        assert_eq!(tier_of("rt_channel_new"), Async);
        assert_eq!(tier_of("rt_executor_start"), Async);
        assert_eq!(tier_of("rt_thread_spawn_isolated"), Async);
        assert_eq!(tier_of("rt_generator_new"), Async);
        assert_eq!(tier_of("rt_wait"), Async);
        // Ext
        assert_eq!(tier_of("rt_vec_sum"), Ext);
        assert_eq!(tier_of("rt_gpu_barrier"), Ext);
        assert_eq!(tier_of("rt_vk_available"), Ext);
        assert_eq!(tier_of("rt_metal_is_available"), Ext);
        assert_eq!(tier_of("rt_cranelift_module_new"), Ext);
        assert_eq!(tier_of("rt_par_map"), Ext);
        assert_eq!(tier_of("rt_simd_aes_round_u8x16"), Ext);
    }

    #[test]
    fn cranelift_emit_object_raw_signature_is_registered() {
        let spec = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_cranelift_emit_object_raw")
            .expect("raw Cranelift object emission must be registered for native codegen");
        assert_eq!(spec.params, [I64, I64, I64]);
        assert_eq!(spec.returns, [I8]);
        assert_eq!(spec.tier(), RuntimeFuncTier::Ext);
    }

    #[test]
    fn host_gpu_payload_text_queue_signature_is_registered() {
        let spec = RUNTIME_FUNCS
            .iter()
            .find(|spec| spec.name == "rt_host_gpu_queue_emit_payload_text")
            .expect("native Draw IR queue payload emission must be registered");
        assert_eq!(spec.params, [I64, I64, I64, I64, I64, I64]);
        assert_eq!(spec.returns, [I64]);
        assert_eq!(spec.tier(), RuntimeFuncTier::Ext);
    }

    #[test]
    fn tier_counts_are_reasonable() {
        let mut counts = std::collections::HashMap::new();
        for spec in RUNTIME_FUNCS {
            *counts.entry(tier_of(spec.name)).or_insert(0usize) += 1;
        }
        // Each tier should have at least a few functions
        assert!(
            *counts.get(&RuntimeFuncTier::Core).unwrap_or(&0) >= 5,
            "Core tier should have at least 5 functions"
        );
        assert!(
            *counts.get(&RuntimeFuncTier::Alloc).unwrap_or(&0) >= 20,
            "Alloc tier should have at least 20 functions"
        );
        assert!(
            *counts.get(&RuntimeFuncTier::Sys).unwrap_or(&0) >= 30,
            "Sys tier should have at least 30 functions"
        );
        assert!(
            *counts.get(&RuntimeFuncTier::Async).unwrap_or(&0) >= 10,
            "Async tier should have at least 10 functions"
        );
        assert!(
            *counts.get(&RuntimeFuncTier::Ext).unwrap_or(&0) >= 20,
            "Ext tier should have at least 20 functions"
        );
    }

    #[test]
    fn baremetal_target_includes_all_tiers() {
        use simple_common::target::{Target, TargetArch, TargetOS};
        let baremetal = Target {
            arch: TargetArch::Aarch64,
            os: TargetOS::None,
            ..Target::default()
        };
        let funcs = runtime_funcs_for_target(&baremetal);
        // All tiers declared as imports; OS shim resolves at link time
        assert!(funcs.iter().any(|f| tier_of(f.name) == RuntimeFuncTier::Core));
        assert!(funcs.iter().any(|f| tier_of(f.name) == RuntimeFuncTier::Alloc));
        assert!(funcs.iter().any(|f| tier_of(f.name) == RuntimeFuncTier::Sys));
        assert!(funcs.iter().any(|f| tier_of(f.name) == RuntimeFuncTier::Async));
    }
}
