//! Runtime FFI function declarations for codegen.
//!
//! This module provides a shared specification of runtime functions that
//! both AOT (cranelift.rs) and JIT (jit.rs) compilers need to declare.

use cranelift_codegen::ir::{types, AbiParam, Signature};
use cranelift_codegen::isa::CallConv;

/// Specification for a runtime FFI function signature.
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
    pub const fn new(
        name: &'static str,
        params: &'static [types::Type],
        returns: &'static [types::Type],
    ) -> Self {
        Self {
            name,
            params,
            returns,
        }
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

/// All runtime FFI function specifications.
pub static RUNTIME_FUNCS: &[RuntimeFuncSpec] = &[
    // =========================================================================
    // AOP runtime operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_aop_invoke_around", &[I64, I64, I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_aop_proceed", &[I64], &[I64]),
    // =========================================================================
    // Array operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_array_new", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_push", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_get", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_set", &[I64, I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_array_pop", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_array_clear", &[I64], &[I8]),
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
    RuntimeFuncSpec::new("rt_vec_extract", &[I64, I64], &[I64]),  // (vector, index) -> element
    RuntimeFuncSpec::new("rt_vec_with", &[I64, I64, I64], &[I64]), // (vector, index, value) -> new_vector
    // Element-wise math operations (SIMD)
    RuntimeFuncSpec::new("rt_vec_sqrt", &[I64], &[I64]),  // (vector) -> vector with sqrt applied
    RuntimeFuncSpec::new("rt_vec_abs", &[I64], &[I64]),   // (vector) -> vector with abs applied
    RuntimeFuncSpec::new("rt_vec_floor", &[I64], &[I64]), // (vector) -> vector with floor applied
    RuntimeFuncSpec::new("rt_vec_ceil", &[I64], &[I64]),  // (vector) -> vector with ceil applied
    RuntimeFuncSpec::new("rt_vec_round", &[I64], &[I64]), // (vector) -> vector with round applied
    RuntimeFuncSpec::new("rt_vec_shuffle", &[I64, I64], &[I64]), // (vector, indices) -> shuffled vector
    RuntimeFuncSpec::new("rt_vec_blend", &[I64, I64, I64], &[I64]), // (vec1, vec2, indices) -> blended vector
    RuntimeFuncSpec::new("rt_vec_select", &[I64, I64, I64], &[I64]), // (mask, if_true, if_false) -> selected vector
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
    // =========================================================================
    // Value creation/conversion
    // =========================================================================
    RuntimeFuncSpec::new("rt_value_int", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_float", &[F64], &[I64]),
    RuntimeFuncSpec::new("rt_value_bool", &[I8], &[I64]),
    RuntimeFuncSpec::new("rt_value_nil", &[], &[I64]),
    RuntimeFuncSpec::new("rt_value_as_int", &[I64], &[I64]),
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
    RuntimeFuncSpec::new("rt_enum_discriminant", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_enum_payload", &[I64], &[I64]),
    // =========================================================================
    // Unique pointer operations (GC-collaborative manual memory)
    // =========================================================================
    RuntimeFuncSpec::new("rt_unique_new", &[I64], &[I64]),        // value -> unique ptr
    RuntimeFuncSpec::new("rt_unique_get", &[I64], &[I64]),        // unique -> value
    RuntimeFuncSpec::new("rt_unique_set", &[I64, I64], &[I64]),   // unique, new_value -> success
    RuntimeFuncSpec::new("rt_unique_free", &[I64], &[]),          // unique -> ()
    RuntimeFuncSpec::new("rt_unique_needs_trace", &[I64], &[I64]), // unique -> bool
    // =========================================================================
    // Shared pointer operations (reference-counted, GC-collaborative)
    // =========================================================================
    RuntimeFuncSpec::new("rt_shared_new", &[I64], &[I64]),        // value -> shared ptr
    RuntimeFuncSpec::new("rt_shared_get", &[I64], &[I64]),        // shared -> value
    RuntimeFuncSpec::new("rt_shared_clone", &[I64], &[I64]),      // shared -> shared (inc refcount)
    RuntimeFuncSpec::new("rt_shared_ref_count", &[I64], &[I64]),  // shared -> count
    RuntimeFuncSpec::new("rt_shared_release", &[I64], &[I64]),    // shared -> freed?
    RuntimeFuncSpec::new("rt_shared_needs_trace", &[I64], &[I64]), // shared -> bool
    RuntimeFuncSpec::new("rt_shared_downgrade", &[I64], &[I64]),  // shared -> weak
    // =========================================================================
    // Weak pointer operations (non-owning reference to shared)
    // =========================================================================
    RuntimeFuncSpec::new("rt_weak_new", &[I64, I64], &[I64]),     // shared_value, addr -> weak
    RuntimeFuncSpec::new("rt_weak_upgrade", &[I64], &[I64]),      // weak -> shared or NIL
    RuntimeFuncSpec::new("rt_weak_is_valid", &[I64], &[I64]),     // weak -> bool
    RuntimeFuncSpec::new("rt_weak_free", &[I64], &[]),            // weak -> ()
    // =========================================================================
    // Handle pointer operations (pool-allocated, index-based)
    // =========================================================================
    RuntimeFuncSpec::new("rt_handle_new", &[I64], &[I64]),        // value -> handle
    RuntimeFuncSpec::new("rt_handle_get", &[I64], &[I64]),        // handle -> value
    RuntimeFuncSpec::new("rt_handle_set", &[I64, I64], &[I64]),   // handle, new_value -> success
    RuntimeFuncSpec::new("rt_handle_free", &[I64], &[]),          // handle -> ()
    RuntimeFuncSpec::new("rt_handle_is_valid", &[I64], &[I64]),   // handle -> bool
    // =========================================================================
    // Raw memory allocation (zero-cost struct support)
    // =========================================================================
    RuntimeFuncSpec::new("rt_alloc", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_free", &[I64, I64], &[]),
    RuntimeFuncSpec::new("rt_ptr_to_value", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_value_to_ptr", &[I64], &[I64]),
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
    // =========================================================================
    // Isolated Thread operations
    // =========================================================================
    RuntimeFuncSpec::new("rt_thread_spawn_isolated", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_spawn_isolated2", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_join", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_is_done", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_id", &[I64], &[I64]),
    RuntimeFuncSpec::new("rt_thread_free", &[I64], &[]),
    RuntimeFuncSpec::new("rt_thread_available_parallelism", &[], &[I64]),
    RuntimeFuncSpec::new("rt_thread_sleep", &[I64], &[]),
    RuntimeFuncSpec::new("rt_thread_yield", &[], &[]),
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
    // Interpreter bridge FFI (for hybrid execution)
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
    RuntimeFuncSpec::new("doctest_path_has_extension", &[I64, I64], &[I64]), // path, ext -> bool (RuntimeValue)
    RuntimeFuncSpec::new("doctest_path_contains", &[I64, I64], &[I64]), // path, pattern -> bool (RuntimeValue)
    // =========================================================================
    // GPU work item identification
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_global_id", &[I32], &[I64]),   // dim -> id
    RuntimeFuncSpec::new("rt_gpu_local_id", &[I32], &[I64]),    // dim -> id
    RuntimeFuncSpec::new("rt_gpu_group_id", &[I32], &[I64]),    // dim -> id
    RuntimeFuncSpec::new("rt_gpu_global_size", &[I32], &[I64]), // dim -> size
    RuntimeFuncSpec::new("rt_gpu_local_size", &[I32], &[I64]),  // dim -> size
    RuntimeFuncSpec::new("rt_gpu_num_groups", &[I32], &[I64]),  // dim -> count
    // =========================================================================
    // GPU synchronization
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_barrier", &[], &[]),           // () -> ()
    RuntimeFuncSpec::new("rt_gpu_mem_fence", &[I32], &[]),      // scope -> ()
    // =========================================================================
    // GPU atomic operations (i64)
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_atomic_add_i64", &[I64, I64], &[I64]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_sub_i64", &[I64, I64], &[I64]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_xchg_i64", &[I64, I64], &[I64]),     // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_cmpxchg_i64", &[I64, I64, I64], &[I64]), // ptr, expected, new -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_min_i64", &[I64, I64], &[I64]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_max_i64", &[I64, I64], &[I64]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_and_i64", &[I64, I64], &[I64]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_or_i64", &[I64, I64], &[I64]),       // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_xor_i64", &[I64, I64], &[I64]),      // ptr, value -> old
    // =========================================================================
    // GPU atomic operations (u32)
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_atomic_add_u32", &[I64, I32], &[I32]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_sub_u32", &[I64, I32], &[I32]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_xchg_u32", &[I64, I32], &[I32]),     // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_cmpxchg_u32", &[I64, I32, I32], &[I32]), // ptr, expected, new -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_min_u32", &[I64, I32], &[I32]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_max_u32", &[I64, I32], &[I32]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_and_u32", &[I64, I32], &[I32]),      // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_or_u32", &[I64, I32], &[I32]),       // ptr, value -> old
    RuntimeFuncSpec::new("rt_gpu_atomic_xor_u32", &[I64, I32], &[I32]),      // ptr, value -> old
    // =========================================================================
    // GPU shared memory
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_shared_alloc", &[I64], &[I64]),  // size -> ptr
    RuntimeFuncSpec::new("rt_gpu_shared_reset", &[], &[]),        // () -> ()
    // =========================================================================
    // GPU kernel launch
    // =========================================================================
    RuntimeFuncSpec::new("rt_gpu_launch", &[I64, I32, I32, I32, I32, I32, I32], &[I32]), // kernel, gx,gy,gz, lx,ly,lz -> status
    RuntimeFuncSpec::new("rt_gpu_launch_1d", &[I64, I32, I32], &[I32]), // kernel, global, local -> status
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
        let sig = spec.build_signature(CallConv::SystemV);
        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.returns.len(), 1);
    }
}
