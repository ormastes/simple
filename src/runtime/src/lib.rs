pub mod concurrency;
pub mod cuda_runtime;
pub mod executor;
pub mod memory;
pub mod value;

// Re-export executor types and functions
pub use executor::{
    configure_async_mode, configure_worker_count, executor, is_manual_mode, pending_count,
    poll_all, poll_one, spawn, AsyncMode, FutureExecutor, Promise, PromiseState,
    // Executor FFI functions
    rt_executor_get_mode, rt_executor_is_manual, rt_executor_pending_count, rt_executor_poll,
    rt_executor_poll_all, rt_executor_set_mode, rt_executor_set_workers, rt_executor_shutdown,
    rt_executor_start,
    // Isolated thread FFI functions
    rt_thread_spawn_isolated, rt_thread_spawn_isolated2, rt_thread_join, rt_thread_is_done,
    rt_thread_id, rt_thread_free, rt_thread_available_parallelism, rt_thread_sleep, rt_thread_yield,
};

// Preserve the public `gc` module path for callers.
pub use memory::gc;
pub use memory::no_gc::NoGcAllocator;

/// ABI version exported for dynamic library loading.
///
/// This function is called by DynamicSymbolProvider to verify that the
/// loaded runtime library is compatible with the compiler/interpreter.
///
/// The version is encoded as: (major << 16) | minor
/// - major: Breaking changes (signature changes, removed symbols)
/// - minor: Additive changes (new symbols only)
#[no_mangle]
pub extern "C" fn simple_runtime_abi_version() -> u32 {
    simple_common::AbiVersion::CURRENT.to_u32()
}

// Re-export runtime value types for codegen
pub use value::{
    HeapHeader, HeapObjectType, RuntimeArray, RuntimeChannel, RuntimeClosure, RuntimeEnum,
    RuntimeObject, RuntimeShared, RuntimeString, RuntimeTuple, RuntimeUnique, RuntimeValue,
    RuntimeWeak,
};

// Re-export runtime FFI functions for codegen
pub use value::{
    // Doctest I/O operations
    doctest_is_dir,
    doctest_is_file,
    doctest_path_contains,
    doctest_path_exists,
    doctest_path_has_extension,
    doctest_read_file,
    doctest_walk_directory,
    // Actor operations
    rt_actor_id,
    rt_actor_is_alive,
    rt_actor_join,
    rt_actor_recv,
    rt_actor_send,
    rt_actor_spawn,
    // Raw memory allocation (zero-cost struct support)
    rt_alloc,
    // Array operations
    rt_array_get,
    rt_array_len,
    rt_array_new,
    rt_array_pop,
    rt_array_push,
    rt_array_set,
    // Channel operations
    rt_channel_close,
    rt_channel_free,
    rt_channel_id,
    rt_channel_is_closed,
    rt_channel_new,
    rt_channel_recv,
    rt_channel_recv_timeout,
    rt_channel_send,
    rt_channel_try_recv,
    // Closure operations
    rt_closure_func_ptr,
    rt_closure_get_capture,
    rt_closure_new,
    rt_closure_set_capture,
    // Dict operations
    rt_dict_get,
    rt_dict_len,
    rt_dict_new,
    rt_dict_set,
    // Enum operations
    rt_enum_discriminant,
    rt_enum_new,
    rt_enum_payload,
    rt_free,
    // Future operations
    rt_future_all,
    rt_future_await,
    rt_future_get_result,
    rt_future_is_ready,
    rt_future_new,
    rt_future_race,
    rt_future_reject,
    rt_future_resolve,
    // Generator operations
    rt_generator_get_ctx,
    rt_generator_get_state,
    rt_generator_load_slot,
    rt_generator_mark_done,
    rt_generator_new,
    rt_generator_next,
    rt_generator_set_state,
    rt_generator_store_slot,
    // Generic collection operations
    rt_index_get,
    rt_index_set,
    // Object operations
    rt_object_class_id,
    rt_object_field_count,
    rt_object_field_get,
    rt_object_field_set,
    rt_object_new,
    rt_ptr_to_value,
    // Shared pointer operations
    rt_shared_clone,
    rt_shared_downgrade,
    rt_shared_get,
    rt_shared_needs_trace,
    rt_shared_new,
    rt_shared_ref_count,
    rt_shared_release,
    rt_slice,
    // String operations
    rt_string_concat,
    rt_string_data,
    rt_string_len,
    rt_string_new,
    // Tuple operations
    rt_tuple_get,
    rt_tuple_len,
    rt_tuple_new,
    rt_tuple_set,
    // Unique pointer operations
    rt_unique_free,
    rt_unique_get,
    rt_unique_needs_trace,
    rt_unique_new,
    rt_unique_set,
    // Value extraction
    rt_value_as_bool,
    rt_value_as_float,
    rt_value_as_int,
    // Value creation
    rt_value_bool,
    rt_value_float,
    rt_value_int,
    // Value type checking
    rt_value_is_bool,
    rt_value_is_float,
    rt_value_is_heap,
    rt_value_is_int,
    rt_value_is_nil,
    rt_value_nil,
    rt_value_to_ptr,
    rt_value_truthy,
    // Wait operation
    rt_wait,
    // Weak pointer operations
    rt_weak_free,
    rt_weak_is_valid,
    rt_weak_new,
    rt_weak_upgrade,
};

// Re-export RuntimeDict struct
pub use value::RuntimeDict;

// Re-export contract violation types and FFI functions (CTR-050-054)
pub use value::{
    ContractViolationKind, RuntimeContractViolation,
    rt_contract_violation_free, rt_contract_violation_func_name, rt_contract_violation_kind,
    rt_contract_violation_message, rt_contract_violation_new, rt_is_contract_violation,
};

// Re-export GPU runtime FFI functions
pub use value::{
    // GPU work item identification
    rt_gpu_global_id, rt_gpu_local_id, rt_gpu_group_id,
    rt_gpu_global_size, rt_gpu_local_size, rt_gpu_num_groups,
    // GPU synchronization
    rt_gpu_barrier, rt_gpu_mem_fence,
    // GPU atomic operations (i64)
    rt_gpu_atomic_add_i64, rt_gpu_atomic_sub_i64, rt_gpu_atomic_xchg_i64,
    rt_gpu_atomic_cmpxchg_i64, rt_gpu_atomic_min_i64, rt_gpu_atomic_max_i64,
    rt_gpu_atomic_and_i64, rt_gpu_atomic_or_i64, rt_gpu_atomic_xor_i64,
    // GPU atomic operations (u32)
    rt_gpu_atomic_add_u32, rt_gpu_atomic_sub_u32, rt_gpu_atomic_xchg_u32,
    rt_gpu_atomic_cmpxchg_u32, rt_gpu_atomic_min_u32, rt_gpu_atomic_max_u32,
    rt_gpu_atomic_and_u32, rt_gpu_atomic_or_u32, rt_gpu_atomic_xor_u32,
    // GPU shared memory
    rt_gpu_shared_alloc, rt_gpu_shared_reset,
    // GPU kernel launch
    rt_gpu_launch, rt_gpu_launch_1d,
    // GPU types and utilities
    GpuWorkItemState, GpuKernelFn,
    set_work_item_state, get_work_item_state,
    execute_kernel_1d, execute_kernel_3d,
};

// Re-export CUDA runtime types and FFI functions
pub use cuda_runtime::{
    CudaDevice, CudaDevicePtr, CudaError, CudaKernel, CudaModule, CudaResult,
    get_device_count,
    rt_cuda_init, rt_cuda_device_count, rt_cuda_available,
};
