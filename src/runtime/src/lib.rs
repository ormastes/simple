pub mod concurrency;
pub mod concurrent;
pub mod coverage;
pub mod cuda_runtime;
#[cfg(feature = "vulkan")]
pub mod vulkan;
pub mod executor;
pub mod aop;
pub mod memory;
#[cfg(feature = "monoio-net")]
pub mod monoio_runtime;
#[cfg(feature = "monoio-net")]
pub mod monoio_tcp;
#[cfg(feature = "monoio-net")]
pub mod monoio_udp;
pub mod parallel;
pub mod sandbox;
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

// Re-export AOP runtime FFI functions
pub use aop::{rt_aop_invoke_around, rt_aop_proceed, AopAroundFn, AopTargetFn, ProceedContext};

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

// Re-export Vulkan runtime types and functions
#[cfg(feature = "vulkan")]
pub use vulkan::{
    // Core types
    VulkanDevice, VulkanInstance, VulkanPhysicalDevice,
    VulkanBuffer, StagingBuffer, BufferUsage,
    ComputePipeline,
    // Error types
    VulkanError, VulkanResult,
    // Utility functions
    is_available as vulkan_is_available,
};

// Re-export Vulkan FFI functions
#[cfg(feature = "vulkan")]
pub use value::{
    // Device management
    rt_vk_available, rt_vk_device_create, rt_vk_device_free, rt_vk_device_sync,
    // Buffer management
    rt_vk_buffer_alloc, rt_vk_buffer_free,
    rt_vk_buffer_upload, rt_vk_buffer_download,
    // Kernel management
    rt_vk_kernel_compile, rt_vk_kernel_free,
    rt_vk_kernel_launch, rt_vk_kernel_launch_1d,
    // Error codes
    VulkanFfiError,
};

// Re-export CPU parallel runtime FFI functions (Rayon backend)
pub use parallel::{
    // Kernel context
    KernelContext, KernelFn,
    // Work item identification
    rt_par_global_id, rt_par_local_id, rt_par_group_id,
    rt_par_global_size, rt_par_local_size, rt_par_num_groups,
    // Synchronization
    rt_par_barrier, rt_par_mem_fence,
    // Shared memory
    rt_par_shared_alloc, rt_par_shared_reset,
    // Kernel launch
    rt_par_launch_1d, rt_par_launch,
    // Atomic operations
    rt_par_atomic_add_i64, rt_par_atomic_sub_i64, rt_par_atomic_xchg_i64,
    rt_par_atomic_cmpxchg_i64, rt_par_atomic_min_i64, rt_par_atomic_max_i64,
};

// Re-export coverage instrumentation types and FFI functions
pub use coverage::{
    CoverageData,
    rt_coverage_decision_probe, rt_coverage_condition_probe,
    rt_coverage_path_probe, rt_coverage_path_finalize,
    rt_coverage_dump_sdn, rt_coverage_free_sdn,
    rt_coverage_clear, rt_coverage_enabled,
};

// Re-export concurrent collections types and FFI functions (#1108-#1112)
pub use concurrent::{
    // Types
    ConcurrentQueue, ConcurrentMap, ConcurrentStack,
    GcWriteBarrier, TraceConcurrent,
    // Write barrier FFI
    simple_gc_barrier_start_collection,
    simple_gc_barrier_end_collection,
    simple_gc_barrier_epoch,
    // ConcurrentQueue FFI
    simple_concurrent_queue_new,
    simple_concurrent_queue_free,
    simple_concurrent_queue_push,
    simple_concurrent_queue_try_pop,
    simple_concurrent_queue_is_empty,
    simple_concurrent_queue_len,
    // ConcurrentMap FFI
    simple_concurrent_map_new,
    simple_concurrent_map_with_capacity,
    simple_concurrent_map_free,
    simple_concurrent_map_insert,
    simple_concurrent_map_get,
    simple_concurrent_map_remove,
    simple_concurrent_map_contains_key,
    simple_concurrent_map_len,
    simple_concurrent_map_is_empty,
    simple_concurrent_map_clear,
    // ConcurrentStack FFI
    simple_concurrent_stack_new,
    simple_concurrent_stack_free,
    simple_concurrent_stack_push,
    simple_concurrent_stack_try_pop,
    simple_concurrent_stack_is_empty,
    simple_concurrent_stack_len,
};

// Re-export sandbox types and functions (#916-923)
pub use sandbox::{
    apply_sandbox, FilesystemIsolation, FilesystemMode, NetworkIsolation, NetworkMode,
    ResourceLimits, SandboxConfig, SandboxError, SandboxResult,
};

// Re-export monoio runtime types and functions (#1730-1759)
#[cfg(feature = "monoio-net")]
pub use monoio_runtime::{
    // Runtime lifecycle
    monoio_runtime_init, monoio_runtime_init_global,
    monoio_runtime_shutdown, monoio_runtime_shutdown_global,
    // Task management
    monoio_spawn_local, monoio_block_on,
    // Configuration
    monoio_get_num_cores, monoio_configure_entries,
    // Statistics
    monoio_get_stats, monoio_reset_stats,
};

// Re-export monoio TCP functions (#1745-1749)
#[cfg(feature = "monoio-net")]
pub use monoio_tcp::{
    // Server operations
    monoio_tcp_listen, monoio_tcp_accept, monoio_tcp_listener_close,
    // Client operations
    monoio_tcp_connect,
    // I/O operations
    monoio_tcp_read, monoio_tcp_write, monoio_tcp_flush,
    // Connection management
    monoio_tcp_shutdown, monoio_tcp_close,
    monoio_tcp_local_addr, monoio_tcp_peer_addr,
    // Socket options
    monoio_tcp_set_nodelay, monoio_tcp_set_keepalive,
};

// Re-export monoio UDP functions (#1745-1749)
#[cfg(feature = "monoio-net")]
pub use monoio_udp::{
    // Socket operations
    monoio_udp_bind, monoio_udp_connect, monoio_udp_close,
    // Unconnected I/O
    monoio_udp_send_to, monoio_udp_recv_from,
    // Connected I/O
    monoio_udp_send, monoio_udp_recv,
    // Socket info
    monoio_udp_local_addr,
    // Socket options
    monoio_udp_set_broadcast, monoio_udp_set_multicast_ttl,
    // Multicast
    monoio_udp_join_multicast, monoio_udp_leave_multicast,
};

// Unit tests
#[cfg(test)]
#[path = "../tests"]
mod tests {
    mod gc_allocator;
    mod gc_logging;
    mod no_gc_allocator;
    mod concurrency_tests;
    mod aop_around_tests;

    #[cfg(feature = "vulkan")]
    mod vulkan_ffi_tests;
}
