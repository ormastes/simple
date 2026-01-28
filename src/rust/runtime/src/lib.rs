// Allow warnings for incomplete features and FFI code
#![allow(clippy::missing_safety_doc)]
#![allow(clippy::type_complexity)]
#![allow(clippy::not_unsafe_ptr_arg_deref)]
#![allow(clippy::fn_to_numeric_cast)]
#![allow(clippy::fn_to_numeric_cast_with_truncation)]
#![allow(improper_ctypes_definitions)]
#![allow(dead_code)]

pub mod aop;
pub mod concurrency;
pub mod concurrent;
pub mod coverage;
pub mod cuda_runtime;
pub mod executor;
pub mod memory;
#[cfg(feature = "monoio-net")]
pub mod monoio_runtime;
#[cfg(feature = "monoio-net")]
pub mod monoio_tcp_v2;
#[cfg(feature = "monoio-net")]
pub mod monoio_thread;
#[cfg(feature = "monoio-net")]
pub mod monoio_udp_v2;
// Direct monoio integration (zero-overhead async I/O)
#[cfg(feature = "monoio-direct")]
pub mod monoio_buffer;
#[cfg(feature = "monoio-direct")]
pub mod monoio_direct;
#[cfg(feature = "monoio-direct")]
pub mod monoio_executor;
#[cfg(feature = "monoio-direct")]
pub mod monoio_waker;
#[cfg(feature = "vulkan")]
pub mod vulkan;

// Initialize runtime thread on first use
#[cfg(feature = "monoio-net")]
#[ctor::ctor]
fn init_monoio() {
    monoio_thread::init_runtime_thread();
}
pub mod parallel;
pub mod sandbox;
pub mod value;

// Re-export executor types and functions
pub use executor::{
    configure_async_mode,
    configure_worker_count,
    executor,
    is_manual_mode,
    pending_count,
    poll_all,
    poll_one,
    // Executor FFI functions
    rt_executor_get_mode,
    rt_executor_is_manual,
    rt_executor_pending_count,
    rt_executor_poll,
    rt_executor_poll_all,
    rt_executor_set_mode,
    rt_executor_set_workers,
    rt_executor_shutdown,
    rt_executor_start,
    rt_thread_available_parallelism,
    rt_thread_free,
    rt_thread_id,
    rt_thread_is_done,
    rt_thread_join,
    rt_thread_sleep,
    // Isolated thread FFI functions
    rt_thread_spawn_isolated,
    rt_thread_spawn_isolated2,
    rt_thread_yield,
    spawn,
    AsyncMode,
    FutureExecutor,
    Promise,
    PromiseState,
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
    HeapHeader, HeapObjectType, RuntimeArray, RuntimeChannel, RuntimeClosure, RuntimeEnum, RuntimeObject,
    RuntimeShared, RuntimeString, RuntimeTuple, RuntimeUnique, RuntimeValue, RuntimeWeak,
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
    rt_enum_check_discriminant,
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
    rt_cstring_to_text,
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
    rt_contract_violation_free, rt_contract_violation_func_name, rt_contract_violation_kind,
    rt_contract_violation_message, rt_contract_violation_new, rt_is_contract_violation, ContractViolationKind,
    RuntimeContractViolation,
};

// Re-export GPU runtime FFI functions
pub use value::{
    execute_kernel_1d,
    execute_kernel_3d,
    get_work_item_state,
    // GPU atomic operations (i64)
    rt_gpu_atomic_add_i64,
    // GPU atomic operations (u32)
    rt_gpu_atomic_add_u32,
    rt_gpu_atomic_and_i64,
    rt_gpu_atomic_and_u32,
    rt_gpu_atomic_cmpxchg_i64,
    rt_gpu_atomic_cmpxchg_u32,
    rt_gpu_atomic_max_i64,
    rt_gpu_atomic_max_u32,
    rt_gpu_atomic_min_i64,
    rt_gpu_atomic_min_u32,
    rt_gpu_atomic_or_i64,
    rt_gpu_atomic_or_u32,
    rt_gpu_atomic_sub_i64,
    rt_gpu_atomic_sub_u32,
    rt_gpu_atomic_xchg_i64,
    rt_gpu_atomic_xchg_u32,
    rt_gpu_atomic_xor_i64,
    rt_gpu_atomic_xor_u32,
    // GPU synchronization
    rt_gpu_barrier,
    // GPU work item identification
    rt_gpu_global_id,
    rt_gpu_global_size,
    rt_gpu_group_id,
    // GPU kernel launch
    rt_gpu_launch,
    rt_gpu_launch_1d,
    rt_gpu_local_id,
    rt_gpu_local_size,
    rt_gpu_mem_fence,
    rt_gpu_num_groups,
    // GPU shared memory
    rt_gpu_shared_alloc,
    rt_gpu_shared_reset,
    set_work_item_state,
    GpuKernelFn,
    // GPU types and utilities
    GpuWorkItemState,
};

// Re-export CUDA runtime types and FFI functions
pub use cuda_runtime::{
    get_device_count, rt_cuda_available, rt_cuda_device_count, rt_cuda_init, CudaDevice, CudaDevicePtr, CudaError,
    CudaKernel, CudaModule, CudaResult,
};

// Re-export Vulkan runtime types and functions
#[cfg(feature = "vulkan")]
pub use vulkan::{
    // Utility functions
    is_available as vulkan_is_available,
    BufferUsage,
    ComputePipeline,
    StagingBuffer,
    VulkanBuffer,
    // Core types
    VulkanDevice,
    // Error types
    VulkanError,
    VulkanInstance,
    VulkanPhysicalDevice,
    VulkanResult,
};

// Re-export Vulkan FFI functions
#[cfg(feature = "vulkan")]
pub use value::{
    // Device management
    rt_vk_available,
    // Buffer management
    rt_vk_buffer_alloc,
    rt_vk_buffer_download,
    rt_vk_buffer_free,
    rt_vk_buffer_upload,
    rt_vk_device_create,
    rt_vk_device_free,
    rt_vk_device_sync,
    // Kernel management
    rt_vk_kernel_compile,
    rt_vk_kernel_free,
    rt_vk_kernel_launch,
    rt_vk_kernel_launch_1d,
    // Error codes
    VulkanFfiError,
};

// Re-export Ratatui TUI FFI functions
#[cfg(feature = "ratatui-tui")]
pub use value::{
    // Cleanup
    ratatui_object_destroy,
    // Event handling
    ratatui_read_event,
    ratatui_read_event_timeout,
    // Rendering
    ratatui_render_textbuffer,
    ratatui_terminal_cleanup,
    ratatui_terminal_clear,
    // Terminal operations
    ratatui_terminal_new,
    ratatui_textbuffer_backspace,
    ratatui_textbuffer_get_text,
    ratatui_textbuffer_insert_char,
    // Text buffer operations
    ratatui_textbuffer_new,
    ratatui_textbuffer_newline,
    ratatui_textbuffer_set_text,
};

// Re-export CPU parallel runtime FFI functions (Rayon backend)
pub use parallel::{
    // Atomic operations
    rt_par_atomic_add_i64,
    rt_par_atomic_cmpxchg_i64,
    rt_par_atomic_max_i64,
    rt_par_atomic_min_i64,
    rt_par_atomic_sub_i64,
    rt_par_atomic_xchg_i64,
    // Synchronization
    rt_par_barrier,
    // Work item identification
    rt_par_global_id,
    rt_par_global_size,
    rt_par_group_id,
    rt_par_launch,
    // Kernel launch
    rt_par_launch_1d,
    rt_par_local_id,
    rt_par_local_size,
    rt_par_mem_fence,
    rt_par_num_groups,
    // Shared memory
    rt_par_shared_alloc,
    rt_par_shared_reset,
    // Kernel context
    KernelContext,
    KernelFn,
};

// Re-export coverage instrumentation types and FFI functions
pub use coverage::{
    rt_coverage_clear, rt_coverage_condition_probe, rt_coverage_decision_probe, rt_coverage_dump_sdn,
    rt_coverage_enabled, rt_coverage_free_sdn, rt_coverage_path_finalize, rt_coverage_path_probe, CoverageData,
};

// Re-export concurrent collections types and FFI functions (#1108-#1112)
pub use concurrent::{
    simple_concurrent_map_clear,
    simple_concurrent_map_contains_key,
    simple_concurrent_map_free,
    simple_concurrent_map_get,
    simple_concurrent_map_insert,
    simple_concurrent_map_is_empty,
    simple_concurrent_map_len,
    // ConcurrentMap FFI
    simple_concurrent_map_new,
    simple_concurrent_map_remove,
    simple_concurrent_map_with_capacity,
    simple_concurrent_queue_free,
    simple_concurrent_queue_is_empty,
    simple_concurrent_queue_len,
    // ConcurrentQueue FFI
    simple_concurrent_queue_new,
    simple_concurrent_queue_push,
    simple_concurrent_queue_try_pop,
    simple_concurrent_stack_free,
    simple_concurrent_stack_is_empty,
    simple_concurrent_stack_len,
    // ConcurrentStack FFI
    simple_concurrent_stack_new,
    simple_concurrent_stack_push,
    simple_concurrent_stack_try_pop,
    simple_gc_barrier_end_collection,
    simple_gc_barrier_epoch,
    // Write barrier FFI
    simple_gc_barrier_start_collection,
    ConcurrentMap,
    // Types
    ConcurrentQueue,
    ConcurrentStack,
    GcWriteBarrier,
    TraceConcurrent,
};

// Re-export sandbox types and functions (#916-923)
pub use sandbox::{
    apply_sandbox, FilesystemIsolation, FilesystemMode, NetworkIsolation, NetworkMode, ResourceLimits, SandboxConfig,
    SandboxError, SandboxResult,
};

// Re-export monoio runtime types and functions (#1730-1759)
#[cfg(feature = "monoio-net")]
pub use monoio_runtime::{
    monoio_block_on,
    monoio_configure_entries,
    // Configuration
    monoio_get_num_cores,
    // Statistics
    monoio_get_stats,
    monoio_reset_stats,
    // Runtime lifecycle
    monoio_runtime_init,
    monoio_runtime_init_global,
    monoio_runtime_shutdown,
    monoio_runtime_shutdown_global,
    // Task management
    monoio_spawn_local,
};

// Re-export monoio TCP functions (#1745-1749)
#[cfg(feature = "monoio-net")]
pub use monoio_tcp_v2::{
    monoio_tcp_accept,
    monoio_tcp_close,
    // Client operations
    monoio_tcp_connect,
    monoio_tcp_flush,
    // Server operations
    monoio_tcp_listen,
    monoio_tcp_listener_close,
    monoio_tcp_local_addr,
    monoio_tcp_peer_addr,
    // I/O operations
    monoio_tcp_read,
    monoio_tcp_set_keepalive,
    // Socket options
    monoio_tcp_set_nodelay,
    // Connection management
    monoio_tcp_shutdown,
    monoio_tcp_write,
};

// Re-export monoio UDP functions (#1745-1749)
#[cfg(feature = "monoio-net")]
pub use monoio_udp_v2::{
    // Socket operations
    monoio_udp_bind,
    monoio_udp_close,
    monoio_udp_connect,
    // Multicast
    monoio_udp_join_multicast,
    monoio_udp_leave_multicast,
    // Socket info
    monoio_udp_local_addr,
    monoio_udp_recv,
    monoio_udp_recv_from,
    // Connected I/O
    monoio_udp_send,
    // Unconnected I/O
    monoio_udp_send_to,
    // Socket options
    monoio_udp_set_broadcast,
    monoio_udp_set_multicast_ttl,
};

// Re-export monoio-direct types and FFI functions (zero-overhead async I/O)
#[cfg(feature = "monoio-direct")]
pub use monoio_buffer::{OwnedBuf, SimpleBuf};

#[cfg(feature = "monoio-direct")]
pub use monoio_direct::{
    // Runtime
    rt_monoio_init,
    rt_monoio_direct_stats,
    // TCP operations
    rt_monoio_tcp_accept,
    rt_monoio_tcp_accept_async,
    rt_monoio_tcp_close,
    rt_monoio_tcp_connect,
    rt_monoio_tcp_connect_async,
    rt_monoio_tcp_flush,
    rt_monoio_tcp_listen,
    rt_monoio_tcp_listener_close,
    rt_monoio_tcp_local_addr,
    rt_monoio_tcp_peer_addr,
    rt_monoio_tcp_read,
    rt_monoio_tcp_read_async,
    rt_monoio_tcp_set_keepalive,
    rt_monoio_tcp_set_nodelay,
    rt_monoio_tcp_shutdown,
    rt_monoio_tcp_write,
    rt_monoio_tcp_write_async,
    // UDP operations
    rt_monoio_udp_bind,
    rt_monoio_udp_close,
    rt_monoio_udp_connect,
    rt_monoio_udp_join_multicast,
    rt_monoio_udp_leave_multicast,
    rt_monoio_udp_local_addr,
    rt_monoio_udp_recv,
    rt_monoio_udp_recv_from,
    rt_monoio_udp_send,
    rt_monoio_udp_send_to,
    rt_monoio_udp_set_broadcast,
    rt_monoio_udp_set_multicast_ttl,
    // Future polling
    rt_monoio_poll,
};

#[cfg(feature = "monoio-direct")]
pub use monoio_waker::{
    rt_monoio_waker_free, rt_monoio_waker_get_wake_count, rt_monoio_waker_new, rt_monoio_waker_wake, SimpleWaker,
    WakerContext,
};

#[cfg(feature = "monoio-direct")]
pub use monoio_runtime::direct::{
    block_on as monoio_direct_block_on, has_direct_runtime as monoio_direct_has_runtime,
    init_direct_runtime as monoio_direct_init, shutdown_direct_runtime as monoio_direct_shutdown,
    with_registry as monoio_direct_with_registry, rt_monoio_direct_available, rt_monoio_direct_init,
    rt_monoio_direct_resource_count, rt_monoio_direct_shutdown, IoRegistry,
};

#[cfg(feature = "monoio-direct")]
pub use value::{
    rt_monoio_future_free, rt_monoio_future_get_async_state, rt_monoio_future_get_ctx, rt_monoio_future_get_io_handle,
    rt_monoio_future_get_operation_type, rt_monoio_future_get_result, rt_monoio_future_get_state,
    rt_monoio_future_is_pending, rt_monoio_future_is_ready, rt_monoio_future_new, rt_monoio_future_set_async_state,
    rt_monoio_future_set_error, rt_monoio_future_set_result, rt_monoio_is_pending, IoOperationType, MonoioFuture,
    FUTURE_STATE_ERROR, FUTURE_STATE_PENDING, FUTURE_STATE_READY, PENDING_MARKER,
};

// Re-export async executor types and FFI functions
#[cfg(feature = "monoio-direct")]
pub use monoio_executor::{
    with_executor,
    // FFI functions
    rt_monoio_async_init,
    rt_monoio_async_pending_count,
    rt_monoio_async_poll_all,
    rt_monoio_async_poll_one,
    // TCP async operations
    rt_monoio_async_tcp_accept,
    rt_monoio_async_tcp_close,
    rt_monoio_async_tcp_connect,
    rt_monoio_async_tcp_listen,
    rt_monoio_async_tcp_listener_close,
    rt_monoio_async_tcp_read,
    rt_monoio_async_tcp_write,
    // UDP async operations
    rt_monoio_async_udp_bind,
    rt_monoio_async_udp_close,
    // Types
    AsyncExecutor,
    HandleStore,
    OpResult,
    OpState,
    OpType,
    PendingOp,
};

// Unit tests
#[cfg(test)]
#[path = "../tests"]
mod tests {
    mod aop_around_tests;
    mod concurrency_tests;
    mod gc_allocator;
    mod gc_logging;
    mod no_gc_allocator;

    #[cfg(feature = "vulkan")]
    mod vulkan_ffi_tests;
}
