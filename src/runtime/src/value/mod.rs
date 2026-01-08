//! Runtime value representation for compiled code.
//!
//! This module provides a tagged pointer value representation that can be
//! used by the code generator. It mirrors the interpreter's `Value` enum
//! but uses a compact 64-bit representation suitable for machine code.
//!
//! ## Tagged Pointer Layout (64-bit)
//!
//! ```text
//! | Payload (61 bits)                              | Tag (3 bits) |
//! ```
//!
//! Tag values:
//! - 000 (0): Signed integer (61-bit, sign-extended)
//! - 001 (1): Heap pointer to object
//! - 010 (2): Float (uses NaN-boxing trick)
//! - 011 (3): Special values (nil, bool, symbol ID)
//! - 100-111: Reserved for future use

mod actors;
mod args;
mod async_gen;
#[cfg(feature = "ratatui-tui")]
pub mod ratatui_tui;
mod channels;
mod collections;
mod contracts;
mod dict;
mod core;
mod doctest_io;
mod ffi;
mod file_io;
pub mod gpu;
mod pty;
mod process;
#[cfg(feature = "vulkan")]
pub mod gpu_vulkan;
#[cfg(feature = "pytorch")]
pub mod torch;
pub mod gpu_backend;
mod heap;
pub mod net;
mod objects;
mod sync;
pub mod tags;

// Re-export core types
pub use core::RuntimeValue;
pub use heap::{HeapHeader, HeapObjectType};

// Re-export collection types
pub use collections::{RuntimeArray, RuntimeString, RuntimeTuple};
pub use dict::RuntimeDict;

// Re-export object types
pub use objects::{RuntimeClosure, RuntimeEnum, RuntimeObject, RuntimeShared, RuntimeUnique, RuntimeWeak};

// Re-export channel types
pub use channels::RuntimeChannel;

// Re-export collection FFI functions
pub use collections::{
    rt_array_clear, rt_array_get, rt_array_len, rt_array_new, rt_array_pop, rt_array_push,
    rt_array_set, rt_contains, rt_index_get, rt_index_set, rt_slice, rt_string_concat,
    rt_string_data, rt_string_len, rt_string_new, rt_tuple_get, rt_tuple_len, rt_tuple_new,
    rt_tuple_set,
};

// Re-export dict FFI functions
pub use dict::{
    rt_dict_clear, rt_dict_get, rt_dict_keys, rt_dict_len, rt_dict_new, rt_dict_set, rt_dict_values,
};

// Re-export object FFI functions
pub use objects::{
    rt_closure_func_ptr, rt_closure_get_capture, rt_closure_new, rt_closure_set_capture,
    rt_enum_discriminant, rt_enum_new, rt_enum_payload, rt_object_class_id, rt_object_field_count,
    rt_object_field_get, rt_object_field_set, rt_object_new,
};

// Re-export unique pointer FFI functions
pub use objects::{
    rt_unique_free, rt_unique_get, rt_unique_needs_trace, rt_unique_new, rt_unique_set,
};

// Re-export shared pointer FFI functions
pub use objects::{
    rt_shared_clone, rt_shared_downgrade, rt_shared_get, rt_shared_needs_trace, rt_shared_new,
    rt_shared_ref_count, rt_shared_release,
};

// Re-export weak pointer FFI functions
pub use objects::{rt_weak_free, rt_weak_is_valid, rt_weak_new, rt_weak_upgrade};

// Re-export actor FFI functions
pub use actors::{rt_actor_id, rt_actor_is_alive, rt_actor_join, rt_actor_recv, rt_actor_send, rt_actor_spawn, rt_wait};

// Re-export channel FFI functions
pub use channels::{
    rt_channel_close, rt_channel_free, rt_channel_id, rt_channel_is_closed, rt_channel_new,
    rt_channel_recv, rt_channel_recv_timeout, rt_channel_send, rt_channel_try_recv,
};

// Re-export synchronization primitives FFI functions
pub use sync::{
    // Mutex
    rt_mutex_free, rt_mutex_id, rt_mutex_lock, rt_mutex_new, rt_mutex_try_lock, rt_mutex_unlock,
    // RwLock
    rt_rwlock_free, rt_rwlock_new, rt_rwlock_read, rt_rwlock_set, rt_rwlock_try_read,
    rt_rwlock_try_write, rt_rwlock_write,
    // Semaphore
    rt_semaphore_acquire, rt_semaphore_acquire_timeout, rt_semaphore_count, rt_semaphore_free,
    rt_semaphore_new, rt_semaphore_release, rt_semaphore_try_acquire,
    // Barrier
    rt_barrier_free, rt_barrier_new, rt_barrier_thread_count, rt_barrier_wait,
};

// Re-export synchronization types
pub use sync::{RuntimeBarrier, RuntimeMutex, RuntimeRwLock, RuntimeSemaphore};

// Re-export async/generator FFI functions
pub use async_gen::{
    rt_async_get_ctx, rt_async_get_state, rt_async_mark_done, rt_async_set_state, rt_future_all,
    rt_future_await, rt_future_get_result, rt_future_is_ready, rt_future_new, rt_future_race,
    rt_future_reject, rt_future_resolve, rt_generator_get_ctx, rt_generator_get_state,
    rt_generator_load_slot, rt_generator_mark_done, rt_generator_new, rt_generator_next,
    rt_generator_set_state, rt_generator_store_slot,
};

// Re-export core FFI functions
pub use ffi::{
    rt_alloc, rt_free, rt_function_not_found, rt_interp_call, rt_interp_eval,
    rt_method_not_found, rt_ptr_to_value, rt_value_as_bool, rt_value_as_float,
    rt_value_as_int, rt_value_bool, rt_value_eq, rt_value_float, rt_value_int,
    rt_value_is_bool, rt_value_is_float, rt_value_is_heap, rt_value_is_int, rt_value_is_nil,
    rt_value_nil, rt_value_to_ptr, rt_value_truthy,
};

// Re-export interpreter bridge handler setters (for compiler crate)
pub use ffi::{set_interp_call_handler, set_interp_eval_handler, InterpCallFn, InterpEvalFn};

// Re-export argument handling functions
pub use args::{
    rt_clear_args, rt_get_argc, rt_get_args, rt_set_args, rt_set_args_vec,
};

// Re-export I/O capture functions (for testing)
pub use ffi::{
    rt_capture_stderr_start, rt_capture_stderr_stop, rt_capture_stdout_start,
    rt_capture_stdout_stop, rt_clear_captured_stderr, rt_clear_captured_stdout,
    rt_get_captured_stderr, rt_get_captured_stdout, rt_is_stderr_capturing, rt_is_stdout_capturing,
};

// Re-export stdin mock functions (for testing)
pub use ffi::{rt_clear_stdin, rt_has_mock_stdin, rt_read_stdin_char, rt_read_stdin_line, rt_set_stdin};

// Re-export print FFI functions
pub use ffi::{
    rt_eprint_str, rt_eprint_value, rt_eprintln_str, rt_eprintln_value, rt_print_str,
    rt_print_value, rt_println_str, rt_println_value,
};

// Re-export doctest I/O FFI functions
pub use doctest_io::{
    doctest_is_dir, doctest_is_file, doctest_path_contains, doctest_path_exists,
    doctest_path_has_extension, doctest_read_file, doctest_walk_directory,
};

// Re-export contract violation types and FFI functions (CTR-050-054)
pub use contracts::{
    ContractViolationKind, RuntimeContractViolation,
    rt_contract_violation_free, rt_contract_violation_func_name, rt_contract_violation_kind,
    rt_contract_violation_message, rt_contract_violation_new, rt_is_contract_violation,
};

// Re-export GPU runtime FFI functions
pub use gpu::{
    // Work item identification
    rt_gpu_global_id, rt_gpu_local_id, rt_gpu_group_id,
    rt_gpu_global_size, rt_gpu_local_size, rt_gpu_num_groups,
    // Synchronization
    rt_gpu_barrier, rt_gpu_mem_fence,
    // Atomic operations (i64)
    rt_gpu_atomic_add_i64, rt_gpu_atomic_sub_i64, rt_gpu_atomic_xchg_i64,
    rt_gpu_atomic_cmpxchg_i64, rt_gpu_atomic_min_i64, rt_gpu_atomic_max_i64,
    rt_gpu_atomic_and_i64, rt_gpu_atomic_or_i64, rt_gpu_atomic_xor_i64,
    // Atomic operations (u32)
    rt_gpu_atomic_add_u32, rt_gpu_atomic_sub_u32, rt_gpu_atomic_xchg_u32,
    rt_gpu_atomic_cmpxchg_u32, rt_gpu_atomic_min_u32, rt_gpu_atomic_max_u32,
    rt_gpu_atomic_and_u32, rt_gpu_atomic_or_u32, rt_gpu_atomic_xor_u32,
    // Shared memory
    rt_gpu_shared_alloc, rt_gpu_shared_reset,
    // Kernel launch
    rt_gpu_launch, rt_gpu_launch_1d,
    // Types and utilities
    GpuWorkItemState, GpuKernelFn,
    set_work_item_state, get_work_item_state,
    execute_kernel_1d, execute_kernel_3d,
};

// Re-export Vulkan GPU FFI functions
#[cfg(feature = "vulkan")]
pub use gpu_vulkan::{
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

// Re-export PyTorch tensor FFI functions
#[cfg(feature = "pytorch")]
pub use torch::{
    // Availability
    rt_torch_available, rt_torch_cuda_available, rt_torch_cuda_device_count,
    // Tensor creation
    rt_torch_zeros, rt_torch_ones, rt_torch_randn, rt_torch_arange, rt_torch_clone,
    // Memory management
    rt_torch_free,
    // Metadata
    rt_torch_shape, rt_torch_dtype, rt_torch_numel, rt_torch_device,
    // Element-wise binary operations
    rt_torch_add, rt_torch_sub, rt_torch_mul, rt_torch_div,
    // Scalar operations
    rt_torch_add_scalar, rt_torch_sub_scalar, rt_torch_mul_scalar, rt_torch_div_scalar,
    // Unary operations
    rt_torch_pow, rt_torch_sqrt, rt_torch_exp, rt_torch_log,
    // Matrix operations
    rt_torch_matmul, rt_torch_bmm, rt_torch_transpose,
    // Activation functions
    rt_torch_relu, rt_torch_sigmoid, rt_torch_tanh,
    // Shape operations
    rt_torch_reshape, rt_torch_permute, rt_torch_squeeze, rt_torch_unsqueeze,
    rt_torch_slice, rt_torch_cat, rt_torch_stack,
    // Device operations
    rt_torch_to_device, rt_torch_to_cpu, rt_torch_to_cuda,
    // Data access
    rt_torch_copy_data_to_cpu, rt_torch_item, rt_torch_sum, rt_torch_mean,
    // Memory management
    rt_torch_cuda_synchronize, rt_torch_cuda_memory_allocated, rt_torch_cuda_reset_peak_memory_stats,
    // Reduction operations
    rt_torch_max, rt_torch_min, rt_torch_argmax, rt_torch_argmin,
    // Comparison operations
    rt_torch_eq, rt_torch_ne, rt_torch_gt, rt_torch_lt, rt_torch_ge, rt_torch_le,
    // Autograd - gradient tracking
    rt_torch_set_requires_grad, rt_torch_requires_grad, rt_torch_is_leaf,
    // Autograd - gradient access
    rt_torch_grad, rt_torch_zero_grad, rt_torch_detach,
    // Autograd - backward pass
    rt_torch_backward, rt_torch_retain_grad,
    // Autograd - advanced
    rt_torch_set_grad_enabled, rt_torch_is_grad_enabled, rt_torch_shallow_clone,
    // Neural Network - advanced activations
    rt_torch_gelu, rt_torch_leaky_relu, rt_torch_silu, rt_torch_mish, rt_torch_elu, rt_torch_softplus,
    rt_torch_softmax, rt_torch_log_softmax,
    // Neural Network - loss functions
    rt_torch_mse_loss, rt_torch_cross_entropy, rt_torch_nll_loss,
    // Neural Network - normalization & dropout
    rt_torch_layer_norm, rt_torch_dropout,
    // Neural Network - initialization
    rt_torch_normal_, rt_torch_uniform_, rt_torch_xavier_uniform_, rt_torch_kaiming_uniform_,
    // Optimizers - creation
    rt_torch_sgd_new, rt_torch_adam_new, rt_torch_adamw_new,
    // Optimizers - operations
    rt_torch_optimizer_step, rt_torch_optimizer_zero_grad,
    rt_torch_optimizer_get_lr, rt_torch_optimizer_set_lr, rt_torch_optimizer_free,
    // Neural Network Modules - Linear
    rt_torch_linear_new, rt_torch_linear_forward,
    rt_torch_linear_get_weight, rt_torch_linear_get_bias,
    // Neural Network Modules - Conv2d
    rt_torch_conv2d_new, rt_torch_conv2d_forward,
    // Neural Network Modules - Pooling
    rt_torch_max_pool2d, rt_torch_avg_pool2d,
    // Neural Network Modules - Global & Adaptive Pooling
    rt_torch_global_avg_pool2d, rt_torch_global_max_pool2d,
    rt_torch_adaptive_avg_pool2d, rt_torch_adaptive_max_pool2d,
    // Neural Network Modules - BatchNorm
    rt_torch_batchnorm2d_new, rt_torch_batchnorm2d_forward,
    rt_torch_batchnorm2d_get_running_mean, rt_torch_batchnorm2d_get_running_var,
    // Neural Network Modules - Dropout
    rt_torch_dropout_new, rt_torch_dropout_forward,
    // Neural Network Modules - LayerNorm
    rt_torch_layernorm_new, rt_torch_layernorm_forward,
    rt_torch_layernorm_get_weight, rt_torch_layernorm_get_bias,
    // Neural Network Modules - Embedding
    rt_torch_embedding_new, rt_torch_embedding_forward,
    rt_torch_embedding_get_weight, rt_torch_embedding_from_pretrained,
    // Neural Network Modules - RNN (LSTM, GRU)
    rt_torch_lstm_new, rt_torch_lstm_forward,
    rt_torch_gru_new, rt_torch_gru_forward,
    // Neural Network Modules - Management
    rt_torch_module_free,
    // Learning Rate Schedulers - Creation
    rt_torch_scheduler_step_new, rt_torch_scheduler_exponential_new,
    rt_torch_scheduler_cosine_new, rt_torch_scheduler_plateau_new,
    // Learning Rate Schedulers - Operations
    rt_torch_scheduler_step, rt_torch_scheduler_step_with_metric, rt_torch_scheduler_free,
    // Data Loading - Dataset
    rt_torch_tensor_dataset_new, rt_torch_dataset_len, rt_torch_dataset_get, rt_torch_dataset_free,
    // Data Loading - DataLoader
    rt_torch_dataloader_new, rt_torch_dataloader_next, rt_torch_dataloader_reset, rt_torch_dataloader_free,
    // Error codes
    TorchFfiError,
};

// Re-export Ratatui TUI FFI functions
#[cfg(feature = "ratatui-tui")]
pub use ratatui_tui::{
    // Terminal operations
    ratatui_terminal_new, ratatui_terminal_cleanup,
    ratatui_terminal_clear,
    // Text buffer operations
    ratatui_textbuffer_new,
    ratatui_textbuffer_insert_char, ratatui_textbuffer_backspace,
    ratatui_textbuffer_newline,
    ratatui_textbuffer_get_text, ratatui_textbuffer_set_text,
    // Rendering
    ratatui_render_textbuffer,
    // Event handling
    ratatui_read_event, ratatui_read_event_timeout,
    // Cleanup
    ratatui_object_destroy,
};

// Re-export networking FFI functions
pub use net::{
    // Error types
    NetError,
    // TCP functions
    native_tcp_bind, native_tcp_accept, native_tcp_connect, native_tcp_connect_timeout,
    native_tcp_read, native_tcp_write, native_tcp_flush, native_tcp_shutdown, native_tcp_close,
    native_tcp_set_backlog, native_tcp_set_nodelay, native_tcp_set_keepalive,
    native_tcp_set_read_timeout, native_tcp_set_write_timeout,
    native_tcp_get_nodelay, native_tcp_peek,
    // UDP functions
    native_udp_bind, native_udp_connect, native_udp_recv_from, native_udp_recv,
    native_udp_send_to, native_udp_send, native_udp_peek_from, native_udp_peek,
    native_udp_peer_addr, native_udp_set_broadcast, native_udp_set_multicast_loop,
    native_udp_set_multicast_ttl, native_udp_set_ttl, native_udp_set_read_timeout,
    native_udp_set_write_timeout, native_udp_get_broadcast, native_udp_get_ttl,
    native_udp_join_multicast_v4, native_udp_leave_multicast_v4,
    native_udp_join_multicast_v6, native_udp_leave_multicast_v6, native_udp_close,
    // HTTP functions
    native_http_send, native_http_response_free,
};

// Re-export file I/O FFI functions - Mold-inspired optimizations
pub use file_io::{
    // Low-level system calls
    sys_mmap, sys_munmap, sys_madvise,
    sys_open, sys_close, sys_file_size, sys_file_exists,
    // Memory-mapped file operations
    native_mmap_create, native_mmap_create_shared, native_mmap_read, native_mmap_unmap,
    // File I/O hints
    native_fadvise_sequential, native_fadvise_random,
    native_fadvise_willneed, native_fadvise_dontneed,
    // Zero-copy operations
    native_sendfile, native_copy_file_range,
    // Standard file operations
    native_fs_open, native_file_read, native_file_write,
    native_file_close, native_file_flush, native_file_seek, native_file_sync,
    // Process management with staging
    native_spawn_worker, native_process_wait,
    native_process_is_alive, native_process_kill,
    // Async file loading (#1765-#1769)
    native_async_file_create, native_async_file_start_loading,
    native_async_file_is_ready, native_async_file_get_state,
    native_async_file_wait,
    // Path resolution and async primitives
    native_path_resolve, async_yield,
};

// ============================================================================
// Tests
// ============================================================================


#[cfg(test)]
#[path = "mod_tests.rs"]
mod tests;
