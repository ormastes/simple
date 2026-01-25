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
mod channels;
pub mod cli_ffi;
mod collections;
pub mod log_ffi;
mod contracts;
mod core;
pub mod diagram_ffi;
mod dict;
// FFI object-based system
pub mod ffi_example;
pub mod ffi_macros;
pub mod ffi_object;
pub mod ffi_registry;
pub mod sdn_ffi;
// High-performance collections module (using Rust std::collections)
pub mod hpcollections;
mod doctest_io;
pub mod ffi;
mod file_io;
pub mod gpu;
pub mod gpu_backend;
#[cfg(feature = "vulkan")]
pub mod gpu_vulkan;
pub mod heap;
#[cfg(feature = "monoio-direct")]
pub mod monoio_future;
pub mod net;
mod objects;
mod process;
mod pty;
#[cfg(feature = "ratatui-tui")]
pub mod ratatui_tui;
pub mod screenshot_ffi;
pub mod simd;
mod sync;
pub mod tags;
#[cfg(feature = "pytorch")]
pub mod torch;

// Re-export core types
pub use core::RuntimeValue;
pub use heap::{HeapHeader, HeapObjectType};

// Re-export collection types
pub use collections::{RuntimeArray, RuntimeString, RuntimeTuple};
pub use dict::RuntimeDict;

// Re-export object types
pub use objects::{RuntimeClosure, RuntimeEnum, RuntimeObject, RuntimeShared, RuntimeUnique, RuntimeWeak};

// Re-export FFI object types
pub use ffi_object::{
    FfiMethodEntry, FfiVtable, RuntimeFfiObject,
    fnv1a_hash, fnv1a_hash_str, method_flags,
    rt_ffi_object_call_method, rt_ffi_object_free, rt_ffi_object_handle,
    rt_ffi_object_has_method, rt_ffi_object_is_ffi, rt_ffi_object_new,
    rt_ffi_object_type_id, rt_ffi_object_type_name, rt_ffi_object_vtable,
};

// Re-export FFI registry types and functions
pub use ffi_registry::{
    FfiObjectStorage, FfiTypeMetadata, FfiTypeRegistry,
    get_registry,
    rt_ffi_call_method, rt_ffi_clear_registry, rt_ffi_clone, rt_ffi_drop,
    rt_ffi_has_method, rt_ffi_is_type, rt_ffi_new, rt_ffi_type_id,
    rt_ffi_type_name, rt_ffi_type_register,
};

// Re-export FFI macro helpers and traits
pub use ffi_macros::{
    FfiError, FfiResult, FromRuntimeValue, IntoRuntimeValue,
    get_arg, get_arg_as, get_bool_arg, get_float_arg, get_int_arg, get_string_arg,
    sort_method_entries,
};

// Re-export FFI example (Counter) for demonstration and testing
pub use ffi_example::{
    Counter, counter_new_ffi, counter_register_type, counter_vtable,
};

// Re-export channel types
pub use channels::RuntimeChannel;

// Re-export collection FFI functions
pub use collections::{
    rt_array_clear, rt_array_get, rt_array_len, rt_array_new, rt_array_pop, rt_array_push, rt_array_set, rt_contains,
    rt_cstring_to_text, rt_index_get, rt_index_set, rt_slice, rt_string_concat, rt_string_data, rt_string_ends_with,
    rt_string_len, rt_string_new, rt_string_starts_with, rt_tuple_get, rt_tuple_len, rt_tuple_new, rt_tuple_set,
};

// Re-export dict FFI functions
pub use dict::{
    rt_dict_clear, rt_dict_get, rt_dict_keys, rt_dict_len, rt_dict_new, rt_dict_remove, rt_dict_set, rt_dict_values,
};

// Re-export high-performance collection FFI functions (Rust std::collections)
pub use hpcollections::{
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

// Re-export object FFI functions
pub use objects::{
    rt_closure_func_ptr, rt_closure_get_capture, rt_closure_new, rt_closure_set_capture, rt_enum_discriminant,
    rt_enum_new, rt_enum_payload, rt_object_class_id, rt_object_field_count, rt_object_field_get, rt_object_field_set,
    rt_object_new,
};

// Re-export unique pointer FFI functions
pub use objects::{rt_unique_free, rt_unique_get, rt_unique_needs_trace, rt_unique_new, rt_unique_set};

// Re-export shared pointer FFI functions
pub use objects::{
    rt_shared_clone, rt_shared_downgrade, rt_shared_get, rt_shared_needs_trace, rt_shared_new, rt_shared_ref_count,
    rt_shared_release,
};

// Re-export weak pointer FFI functions
pub use objects::{rt_weak_free, rt_weak_is_valid, rt_weak_new, rt_weak_upgrade};

// Re-export actor FFI functions
pub use actors::{rt_actor_id, rt_actor_is_alive, rt_actor_join, rt_actor_recv, rt_actor_send, rt_actor_spawn, rt_wait};

// Re-export channel FFI functions
pub use channels::{
    rt_channel_close, rt_channel_free, rt_channel_id, rt_channel_is_closed, rt_channel_new, rt_channel_recv,
    rt_channel_recv_timeout, rt_channel_send, rt_channel_try_recv,
};

// Re-export synchronization primitives FFI functions
pub use sync::{
    // Atomic
    rt_atomic_compare_exchange,
    rt_atomic_fetch_add,
    rt_atomic_fetch_and,
    rt_atomic_fetch_or,
    rt_atomic_fetch_sub,
    rt_atomic_free,
    rt_atomic_load,
    rt_atomic_new,
    rt_atomic_store,
    rt_atomic_swap,
    // Barrier
    rt_barrier_free,
    rt_barrier_new,
    rt_barrier_thread_count,
    rt_barrier_wait,
    // Mutex
    rt_mutex_free,
    rt_mutex_id,
    rt_mutex_lock,
    rt_mutex_new,
    rt_mutex_try_lock,
    rt_mutex_unlock,
    // RwLock
    rt_rwlock_free,
    rt_rwlock_new,
    rt_rwlock_read,
    rt_rwlock_set,
    rt_rwlock_try_read,
    rt_rwlock_try_write,
    rt_rwlock_write,
    // Semaphore
    rt_semaphore_acquire,
    rt_semaphore_acquire_timeout,
    rt_semaphore_count,
    rt_semaphore_free,
    rt_semaphore_new,
    rt_semaphore_release,
    rt_semaphore_try_acquire,
};

// Re-export synchronization types
pub use sync::{RuntimeAtomic, RuntimeBarrier, RuntimeMutex, RuntimeRwLock, RuntimeSemaphore};

// Re-export async/generator FFI functions
pub use async_gen::{
    rt_async_get_ctx, rt_async_get_state, rt_async_mark_done, rt_async_set_state, rt_future_all, rt_future_await,
    rt_future_get_result, rt_future_is_ready, rt_future_new, rt_future_race, rt_future_reject, rt_future_resolve,
    rt_generator_get_ctx, rt_generator_get_state, rt_generator_load_slot, rt_generator_mark_done, rt_generator_new,
    rt_generator_next, rt_generator_set_state, rt_generator_store_slot,
};

// Re-export core FFI functions
pub use ffi::{
    rt_alloc, rt_free, rt_function_not_found, rt_interp_call, rt_interp_eval, rt_method_not_found, rt_ptr_to_value,
    rt_value_as_bool, rt_value_as_float, rt_value_as_int, rt_value_bool, rt_value_eq, rt_value_float, rt_value_int,
    rt_value_is_bool, rt_value_is_float, rt_value_is_heap, rt_value_is_int, rt_value_is_nil, rt_value_nil,
    rt_value_to_ptr, rt_value_truthy,
};

// Re-export interpreter bridge handler setters (for compiler crate)
pub use ffi::{set_interp_call_handler, set_interp_eval_handler, InterpCallFn, InterpEvalFn};

// Re-export argument handling functions
pub use args::{rt_clear_args, rt_get_argc, rt_get_args, rt_set_args, rt_set_args_vec};

// Re-export I/O capture functions (for testing)
pub use ffi::{
    rt_capture_stderr_start, rt_capture_stderr_stop, rt_capture_stdout_start, rt_capture_stdout_stop,
    rt_clear_captured_stderr, rt_clear_captured_stdout, rt_get_captured_stderr, rt_get_captured_stdout,
    rt_is_stderr_capturing, rt_is_stdout_capturing,
};

// Re-export stdin mock functions (for testing)
pub use ffi::{rt_clear_stdin, rt_has_mock_stdin, rt_read_stdin_char, rt_read_stdin_line, rt_set_stdin};

// Re-export print FFI functions
pub use ffi::{
    rt_eprint_str, rt_eprint_value, rt_eprintln_str, rt_eprintln_value, rt_print_str, rt_print_value, rt_println_str,
    rt_println_value, rt_value_to_string,
};

// Re-export log FFI functions
pub use log_ffi::{
    rt_log_clear_scope_levels, rt_log_debug, rt_log_emit, rt_log_emit_rv, rt_log_error, rt_log_fatal,
    rt_log_get_global_level, rt_log_get_scope_level, rt_log_info, rt_log_is_enabled, rt_log_level_name,
    rt_log_set_global_level, rt_log_set_scope_level, rt_log_trace, rt_log_verbose, rt_log_warn,
};

// Re-export time FFI functions
pub use ffi::rt_time_now_seconds;

// Re-export environment & process FFI functions
pub use ffi::{
    rt_condition_probe, rt_decision_probe, rt_env_all, rt_env_cwd, rt_env_exists, rt_env_get, rt_env_home,
    rt_env_remove, rt_env_set, rt_env_temp, rt_env_vars, rt_exit, rt_get_env, rt_path_probe, rt_platform_name,
    rt_process_execute, rt_process_run, rt_process_spawn, rt_set_env,
};

// Re-export runtime configuration FFI functions
pub use ffi::{rt_is_debug_mode_enabled, rt_is_macro_trace_enabled, rt_set_debug_mode, rt_set_macro_trace};

// Re-export file I/O FFI functions
pub use ffi::{
    // Metadata
    rt_file_exists,
    rt_file_stat,
    // File ops
    rt_file_canonicalize,
    rt_file_read_text,
    rt_file_write_text,
    rt_file_copy,
    rt_file_remove,
    rt_file_rename,
    rt_file_read_lines,
    rt_file_append_text,
    rt_file_read_bytes,
    rt_file_write_bytes,
    rt_file_move,
    // Directory ops
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
    // Descriptor ops
    rt_file_open,
    rt_file_get_size,
    rt_file_close,
    // Path ops
    rt_path_basename,
    rt_path_dirname,
    rt_path_ext,
    rt_path_absolute,
    rt_path_separator,
    rt_path_stem,
    rt_path_relative,
    rt_path_join,
};

// Re-export atomic operations FFI functions
pub use ffi::{
    rt_atomic_bool_free, rt_atomic_bool_load, rt_atomic_bool_new, rt_atomic_bool_store, rt_atomic_bool_swap,
    rt_atomic_flag_clear, rt_atomic_flag_free, rt_atomic_flag_new, rt_atomic_flag_test_and_set,
    rt_atomic_int_compare_exchange, rt_atomic_int_fetch_add, rt_atomic_int_fetch_and, rt_atomic_int_fetch_or,
    rt_atomic_int_fetch_sub, rt_atomic_int_fetch_xor, rt_atomic_int_free, rt_atomic_int_load, rt_atomic_int_new,
    rt_atomic_int_store, rt_atomic_int_swap,
};

// Re-export doctest I/O FFI functions
pub use doctest_io::{
    doctest_is_dir, doctest_is_file, doctest_path_contains, doctest_path_exists, doctest_path_has_extension,
    doctest_read_file, doctest_walk_directory,
};

// Re-export contract violation types and FFI functions (CTR-050-054)
pub use contracts::{
    rt_contract_violation_free, rt_contract_violation_func_name, rt_contract_violation_kind,
    rt_contract_violation_message, rt_contract_violation_new, rt_is_contract_violation, ContractViolationKind,
    RuntimeContractViolation,
};

// Re-export GPU runtime FFI functions
pub use gpu::{
    execute_kernel_1d,
    execute_kernel_3d,
    get_work_item_state,
    // Atomic operations (i64)
    rt_gpu_atomic_add_i64,
    // Atomic operations (u32)
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
    // Synchronization
    rt_gpu_barrier,
    // Work item identification
    rt_gpu_global_id,
    rt_gpu_global_size,
    rt_gpu_group_id,
    // Kernel launch
    rt_gpu_launch,
    rt_gpu_launch_1d,
    rt_gpu_local_id,
    rt_gpu_local_size,
    rt_gpu_mem_fence,
    rt_gpu_num_groups,
    // Shared memory
    rt_gpu_shared_alloc,
    rt_gpu_shared_reset,
    set_work_item_state,
    GpuKernelFn,
    // Types and utilities
    GpuWorkItemState,
};

// Re-export Vulkan GPU FFI functions
#[cfg(feature = "vulkan")]
pub use gpu_vulkan::{
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
    // Graphics pipeline management
    rt_vk_framebuffer_create,
    rt_vk_framebuffer_create_for_swapchain,
    rt_vk_framebuffer_free,
    rt_vk_framebuffer_get_dimensions,
    rt_vk_graphics_pipeline_create,
    rt_vk_graphics_pipeline_free,
    rt_vk_render_pass_create_simple,
    rt_vk_render_pass_create_with_depth,
    rt_vk_render_pass_free,
    rt_vk_render_pass_get_color_format,
    rt_vk_shader_module_create,
    rt_vk_shader_module_free,
    // Image management
    rt_vk_image_create_2d,
    rt_vk_image_download,
    rt_vk_image_free,
    rt_vk_image_get_view,
    rt_vk_image_upload,
    rt_vk_sampler_create,
    rt_vk_sampler_free,
    // Command buffer management
    rt_vk_cmd_begin_render_pass,
    rt_vk_cmd_bind_index_buffer,
    rt_vk_cmd_bind_pipeline,
    rt_vk_cmd_bind_vertex_buffer,
    rt_vk_cmd_draw,
    rt_vk_cmd_draw_indexed,
    rt_vk_cmd_end_render_pass,
    rt_vk_cmd_set_scissor,
    rt_vk_cmd_set_viewport,
    rt_vk_command_buffer_begin,
    rt_vk_command_buffer_end,
    rt_vk_command_buffer_free,
    rt_vk_command_buffer_submit,
    // Error codes
    VulkanFfiError,
};

// Re-export PyTorch tensor FFI functions
#[cfg(feature = "pytorch")]
pub use torch::{
    rt_torch_adam_new,
    rt_torch_adamw_new,
    rt_torch_adaptive_avg_pool2d,
    rt_torch_adaptive_max_pool2d,
    // Element-wise binary operations
    rt_torch_add,
    // Scalar operations
    rt_torch_add_scalar,
    rt_torch_arange,
    rt_torch_argmax,
    rt_torch_argmin,
    // Availability
    rt_torch_available,
    rt_torch_avg_pool2d,
    // Autograd - backward pass
    rt_torch_backward,
    rt_torch_batchnorm2d_forward,
    rt_torch_batchnorm2d_get_running_mean,
    rt_torch_batchnorm2d_get_running_var,
    // Neural Network Modules - BatchNorm
    rt_torch_batchnorm2d_new,
    rt_torch_bmm,
    rt_torch_cat,
    rt_torch_clone,
    rt_torch_conv2d_forward,
    // Neural Network Modules - Conv2d
    rt_torch_conv2d_new,
    // Data access
    rt_torch_copy_data_to_cpu,
    rt_torch_cross_entropy,
    rt_torch_cuda_available,
    rt_torch_cuda_device_count,
    rt_torch_cuda_memory_allocated,
    rt_torch_cuda_reset_peak_memory_stats,
    // Memory management
    rt_torch_cuda_synchronize,
    rt_torch_dataloader_free,
    // Data Loading - DataLoader
    rt_torch_dataloader_new,
    rt_torch_dataloader_next,
    rt_torch_dataloader_reset,
    rt_torch_dataset_free,
    rt_torch_dataset_get,
    rt_torch_dataset_len,
    rt_torch_detach,
    rt_torch_device,
    rt_torch_div,
    rt_torch_div_scalar,
    rt_torch_dropout,
    rt_torch_dropout_forward,
    // Neural Network Modules - Dropout
    rt_torch_dropout_new,
    rt_torch_dtype,
    rt_torch_elu,
    rt_torch_embedding_forward,
    rt_torch_embedding_from_pretrained,
    rt_torch_embedding_get_weight,
    // Neural Network Modules - Embedding
    rt_torch_embedding_new,
    // Comparison operations
    rt_torch_eq,
    rt_torch_exp,
    // Memory management
    rt_torch_free,
    rt_torch_ge,
    // Neural Network - advanced activations
    rt_torch_gelu,
    // Neural Network Modules - Global & Adaptive Pooling
    rt_torch_global_avg_pool2d,
    rt_torch_global_max_pool2d,
    // Autograd - gradient access
    rt_torch_grad,
    rt_torch_gru_forward,
    rt_torch_gru_new,
    rt_torch_gt,
    rt_torch_is_grad_enabled,
    rt_torch_is_leaf,
    rt_torch_item,
    rt_torch_kaiming_uniform_,
    // Neural Network - normalization & dropout
    rt_torch_layer_norm,
    rt_torch_layernorm_forward,
    rt_torch_layernorm_get_bias,
    rt_torch_layernorm_get_weight,
    // Neural Network Modules - LayerNorm
    rt_torch_layernorm_new,
    rt_torch_le,
    rt_torch_leaky_relu,
    rt_torch_linear_forward,
    rt_torch_linear_get_bias,
    rt_torch_linear_get_weight,
    // Neural Network Modules - Linear
    rt_torch_linear_new,
    rt_torch_log,
    rt_torch_log_softmax,
    rt_torch_lstm_forward,
    // Neural Network Modules - RNN (LSTM, GRU)
    rt_torch_lstm_new,
    rt_torch_lt,
    // Matrix operations
    rt_torch_matmul,
    // Reduction operations
    rt_torch_max,
    // Neural Network Modules - Pooling
    rt_torch_max_pool2d,
    rt_torch_mean,
    rt_torch_min,
    rt_torch_mish,
    // Neural Network Modules - Management
    rt_torch_module_free,
    // Neural Network - loss functions
    rt_torch_mse_loss,
    rt_torch_mul,
    rt_torch_mul_scalar,
    rt_torch_ne,
    rt_torch_nll_loss,
    // Neural Network - initialization
    rt_torch_normal_,
    rt_torch_numel,
    rt_torch_ones,
    rt_torch_optimizer_free,
    rt_torch_optimizer_get_lr,
    rt_torch_optimizer_set_lr,
    // Optimizers - operations
    rt_torch_optimizer_step,
    rt_torch_optimizer_zero_grad,
    rt_torch_permute,
    // Unary operations
    rt_torch_pow,
    rt_torch_randn,
    // Activation functions
    rt_torch_relu,
    rt_torch_requires_grad,
    // Shape operations
    rt_torch_reshape,
    rt_torch_retain_grad,
    rt_torch_scheduler_cosine_new,
    rt_torch_scheduler_exponential_new,
    rt_torch_scheduler_free,
    rt_torch_scheduler_plateau_new,
    // Learning Rate Schedulers - Operations
    rt_torch_scheduler_step,
    // Learning Rate Schedulers - Creation
    rt_torch_scheduler_step_new,
    rt_torch_scheduler_step_with_metric,
    // Autograd - advanced
    rt_torch_set_grad_enabled,
    // Autograd - gradient tracking
    rt_torch_set_requires_grad,
    // Optimizers - creation
    rt_torch_sgd_new,
    rt_torch_shallow_clone,
    // Metadata
    rt_torch_shape,
    rt_torch_sigmoid,
    rt_torch_silu,
    rt_torch_slice,
    rt_torch_softmax,
    rt_torch_softplus,
    rt_torch_sqrt,
    rt_torch_squeeze,
    rt_torch_stack,
    rt_torch_sub,
    rt_torch_sub_scalar,
    rt_torch_sum,
    rt_torch_tanh,
    // Data Loading - Dataset
    rt_torch_tensor_dataset_new,
    rt_torch_to_cpu,
    rt_torch_to_cuda,
    // Device operations
    rt_torch_to_device,
    rt_torch_transpose,
    rt_torch_uniform_,
    rt_torch_unsqueeze,
    rt_torch_xavier_uniform_,
    rt_torch_zero_grad,
    // Tensor creation
    rt_torch_zeros,
    // Error codes
    TorchFfiError,
};

// Re-export Ratatui TUI FFI functions
#[cfg(feature = "ratatui-tui")]
pub use ratatui_tui::{
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

// Re-export networking FFI functions
pub use net::{
    native_http_response_free,
    // HTTP functions
    native_http_send,
    native_tcp_accept,
    // TCP functions
    native_tcp_bind,
    native_tcp_close,
    native_tcp_connect,
    native_tcp_connect_timeout,
    native_tcp_flush,
    native_tcp_get_nodelay,
    native_tcp_peek,
    native_tcp_read,
    native_tcp_set_backlog,
    native_tcp_set_keepalive,
    native_tcp_set_nodelay,
    native_tcp_set_read_timeout,
    native_tcp_set_write_timeout,
    native_tcp_shutdown,
    native_tcp_write,
    // UDP functions
    native_udp_bind,
    native_udp_close,
    native_udp_connect,
    native_udp_get_broadcast,
    native_udp_get_ttl,
    native_udp_join_multicast_v4,
    native_udp_join_multicast_v6,
    native_udp_leave_multicast_v4,
    native_udp_leave_multicast_v6,
    native_udp_peek,
    native_udp_peek_from,
    native_udp_peer_addr,
    native_udp_recv,
    native_udp_recv_from,
    native_udp_send,
    native_udp_send_to,
    native_udp_set_broadcast,
    native_udp_set_multicast_loop,
    native_udp_set_multicast_ttl,
    native_udp_set_read_timeout,
    native_udp_set_ttl,
    native_udp_set_write_timeout,
    // Error types
    NetError,
};

// Re-export file I/O FFI functions - Mold-inspired optimizations
pub use file_io::{
    async_yield,
    // Async file loading (#1765-#1769)
    native_async_file_create,
    native_async_file_get_state,
    native_async_file_is_ready,
    native_async_file_start_loading,
    native_async_file_wait,
    native_copy_file_range,
    native_fadvise_dontneed,
    native_fadvise_random,
    // File I/O hints
    native_fadvise_sequential,
    native_fadvise_willneed,
    native_file_close,
    native_file_flush,
    native_file_read,
    native_file_seek,
    native_file_sync,
    native_file_write,
    // Standard file operations
    native_fs_open,
    // Memory-mapped file operations
    native_mmap_create,
    native_mmap_create_shared,
    native_mmap_read,
    native_mmap_unmap,
    // Path resolution and async primitives
    native_path_resolve,
    native_process_is_alive,
    native_process_kill,
    native_process_wait,
    // Zero-copy operations
    native_sendfile,
    // Process management with staging
    native_spawn_worker,
    sys_close,
    sys_file_exists,
    sys_file_size,
    sys_madvise,
    // Low-level system calls
    sys_mmap,
    sys_munmap,
    sys_open,
};

// Re-export SIMD vector operations
pub use simd::{
    rt_vec_abs, rt_vec_all, rt_vec_any, rt_vec_blend, rt_vec_ceil, rt_vec_extract, rt_vec_floor, rt_vec_max,
    rt_vec_min, rt_vec_product, rt_vec_round, rt_vec_select, rt_vec_shuffle, rt_vec_sqrt, rt_vec_sum, rt_vec_with,
};

// Re-export regex FFI functions
pub use ffi::regex::{
    ffi_regex_captures, ffi_regex_find, ffi_regex_find_all, ffi_regex_is_match, ffi_regex_replace,
    ffi_regex_replace_all, ffi_regex_split, ffi_regex_split_n,
};

// Re-export sandbox FFI functions
pub use ffi::sandbox::{
    rt_sandbox_add_allowed_domain, rt_sandbox_add_blocked_domain, rt_sandbox_add_read_path, rt_sandbox_add_write_path,
    rt_sandbox_apply, rt_sandbox_cleanup, rt_sandbox_disable_network, rt_sandbox_get_cpu_time, rt_sandbox_get_fs_mode,
    rt_sandbox_get_memory, rt_sandbox_get_network_mode, rt_sandbox_is_configured, rt_sandbox_reset,
    rt_sandbox_set_cpu_time, rt_sandbox_set_fd_limit, rt_sandbox_set_fs_overlay, rt_sandbox_set_fs_readonly,
    rt_sandbox_set_fs_restricted, rt_sandbox_set_memory, rt_sandbox_set_network_allowlist,
    rt_sandbox_set_network_blocklist, rt_sandbox_set_thread_limit,
};

// Re-export diagram FFI functions (for spec framework)
pub use diagram_ffi::{
    rt_diagram_clear, rt_diagram_disable, rt_diagram_enable, rt_diagram_free_string, rt_diagram_generate_arch,
    rt_diagram_generate_class, rt_diagram_generate_sequence, rt_diagram_is_enabled, rt_diagram_mark_architectural,
    rt_diagram_trace_method, rt_diagram_trace_method_with_args, rt_diagram_trace_return,
};

// Re-export screenshot FFI functions (for spec framework)
pub use screenshot_ffi::{
    rt_screenshot_capture_after_terminal, rt_screenshot_capture_before_terminal, rt_screenshot_capture_count,
    rt_screenshot_clear_captures, rt_screenshot_clear_context, rt_screenshot_disable, rt_screenshot_enable,
    rt_screenshot_exists, rt_screenshot_free_string, rt_screenshot_get_output_dir, rt_screenshot_get_path,
    rt_screenshot_is_enabled, rt_screenshot_is_refresh, rt_screenshot_set_context, rt_screenshot_set_output_dir,
    rt_screenshot_set_refresh,
};
pub use screenshot_ffi::{CaptureType, ImageFormat};

// Re-export MonoioFuture types and FFI functions
#[cfg(feature = "monoio-direct")]
pub use monoio_future::{
    rt_monoio_future_free, rt_monoio_future_get_async_state, rt_monoio_future_get_ctx, rt_monoio_future_get_io_handle,
    rt_monoio_future_get_operation_type, rt_monoio_future_get_result, rt_monoio_future_get_state,
    rt_monoio_future_is_pending, rt_monoio_future_is_ready, rt_monoio_future_new, rt_monoio_future_set_async_state,
    rt_monoio_future_set_error, rt_monoio_future_set_result, rt_monoio_is_pending, IoOperationType, MonoioFuture,
    FUTURE_STATE_ERROR, FUTURE_STATE_PENDING, FUTURE_STATE_READY, PENDING_MARKER,
};

// ============================================================================
// Registry Cleanup Functions (for test isolation)
// ============================================================================

// Re-export individual registry clear functions
pub use hpcollections::hashmap::clear_hashmap_registry;
pub use hpcollections::hashset::clear_hashset_registry;
pub use hpcollections::btreemap::clear_btreemap_registry;
pub use hpcollections::btreeset::clear_btreeset_registry;
pub use ffi::regex::clear_regex_cache;
pub use ffi::sync::clear_sync_registries;
pub use ffi::atomic::clear_atomic_registries;
pub use ffi::hash::clear_hash_registries;
pub use ffi::concurrent::clear_concurrent_registries;
pub use net::clear_socket_registry;

/// Clear all runtime registries to prevent memory leaks between test runs.
/// This should be called before each test to ensure clean state.
pub fn clear_all_runtime_registries() {
    // Clear HP collections registries
    clear_hashmap_registry();
    clear_hashset_registry();
    clear_btreemap_registry();
    clear_btreeset_registry();

    // Clear regex cache
    clear_regex_cache();

    // Clear sync registries (condvar, thread-local)
    clear_sync_registries();

    // Clear atomic registries
    clear_atomic_registries();

    // Clear hash registries (sha1, sha256, xxhash)
    clear_hash_registries();

    // Clear concurrent data structure registries (arena, map, pool, queue, stack, tls)
    clear_concurrent_registries();

    // Clear socket registry (TCP, UDP)
    clear_socket_registry();

    // Clear actor registry
    actors::clear_actor_registry();

    // Clear memory-mapped file registry
    file_io::clear_mmap_registry();

    // Clear FFI type registry
    rt_ffi_clear_registry();

    // Clear ratatui registry (if enabled)
    #[cfg(feature = "ratatui-tui")]
    ratatui_tui::clear_ratatui_registry();

    // Clear diagram state
    diagram_ffi::clear_diagram_data();

    // Clear screenshot captures
    screenshot_ffi::rt_screenshot_clear_captures();

    // Clear log state
    log_ffi::clear_log_state();
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
#[path = "mod_tests.rs"]
mod tests;
