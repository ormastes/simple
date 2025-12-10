pub mod concurrency;
pub mod memory;
pub mod value;

// Preserve the public `gc` module path for callers.
pub use memory::gc;
pub use memory::no_gc::NoGcAllocator;

// Re-export runtime value types for codegen
pub use value::{
    HeapHeader, HeapObjectType, RuntimeArray, RuntimeClosure, RuntimeEnum, RuntimeObject,
    RuntimeString, RuntimeTuple, RuntimeValue,
};

// Re-export runtime FFI functions for codegen
pub use value::{
    rt_actor_recv,
    rt_actor_send,
    // Actor operations
    rt_actor_spawn,
    // Raw memory allocation (zero-cost struct support)
    rt_alloc,
    rt_array_get,
    rt_array_len,
    // Array operations
    rt_array_new,
    rt_array_pop,
    rt_array_push,
    rt_array_set,
    rt_closure_func_ptr,
    rt_closure_get_capture,
    // Closure operations
    rt_closure_new,
    rt_closure_set_capture,
    rt_dict_get,
    rt_dict_len,
    // Dict operations
    rt_dict_new,
    rt_dict_set,
    rt_enum_discriminant,
    // Enum operations
    rt_enum_new,
    rt_enum_payload,
    rt_free,
    rt_future_await,
    rt_future_new,
    rt_generator_new,
    rt_generator_next,
    rt_generator_yield,
    // Generic collection operations
    rt_index_get,
    rt_index_set,
    rt_object_class_id,
    rt_object_field_count,
    rt_object_field_get,
    rt_object_field_set,
    // Object operations
    rt_object_new,
    rt_ptr_to_value,
    rt_slice,
    rt_string_concat,
    rt_string_data,
    rt_string_len,
    // String operations
    rt_string_new,
    rt_tuple_get,
    rt_tuple_len,
    // Tuple operations
    rt_tuple_new,
    rt_tuple_set,
    rt_value_as_bool,
    rt_value_as_float,
    // Value extraction
    rt_value_as_int,
    rt_value_bool,
    rt_value_float,
    // Value creation
    rt_value_int,
    rt_value_is_bool,
    rt_value_is_float,
    rt_value_is_heap,
    rt_value_is_int,
    // Value type checking
    rt_value_is_nil,
    rt_value_nil,
    rt_value_to_ptr,
    rt_value_truthy,
    // Future/generator operations
    rt_wait,
};

// Re-export RuntimeDict struct
pub use value::RuntimeDict;
