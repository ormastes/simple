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
    RuntimeFuncSpec::new("rt_actor_spawn", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_actor_send", &[I64, I64], &[]),
    RuntimeFuncSpec::new("rt_actor_recv", &[], &[I64]),
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
    // Interpreter bridge FFI
    // =========================================================================
    RuntimeFuncSpec::new("rt_interp_call", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_interp_eval", &[I64], &[I64]),
    // =========================================================================
    // Error handling
    // =========================================================================
    RuntimeFuncSpec::new("rt_function_not_found", &[I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_method_not_found", &[I64, I64, I64, I64], &[I64]),
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
