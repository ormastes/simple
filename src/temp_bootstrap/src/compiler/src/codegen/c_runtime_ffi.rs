//! Generate C extern declarations from the shared RUNTIME_FUNCS spec.
//!
//! Reads the same `RuntimeFuncSpec` array used by Cranelift/LLVM backends
//! and emits matching C `extern` function declarations.

use cranelift_codegen::ir::types;

use super::runtime_ffi::RUNTIME_FUNCS;

/// Map a Cranelift IR type to its C type string.
///
/// All integer types (I8, I16, I32, I64) map to int64_t because the runtime
/// uses int64_t-width parameters uniformly for ABI simplicity.
fn cranelift_type_to_c(ty: types::Type) -> &'static str {
    if ty == types::F32 {
        "float"
    } else if ty == types::F64 {
        "double"
    } else {
        "int64_t" // I8, I16, I32, I64, and all other types
    }
}

/// Generate C `extern` declarations for all runtime FFI functions.
///
/// Returns a string like:
/// ```c
/// extern int64_t rt_array_new(int64_t);
/// extern void rt_print_str(int64_t, int64_t);
/// ```
pub fn generate_runtime_declarations() -> String {
    let mut out = String::new();
    out.push_str("/* Runtime FFI declarations (auto-generated from RUNTIME_FUNCS) */\n");

    for spec in RUNTIME_FUNCS {
        out.push_str("extern ");

        // Return type
        if spec.returns.is_empty() {
            out.push_str("void");
        } else {
            out.push_str(cranelift_type_to_c(spec.returns[0]));
        }

        out.push(' ');
        out.push_str(spec.name);
        out.push('(');

        // Parameters
        if spec.params.is_empty() {
            out.push_str("void");
        } else {
            for (i, &param_ty) in spec.params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(cranelift_type_to_c(param_ty));
            }
        }

        out.push_str(");\n");
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_runtime_declarations_not_empty() {
        let decls = generate_runtime_declarations();
        assert!(!decls.is_empty());
        // Should contain known runtime functions
        assert!(decls.contains("rt_array_new"));
        assert!(decls.contains("rt_string_concat"));
        assert!(decls.contains("rt_object_new"));
        assert!(decls.contains("rt_print_value"));
    }

    #[test]
    fn test_void_return_functions() {
        let decls = generate_runtime_declarations();
        // rt_print_str returns void
        assert!(decls.contains("extern void rt_print_str("));
    }

    #[test]
    fn test_parameterless_functions() {
        let decls = generate_runtime_declarations();
        // rt_actor_recv takes no params
        assert!(decls.contains("extern int64_t rt_actor_recv(void)"));
    }

    #[test]
    fn test_cranelift_type_mapping() {
        assert_eq!(cranelift_type_to_c(types::I64), "int64_t");
        assert_eq!(cranelift_type_to_c(types::F64), "double");
        assert_eq!(cranelift_type_to_c(types::F32), "float");
    }
}
