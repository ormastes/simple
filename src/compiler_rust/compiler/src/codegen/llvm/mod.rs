/// LLVM backend for 32-bit and 64-bit target support
///
/// This backend complements Cranelift by providing:
/// - 32-bit architecture support (i686, armv7, riscv32)
/// - Alternative 64-bit backend option
/// - Shared MIR transforms and runtime SFFI specs
///
/// Requires the `llvm` feature flag and LLVM 18 toolchain to be enabled.
// Module structure
mod backend_core;
pub mod emitter;
mod functions;
mod gpu_instructions;
mod instructions;
mod types;
mod wasm_imports;

#[cfg(feature = "llvm-gpu")]
pub mod gpu;

// Re-export public types
pub use backend_core::LlvmBackend;
pub use types::{BinOp, LlvmType};
pub use wasm_imports::declare_wasi_imports;

/// Runtime method shims are valid only for built-in receiver owners.  Imported
/// user methods can share leaves such as `to_text`, `get`, or `len`; rewriting
/// those qualified calls by leaf alone silently changes their call target.
pub(crate) fn qualified_runtime_method_owner_is_builtin(func_name: &str) -> bool {
    let dotted = func_name.replace("_dot_", ".");
    let Some((owner, _method)) = dotted.rsplit_once('.') else {
        return false;
    };
    let owner = owner.rsplit("__").next().unwrap_or(owner);
    let owner = owner.rsplit('.').next().unwrap_or(owner);
    matches!(
        owner,
        "bool"
            | "Bool"
            | "u8"
            | "i8"
            | "u16"
            | "i16"
            | "u32"
            | "i32"
            | "u64"
            | "i64"
            | "Int"
            | "f32"
            | "f64"
            | "Float"
            | "char"
            | "Char"
            | "str"
            | "text"
            | "String"
            | "string"
            | "Array"
            | "array"
            | "Dict"
            | "dict"
            | "Map"
            | "map"
            | "Set"
            | "set"
            | "Tuple"
            | "tuple"
            | "Option"
            | "option"
            | "Result"
            | "result"
    )
}

#[cfg(feature = "llvm-gpu")]
pub use gpu::{GpuComputeCapability, LlvmGpuBackend};

// Test helper methods for LLVM backend.
#[cfg(feature = "llvm-tests")]
include!("../llvm_test_utils.rs");

// WASM compilation tests
#[cfg(test)]
mod wasm_tests;

#[cfg(test)]
mod qualified_runtime_method_tests {
    use super::qualified_runtime_method_owner_is_builtin;

    #[test]
    fn runtime_method_shortcuts_require_builtin_owners() {
        assert!(qualified_runtime_method_owner_is_builtin("str.to_text"));
        assert!(qualified_runtime_method_owner_is_builtin("Dict.get"));
        assert!(qualified_runtime_method_owner_is_builtin(
            "lib__common__string_core__str_dot_to_text"
        ));
        assert!(!qualified_runtime_method_owner_is_builtin("DbValue.to_text"));
        assert!(!qualified_runtime_method_owner_is_builtin(
            "lib__database__DbValue_dot_to_text"
        ));
        assert!(!qualified_runtime_method_owner_is_builtin("to_text"));
    }
}
