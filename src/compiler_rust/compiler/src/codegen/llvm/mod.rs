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

/// Map resolved canonical text methods to their C-runtime providers.
///
/// This is intentionally narrower than the general built-in owner predicate:
/// aliases resolved through `use_map`/`import_map` must prove a text receiver
/// before a leaf such as `replace` can be rewritten.
pub(crate) fn resolved_text_runtime_method(func_name: &str) -> Option<&'static str> {
    let dotted = func_name.replace("_dot_", ".");
    let (owner, method) = dotted.rsplit_once('.')?;
    let canonical_string_core = owner == "lib__common__string_core__str";
    let unqualified_builtin =
        !owner.contains("__") && !owner.contains('.') && matches!(owner, "str" | "text" | "String" | "string");
    if !canonical_string_core && !unqualified_builtin {
        return None;
    }
    match method {
        "bytes" => Some("rt_string_bytes"),
        "replace" => Some("rt_string_replace"),
        "split" => Some("rt_string_split"),
        "starts_with" => Some("rt_string_starts_with"),
        "rfind" => Some("rt_string_rfind"),
        "substring" => Some("rt_slice"),
        "char_code_at" => Some("rt_string_char_code_at"),
        _ => None,
    }
}

/// A suffix-only match has no owner proof.  When MIR still carries an exact
/// STRING receiver, accept only a canonical built-in text owner; never let a
/// same-leaf user method become the callee.
pub(crate) fn string_receiver_suffix_candidate_is_builtin(candidate: &str) -> bool {
    candidate.starts_with("rt_")
        || (qualified_runtime_method_owner_is_builtin(candidate) && resolved_text_runtime_method(candidate).is_some())
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
    use super::{
        qualified_runtime_method_owner_is_builtin, resolved_text_runtime_method,
        string_receiver_suffix_candidate_is_builtin,
    };

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

    #[test]
    fn resolved_canonical_text_methods_keep_owner_proof() {
        let cases = [
            ("lib__common__string_core__str_dot_replace", "rt_string_replace"),
            ("lib__common__string_core__str_dot_split", "rt_string_split"),
            ("lib__common__string_core__str_dot_starts_with", "rt_string_starts_with"),
            ("lib__common__string_core__str_dot_rfind", "rt_string_rfind"),
            ("lib__common__string_core__str_dot_substring", "rt_slice"),
            (
                "lib__common__string_core__str_dot_char_code_at",
                "rt_string_char_code_at",
            ),
            ("lib__common__string_core__str_dot_bytes", "rt_string_bytes"),
        ];
        for (resolved, intrinsic) in cases {
            assert_eq!(resolved_text_runtime_method(resolved), Some(intrinsic));
        }
        for leaf in ["replace", "split", "starts_with", "rfind", "substring", "char_code_at"] {
            assert_eq!(
                resolved_text_runtime_method(&format!("UserText_dot_{leaf}")),
                None,
                "a custom unresolved `{leaf}` must not be redirected to a text runtime intrinsic"
            );
            assert_eq!(
                resolved_text_runtime_method(leaf),
                None,
                "a bare unresolved `{leaf}` has no receiver proof"
            );
        }
        assert_eq!(resolved_text_runtime_method("user__model__str_dot_replace"), None);
    }

    #[test]
    fn typed_string_suffix_match_rejects_unrelated_bytes_owner() {
        assert!(string_receiver_suffix_candidate_is_builtin(
            "lib__common__string_core__str_dot_bytes"
        ));
        assert!(string_receiver_suffix_candidate_is_builtin("rt_string_bytes"));
        assert!(!string_receiver_suffix_candidate_is_builtin("PointerSize.bytes"));
        assert!(!string_receiver_suffix_candidate_is_builtin("UserType.bytes"));
    }
}
