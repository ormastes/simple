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

/// Last-resort mapping from a call target that resolved to NOTHING onto the
/// C-runtime intrinsic that actually implements it.
///
/// Only for the terminal fall-through in `functions/calls.rs`, where every
/// resolution strategy has already failed and the alternative is to mint an
/// unmangled external (`@char_code_at`, `@substring`, `@rfind`, …) that either
/// fails the link or, worse, binds to absolute address 0 and segfaults when
/// called. See
/// `doc/08_tracking/bug/stage2_native_build_link_undefined_method_symbols_2026-08-09.md`.
///
/// This is deliberately NOT the general shim table and must never be used as
/// one: the guard added in 36673b6b6a3 stays in force on every path where a
/// real user symbol might still resolve. Here nothing can.
pub(crate) fn last_resort_runtime_method(func_name: &str) -> Option<&'static str> {
    let dotted = func_name.replace("_dot_", ".");
    let method = dotted.rsplit('.').next().unwrap_or(&dotted);
    match method {
        "starts_with" => Some("rt_string_starts_with"),
        "ends_with" => Some("rt_string_ends_with"),
        "substring" | "slice" => Some("rt_slice"),
        "rfind" | "last_index_of" => Some("rt_string_rfind"),
        "split" => Some("rt_string_split"),
        "replace" => Some("rt_string_replace"),
        "char_code_at" => Some("rt_string_char_code_at"),
        "char_at" => Some("rt_string_char_at"),
        "byte_at" => Some("rt_string_byte_at"),
        "concat" => Some("rt_string_concat"),
        "trim" => Some("rt_string_trim"),
        "trim_start" => Some("rt_string_trim_start"),
        "trim_end" => Some("rt_string_trim_end"),
        "to_upper" | "upper" => Some("rt_string_to_upper"),
        "to_lower" | "lower" => Some("rt_string_to_lower"),
        _ => None,
    }
}

/// Parameter count of a last-resort intrinsic, receiver included.
pub(crate) fn last_resort_runtime_arity(rt_name: &str) -> usize {
    match rt_name {
        "rt_slice" => 4,             // (collection, start, end, step)
        "rt_string_replace" => 3,    // (text, from, to)
        "rt_string_trim" | "rt_string_trim_start" | "rt_string_trim_end" => 1,
        "rt_string_to_upper" | "rt_string_to_lower" => 1,
        _ => 2,
    }
}

/// Default padding for a last-resort intrinsic argument the call site omitted.
/// Only `rt_slice` has non-zero defaults: an absent `end` means "to the end"
/// and an absent `step` means 1, matching the `rt_slice` handling in
/// `functions/calls.rs`.
pub(crate) fn last_resort_runtime_arg_default(rt_name: &str, index: usize) -> i64 {
    match (rt_name, index) {
        ("rt_slice", 2) => i64::MAX,
        ("rt_slice", 3) => 1,
        _ => 0,
    }
}

fn last_resort_diagnostics_enabled() -> bool {
    std::env::var("SIMPLE_LLVM_CALL_TARGET_DEBUG").is_ok_and(|v| v != "0")
}

/// Level-gated: a call target was rescued by an intrinsic at the last resort.
pub(crate) fn log_last_resort_intrinsic(func_name: &str, rt_name: &str) {
    if last_resort_diagnostics_enabled() {
        eprintln!("[llvm][call-target] `{func_name}` resolved to nothing; routed to intrinsic `{rt_name}`");
    }
}

/// Level-gated: a call target resolved to nothing and no intrinsic covers it,
/// so an unmangled external is being minted. That symbol WILL fail the link (or
/// bind to address 0). Naming it here is what makes the failure diagnosable.
pub(crate) fn log_unresolved_call_symbol(func_name: &str) {
    if last_resort_diagnostics_enabled() {
        eprintln!(
            "[llvm][call-target] `{func_name}` resolved to nothing and no intrinsic covers it; \
             emitting an UNMANGLED external — this will be an undefined reference at link time"
        );
    }
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
    let unqualified_builtin = !owner.contains("__")
        && !owner.contains('.')
        && matches!(owner, "str" | "text" | "String" | "string");
    if !canonical_string_core && !unqualified_builtin {
        return None;
    }
    match method {
        "replace" => Some("rt_string_replace"),
        "split" => Some("rt_string_split"),
        "starts_with" => Some("rt_string_starts_with"),
        "rfind" => Some("rt_string_rfind"),
        "substring" => Some("rt_slice"),
        "char_code_at" => Some("rt_string_char_code_at"),
        _ => None,
    }
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
    use super::{qualified_runtime_method_owner_is_builtin, resolved_text_runtime_method};

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

    /// Regression, both directions, for
    /// `doc/08_tracking/bug/stage2_native_build_link_undefined_method_symbols_2026-08-09.md`.
    ///
    /// Forward: the six `text` leaves that Stage 2 could not link must have a
    /// last-resort intrinsic, so the terminal fall-through routes them to a real
    /// implementation instead of minting `@starts_with` / `@substring` /
    /// `@rfind` / `@split` / `@replace` / `@char_code_at`.
    ///
    /// Backward: 36673b6b6a3's guard is untouched — an imported user method
    /// with a colliding leaf is still refused by the shortcut paths. The
    /// last-resort table is a strictly separate, terminal-only mechanism and
    /// must not cover generic leaves like `to_text`, `get`, or `len`, which
    /// real user types commonly define.
    #[test]
    fn stage2_undefined_text_leaves_have_a_last_resort_intrinsic() {
        for (leaf, expected) in [
            ("starts_with", "rt_string_starts_with"),
            ("substring", "rt_slice"),
            ("rfind", "rt_string_rfind"),
            ("split", "rt_string_split"),
            ("replace", "rt_string_replace"),
            ("char_code_at", "rt_string_char_code_at"),
        ] {
            assert_eq!(
                super::last_resort_runtime_method(leaf),
                Some(expected),
                "bare `{leaf}` must route to `{expected}`, not link as an unmangled external"
            );
            assert_eq!(
                super::last_resort_runtime_method(&format!("lib__common__text__{leaf}")),
                Some(expected),
                "module-mangled `{leaf}` must route the same way"
            );
        }
    }

    #[test]
    fn last_resort_table_does_not_swallow_user_method_leaves() {
        // Generic leaves that user types own must stay OUT of the last-resort
        // table, or a genuinely unresolved user call would be silently
        // miscompiled into a string intrinsic instead of failing loudly.
        for leaf in ["to_text", "get", "len", "is_terminal", "lock", "unlock", "push"] {
            assert_eq!(
                super::last_resort_runtime_method(leaf),
                None,
                "`{leaf}` must not be rescued by the last-resort table"
            );
        }

        // 36673b6b6a3's guard must still refuse user owners on the shortcut paths.
        assert!(!qualified_runtime_method_owner_is_builtin("DbValue.to_text"));
        assert!(!qualified_runtime_method_owner_is_builtin("TaskState.is_terminal"));
        assert!(qualified_runtime_method_owner_is_builtin("str.to_text"));
    }

    #[test]
    fn resolved_canonical_text_methods_keep_owner_proof() {
        let cases = [
            ("lib__common__string_core__str_dot_replace", "rt_string_replace"),
            ("lib__common__string_core__str_dot_split", "rt_string_split"),
            ("lib__common__string_core__str_dot_starts_with", "rt_string_starts_with"),
            ("lib__common__string_core__str_dot_rfind", "rt_string_rfind"),
            ("lib__common__string_core__str_dot_substring", "rt_slice"),
            ("lib__common__string_core__str_dot_char_code_at", "rt_string_char_code_at"),
        ];
        for (resolved, intrinsic) in cases {
            assert_eq!(resolved_text_runtime_method(resolved), Some(intrinsic));
        }
        assert_eq!(resolved_text_runtime_method("UserText_dot_replace"), None);
        assert_eq!(resolved_text_runtime_method("user__model__str_dot_replace"), None);
        assert_eq!(resolved_text_runtime_method("replace"), None);
    }
}
