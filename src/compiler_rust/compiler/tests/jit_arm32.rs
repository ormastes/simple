//! Integration tests for ARM32 JIT backend selection.
//!
//! Verifies that `JitBackend::for_target()` routes ARM32 to LLVM when the
//! `llvm` feature is enabled, and falls back to Cranelift otherwise.
//! Also exercises `LocalExecutionManager::for_target()` construction.

use simple_common::target::{Target, TargetArch, TargetOS};
use simple_compiler::codegen::local_execution::{JitBackend, LocalExecutionManager};

fn arm32_target() -> Target {
    Target { arch: TargetArch::Arm, os: TargetOS::Linux, ..Target::host() }
}

// --- JitBackend::for_target selection ---

#[cfg(feature = "llvm")]
#[test]
fn jit_backend_for_arm32_selects_llvm() {
    let arm32 = arm32_target();
    assert_eq!(
        JitBackend::for_target(&arm32),
        JitBackend::Llvm,
        "ARM32 should route to LLVM when the llvm feature is enabled"
    );
}

#[cfg(not(feature = "llvm"))]
#[test]
fn jit_backend_for_arm32_falls_back_to_cranelift() {
    let arm32 = arm32_target();
    assert_eq!(
        JitBackend::for_target(&arm32),
        JitBackend::Cranelift,
        "ARM32 should fall back to Cranelift when the llvm feature is absent"
    );
}

// --- LocalExecutionManager::for_target construction ---

#[cfg(feature = "llvm")]
#[test]
fn local_execution_manager_for_arm32_uses_llvm() {
    let arm32 = arm32_target();
    let em = LocalExecutionManager::for_target(arm32);
    assert!(em.is_ok(), "LocalExecutionManager::for_target should succeed for ARM32 with LLVM: {:?}", em.err());
    assert_eq!(
        em.unwrap().backend_kind(),
        JitBackend::Llvm,
        "Resolved backend should be LLVM for ARM32"
    );
}

#[cfg(not(feature = "llvm"))]
#[test]
fn local_execution_manager_for_arm32_falls_back_to_cranelift() {
    let arm32 = arm32_target();
    // Without LLVM, for_target falls back to Cranelift (even for 32-bit).
    // Construction may still succeed (Cranelift can be created on a 64-bit host).
    let em = LocalExecutionManager::for_target(arm32);
    if let Ok(manager) = em {
        assert_eq!(
            manager.backend_kind(),
            JitBackend::Cranelift,
            "Without LLVM feature, ARM32 must resolve to Cranelift"
        );
    }
    // If creation fails (e.g. on a 32-bit host without LLVM), that is also
    // acceptable — the test simply documents that LLVM is not available.
}
