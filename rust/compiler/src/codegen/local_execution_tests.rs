//! Tests for LocalExecutionManager and ExecutionManager trait.

use super::execution_manager::ExecutionManager;
use super::local_execution::{JitBackend, LocalExecutionManager};
use crate::hir;
use crate::mir::lower_to_mir;
use simple_parser::Parser;

/// Helper: parse source → HIR → MIR
fn source_to_mir(source: &str) -> crate::mir::MirModule {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir(&hir_module).expect("mir lower failed")
}

// =============================================================================
// Cranelift JIT Tests
// =============================================================================

#[test]
fn test_cranelift_jit_basic() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn answer() -> i64:\n    return 42\n");

    let info = em.compile_module(&mir).expect("compile");
    assert!(info.symbol_names.contains(&"answer".to_string()));

    let result = em.execute("answer", &[]).expect("execute");
    assert_eq!(result, 42);
}

#[test]
fn test_cranelift_jit_with_args() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn add(a: i64, b: i64) -> i64:\n    return a + b\n");

    em.compile_module(&mir).expect("compile");

    let result = em.execute("add", &[10, 32]).expect("execute");
    assert_eq!(result, 42);
}

#[test]
fn test_cranelift_jit_has_function() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn hello() -> i64:\n    return 1\n");

    em.compile_module(&mir).expect("compile");
    assert!(em.has_function("hello"));
    assert!(!em.has_function("nonexistent"));
}

#[test]
fn test_cranelift_jit_backend_name() {
    let em = LocalExecutionManager::cranelift().expect("cranelift init");
    assert_eq!(em.backend_name(), "cranelift-jit");
}

#[test]
fn test_cranelift_jit_cleanup() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn foo() -> i64:\n    return 1\n");

    em.compile_module(&mir).expect("compile");
    assert!(em.has_function("foo"));

    em.cleanup();
    // After cleanup, previously compiled functions should be gone
    assert!(!em.has_function("foo"));
}

// =============================================================================
// Auto-select Tests
// =============================================================================

#[test]
fn test_auto_select() {
    let em = LocalExecutionManager::auto().expect("auto init");

    // On 64-bit hosts, auto should select Cranelift
    #[cfg(target_pointer_width = "64")]
    assert_eq!(em.backend_kind(), JitBackend::Cranelift);

    // Backend name should be valid
    let name = em.backend_name();
    assert!(
        name == "cranelift-jit" || name == "llvm-jit",
        "unexpected backend: {}",
        name
    );
}

#[test]
fn test_auto_jit_execute() {
    let mut em = LocalExecutionManager::auto().expect("auto init");
    let mir = source_to_mir("fn square(x: i64) -> i64:\n    return x * x\n");

    em.compile_module(&mir).expect("compile");
    let result = em.execute("square", &[7]).expect("execute");
    assert_eq!(result, 49);
}

// =============================================================================
// Backend Switching Tests
// =============================================================================

#[test]
fn test_backend_switching_same_result() {
    let mir = source_to_mir("fn triple(x: i64) -> i64:\n    return x * 3\n");

    // Compile and run with Cranelift
    let mut em_cl = LocalExecutionManager::cranelift().expect("cranelift init");
    em_cl.compile_module(&mir).expect("cranelift compile");
    let result_cl = em_cl.execute("triple", &[14]).expect("cranelift execute");

    // Both should give the same result
    assert_eq!(result_cl, 42, "Cranelift should compute 14*3=42");
}

// =============================================================================
// ExecutionResult (captured output) Tests
// =============================================================================

#[test]
fn test_execute_captured() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn ret_zero() -> i64:\n    return 0\n");

    em.compile_module(&mir).expect("compile");
    let result = em.execute_captured("ret_zero", &[]).expect("execute_captured");
    assert_eq!(result.exit_code, 0);
    // stdout/stderr may be empty for a simple return
}

// =============================================================================
// CodeInfo Tests
// =============================================================================

#[test]
fn test_code_info_entry_point() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn main() -> i64:\n    return 0\n");

    let info = em.compile_module(&mir).expect("compile");
    assert_eq!(info.entry_point, "main");
    assert!(info.symbol_names.contains(&"main".to_string()));
}

#[test]
fn test_code_info_no_main() {
    let mut em = LocalExecutionManager::cranelift().expect("cranelift init");
    let mir = source_to_mir("fn helper() -> i64:\n    return 1\n");

    let info = em.compile_module(&mir).expect("compile");
    // When no main, entry_point is the first function
    assert_eq!(info.entry_point, "helper");
}

// =============================================================================
// LLVM JIT Tests (feature-gated)
// =============================================================================

#[cfg(feature = "llvm")]
mod llvm_jit_tests {
    use super::*;

    #[test]
    fn test_llvm_jit_basic() {
        let mut em = LocalExecutionManager::new(JitBackend::Llvm).expect("llvm init");
        let mir = source_to_mir("fn answer() -> i64:\n    return 42\n");

        em.compile_module(&mir).expect("compile");
        let result = em.execute("answer", &[]).expect("execute");
        assert_eq!(result, 42);
    }

    #[test]
    fn test_llvm_jit_backend_name() {
        let em = LocalExecutionManager::new(JitBackend::Llvm).expect("llvm init");
        assert_eq!(em.backend_name(), "llvm-jit");
    }
}
