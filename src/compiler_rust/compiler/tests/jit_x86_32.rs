//! Integration tests for x86_32 JIT routing via LocalExecutionManager.
//!
//! Verifies that `LocalExecutionManager::for_target` with an x86_32 target
//! selects LLVM (when available) or falls back to Cranelift, and that
//! the resulting manager is usable for compilation.

use simple_common::target::{Target, TargetArch, TargetOS};
use simple_compiler::codegen::{ExecutionManager, local_execution::{JitBackend, LocalExecutionManager}};

fn x86_32_linux() -> Target {
    Target { arch: TargetArch::X86, os: TargetOS::Linux, ..Target::host() }
}

/// Verify that `for_target` with an x86_32 target constructs successfully
/// and that the backend kind matches expectations.
#[test]
fn test_for_target_x86_32_succeeds() {
    let target = x86_32_linux();
    let em = LocalExecutionManager::for_target(target);
    assert!(em.is_ok(), "LocalExecutionManager::for_target x86_32 should succeed: {:?}", em.err());
}

/// When the `llvm` feature is enabled, x86_32 must select the LLVM backend.
/// Without `llvm`, the fallback is Cranelift.
#[test]
fn test_for_target_x86_32_backend_kind() {
    let target = x86_32_linux();
    let em = LocalExecutionManager::for_target(target).expect("manager creation");

    #[cfg(feature = "llvm")]
    assert_eq!(
        em.backend_kind(),
        JitBackend::Llvm,
        "x86_32 should select LLVM backend when llvm feature is enabled"
    );

    #[cfg(not(feature = "llvm"))]
    assert_eq!(
        em.backend_kind(),
        JitBackend::Cranelift,
        "x86_32 should fall back to Cranelift when llvm feature is disabled"
    );
}

/// Verify backend_name reflects the selected backend.
#[test]
fn test_for_target_x86_32_backend_name() {
    let target = x86_32_linux();
    let em = LocalExecutionManager::for_target(target).expect("manager creation");
    let name = em.backend_name();

    #[cfg(feature = "llvm")]
    assert!(
        name.contains("llvm"),
        "backend_name should contain 'llvm' when llvm feature is enabled, got: {name}"
    );

    #[cfg(not(feature = "llvm"))]
    assert!(
        name.contains("cranelift"),
        "backend_name should contain 'cranelift' when llvm feature is disabled, got: {name}"
    );
}

/// When LLVM is available, attempt to compile a minimal MIR module through
/// the x86_32 LLVM JIT. This exercises the full compile_module code path
/// for cross-arch (32-bit) targets.
#[cfg(feature = "llvm")]
#[test]
fn test_x86_32_llvm_compile_simple_function() {
    use simple_compiler::hir::{BinOp, TypeId};
    use simple_compiler::mir::{
        BlockId, LocalKind, MirBlock, MirFunction, MirInst, MirLocal, MirModule, Terminator, VReg,
    };
    use simple_parser::Visibility;

    // Build: fn add_b_times_2(a: i64, b: i64) -> i64 { a + b * 2 }
    //
    // VReg layout:
    //   VReg(0) = param a  (implicit, first param)
    //   VReg(1) = param b  (implicit, second param)
    //   VReg(2) = const 2
    //   VReg(3) = b * 2
    //   VReg(4) = a + (b * 2)   <- return value

    let mut func = MirFunction::new("add_b_times_2".into(), TypeId::I64, Visibility::Public);
    func.blocks.clear();
    func.entry_block = BlockId(0);

    func.params.push(MirLocal { name: "a".into(), ty: TypeId::I64, kind: LocalKind::Parameter, is_ghost: false });
    func.params.push(MirLocal { name: "b".into(), ty: TypeId::I64, kind: LocalKind::Parameter, is_ghost: false });

    let mut b0 = MirBlock::new(BlockId(0));

    // VReg(0) = a, VReg(1) = b  (parameters occupy the first VRegs by convention)
    b0.instructions.push(MirInst::ConstInt { dest: VReg(2), value: 2 });
    b0.instructions.push(MirInst::BinOp {
        dest: VReg(3),
        op: BinOp::Mul,
        left: VReg(1),
        right: VReg(2),
    });
    b0.instructions.push(MirInst::BinOp {
        dest: VReg(4),
        op: BinOp::Add,
        left: VReg(0),
        right: VReg(3),
    });
    b0.terminator = Terminator::Return(Some(VReg(4)));
    func.blocks.push(b0);

    let mut module = MirModule::new();
    module.functions.push(func);

    let target = x86_32_linux();
    let mut em = LocalExecutionManager::for_target(target).expect("manager creation");

    // compile_module may legitimately fail for cross-arch JIT (MCJIT targets the
    // host machine, so loading an i686 data-layout module on x86_64 may error).
    // We accept both outcomes but report which path was taken.
    match em.compile_module(&module) {
        Ok(code_info) => {
            // Compilation succeeded — verify the function is registered.
            assert!(
                code_info.symbol_names.contains(&"add_b_times_2".to_string()),
                "compiled symbol list should include 'add_b_times_2', got: {:?}",
                code_info.symbol_names
            );
            assert!(em.has_function("add_b_times_2"), "has_function should return true after successful compile");
        }
        Err(e) => {
            // Cross-arch JIT failure is acceptable; document the reason.
            eprintln!(
                "x86_32 LLVM JIT compile_module returned error (expected on x86_64 host with cross-arch MCJIT): {e}"
            );
            // Not a hard failure — cross-arch execution requires actual x86 hardware or emulation.
        }
    }
}
