//! Type mapping tests - LLVM type system and pointer width tests.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

/// Test LLVM type mapping for basic types
#[test]
#[cfg(feature = "llvm")]
fn test_llvm_type_mapping() {
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    // Test integer types map correctly
    assert_eq!(backend.map_type(&T::I32).unwrap(), LlvmType::I32);
    assert_eq!(backend.map_type(&T::I64).unwrap(), LlvmType::I64);
    assert_eq!(backend.map_type(&T::U32).unwrap(), LlvmType::I32);
    assert_eq!(backend.map_type(&T::U64).unwrap(), LlvmType::I64);

    // Test floating point types
    assert_eq!(backend.map_type(&T::F32).unwrap(), LlvmType::F32);
    assert_eq!(backend.map_type(&T::F64).unwrap(), LlvmType::F64);

    // Test bool
    assert_eq!(backend.map_type(&T::BOOL).unwrap(), LlvmType::I1);
}

/// Test pointer width consistency
#[test]
#[cfg(feature = "llvm")]
fn test_pointer_width_32bit() {
    let target = Target::new(TargetArch::X86, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();
    assert_eq!(backend.pointer_width(), 32);
}

/// RuntimeValue matches the C runtime's `uint64_t` even where pointers are
/// 32-bit on hosted targets and wasm32 (cross_compile_linker_matrix_2026-11-17 item (b): i686 Windows).
#[test]
#[cfg(feature = "llvm")]
fn test_runtime_value_is_i64_on_32bit_targets() {
    for triple in ["i686-pc-windows-gnu", "i686-unknown-linux-gnu", "wasm32-unknown-unknown"] {
        let target = Target::parse(triple).unwrap();
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 32, "{triple}");
        assert_eq!(backend.runtime_int_type().get_bit_width(), 64, "{triple}");
    }
}

/// Freestanding / bare-metal 32-bit targets (`x86_32`, `arm32`, `riscv32` on
/// `SimpleOS` / `None`) match their 32-bit `typedef int32_t RuntimeValue` /
/// `intptr_t` stubs and pure-Simple kernel value shims.
#[test]
#[cfg(feature = "llvm")]
fn test_runtime_value_is_i32_on_freestanding_32bit_targets() {
    for arch in [TargetArch::Riscv32, TargetArch::Arm, TargetArch::X86] {
        for os in [TargetOS::SimpleOS, TargetOS::None] {
            let target = Target::new(arch, os);
            let backend = LlvmBackend::new(target).unwrap();
            assert_eq!(backend.pointer_width(), 32, "{arch}-{os}");
            assert_eq!(backend.runtime_int_type().get_bit_width(), 32, "{arch}-{os}");
        }
    }
    for arch in [TargetArch::Riscv64, TargetArch::Aarch64, TargetArch::X86_64] {
        let target = Target::new(arch, TargetOS::SimpleOS);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.runtime_int_type().get_bit_width(), 64, "{arch}-simpleos");
    }
}

/// Test pointer width consistency for 64-bit
#[test]
#[cfg(feature = "llvm")]
fn test_pointer_width_64bit() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();
    assert_eq!(backend.pointer_width(), 64);
}
