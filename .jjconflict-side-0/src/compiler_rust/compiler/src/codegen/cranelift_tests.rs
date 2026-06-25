//! Tests for AOT Cranelift compilation

use super::*;
use crate::hir;
use crate::mir::lower_to_mir;
use crate::optimizations::NativeOptimizationLevel;
use simple_common::target::{Target, TargetArch, TargetCpu, TargetOS};
use simple_parser::Parser;

fn compile_to_object(source: &str) -> CodegenResult<Vec<u8>> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    let mir_module = lower_to_mir(&hir_module).expect("mir lower failed");
    Codegen::new()?.compile_module(&mir_module)
}

#[test]
fn test_compile_simple_function() {
    let obj = compile_to_object("fn answer() -> i64:\n    return 42\n").unwrap();
    assert!(!obj.is_empty());
}

#[test]
fn test_compile_add_function() {
    let obj = compile_to_object("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();
    assert!(!obj.is_empty());
}

#[test]
fn test_compile_comparison() {
    let obj = compile_to_object("fn is_positive(x: i64) -> bool:\n    return x > 0\n").unwrap();
    assert!(!obj.is_empty());
}

#[test]
fn test_compile_if_else() {
    let obj = compile_to_object(
        "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n",
    )
    .unwrap();
    assert!(!obj.is_empty());
}

/// Test which architectures Cranelift actually supports.
/// With x86, arm64, riscv64 features enabled, all 64-bit targets compile from any host.
/// 32-bit targets remain unsupported (require LLVM backend).
#[test]
fn test_cranelift_target_support() {
    let targets = [
        ("x86_64", TargetArch::X86_64, true),    // Cross-arch enabled
        ("aarch64", TargetArch::Aarch64, true),  // Cross-arch enabled
        ("riscv64", TargetArch::Riscv64, true),  // Cross-arch enabled
        ("i686", TargetArch::X86, false),        // Expected: NOT supported
        ("armv7", TargetArch::Arm, false),       // Expected: NOT supported
        ("riscv32", TargetArch::Riscv32, false), // Expected: NOT supported
    ];

    for (name, arch, expected_support) in targets {
        let target = Target::new(arch, TargetOS::Linux);
        let result = Codegen::for_target(target);

        if expected_support {
            assert!(
                result.is_ok(),
                "{} should be supported but got: {:?}",
                name,
                result.err()
            );
            println!("{}: Supported", name);
        } else {
            // 32-bit targets are not supported by Cranelift
            assert!(result.is_err(), "{} should NOT be supported", name);
            println!("{}: Not supported (expected)", name);
        }
    }
}

#[test]
fn test_cranelift_x86_64_cpu_levels_are_accepted() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    for cpu in [
        TargetCpu::X86_64V1,
        TargetCpu::X86_64V2,
        TargetCpu::X86_64V3,
        TargetCpu::X86_64V4,
    ] {
        let result = Codegen::for_target_with_opt_level_and_cpu(target, NativeOptimizationLevel::Standard, cpu.clone());
        assert!(
            result.is_ok(),
            "expected {:?} to be accepted, got {:?}",
            cpu,
            result.err()
        );
    }
}

#[test]
fn test_cranelift_rejects_x86_64_cpu_levels_for_non_x86_64_targets() {
    let target = Target::new(TargetArch::Aarch64, TargetOS::Linux);
    let result =
        Codegen::for_target_with_opt_level_and_cpu(target, NativeOptimizationLevel::Standard, TargetCpu::X86_64V3);
    assert!(result.is_err());
    let message = format!("{:?}", result.err());
    assert!(message.contains("only applies to x86_64"));
}

#[test]
fn test_cranelift_rejects_scaffolded_32bit_hosted_targets() {
    for arch in [TargetArch::Arm, TargetArch::Riscv32] {
        let target = Target::new(arch, TargetOS::Linux);
        let result =
            Codegen::for_target_with_opt_level_and_cpu(target, NativeOptimizationLevel::Standard, TargetCpu::Default);
        assert!(result.is_err(), "expected {:?} hosted target to be rejected", arch);
        let message = format!("{:?}", result.err());
        assert!(message.contains("use --backend llvm"));
    }
}

#[test]
fn test_cranelift_rejects_custom_cpu_strings() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let result = Codegen::for_target_with_opt_level_and_cpu(
        target,
        NativeOptimizationLevel::Standard,
        TargetCpu::Custom("znver4".to_string()),
    );
    assert!(result.is_err());
    let message = format!("{:?}", result.err());
    assert!(message.contains("does not accept free-form CPU"));
}
