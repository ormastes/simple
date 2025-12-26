//! Test helpers for LLVM codegen tests
//!
//! This module provides common setup and utility functions to reduce
//! duplication across LLVM backend tests.

use crate::codegen::llvm::LlvmBackend;
use simple_common::target::{Target, TargetArch, TargetOS};

/// Create an LLVM backend with default x86_64 Linux target and module
pub fn create_test_backend(module_name: &str) -> LlvmBackend {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();
    backend.create_module(module_name).unwrap();
    backend
}

/// Create an LLVM backend with specified architecture
pub fn create_test_backend_with_arch(module_name: &str, arch: TargetArch) -> LlvmBackend {
    let target = Target::new(arch, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();
    backend.create_module(module_name).unwrap();
    backend
}

/// Create an LLVM backend with specified target
pub fn create_test_backend_with_target(module_name: &str, target: Target) -> LlvmBackend {
    let backend = LlvmBackend::new(target).unwrap();
    backend.create_module(module_name).unwrap();
    backend
}
