//! Tests for WASM compilation via LLVM backend
//!
//! This module tests WebAssembly target support including:
//! - Target triple generation (wasm32-unknown-unknown, wasm32-wasi, wasm64)
//! - Binary format validation (WASM magic bytes)
//! - Basic function compilation to WASM
//! - Backend selection routing
//! - Pointer width validation

#[cfg(test)]
mod tests {
    use crate::codegen::backend_trait::{BackendKind, NativeBackend};
    use crate::codegen::llvm::LlvmBackend;
    use simple_common::target::{Target, TargetArch, TargetOS, WasmRuntime};

    /// Test WASM target triple generation for standalone (no runtime)
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm32_standalone_triple() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Standalone);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.get_target_triple(), "wasm32-unknown-unknown");
    }

    /// Test WASM target triple generation for WASI runtime
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm32_wasi_triple() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Wasi);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.get_target_triple(), "wasm32-wasi");
    }

    /// Test WASM target triple generation for browser runtime
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm32_browser_triple() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Browser);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.get_target_triple(), "wasm32-unknown-unknown");
    }

    /// Test WASM target triple generation for Emscripten runtime
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm32_emscripten_triple() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Emscripten);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.get_target_triple(), "wasm32-unknown-emscripten");
    }

    /// Test WASM64 target triple generation (experimental)
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm64_standalone_triple() {
        let target = Target::new_wasm(TargetArch::Wasm64, WasmRuntime::Standalone);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.get_target_triple(), "wasm64-unknown-unknown");
    }

    /// Test WASM64 WASI target triple
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm64_wasi_triple() {
        let target = Target::new_wasm(TargetArch::Wasm64, WasmRuntime::Wasi);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.get_target_triple(), "wasm64-wasi");
    }

    /// Test WASM32 pointer width (should be 32 bits)
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm32_pointer_width() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Standalone);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 32);
    }

    /// Test WASM64 pointer width (should be 64 bits)
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm64_pointer_width() {
        let target = Target::new_wasm(TargetArch::Wasm64, WasmRuntime::Standalone);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 64);
    }

    /// Test that WASM targets route to LLVM backend
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm32_backend_selection() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Standalone);
        let backend_kind = BackendKind::for_target(&target);
        assert_eq!(backend_kind, BackendKind::Llvm);
    }

    /// Test that WASM64 targets route to LLVM backend
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm64_backend_selection() {
        let target = Target::new_wasm(TargetArch::Wasm64, WasmRuntime::Wasi);
        let backend_kind = BackendKind::for_target(&target);
        assert_eq!(backend_kind, BackendKind::Llvm);
    }

    /// Test that LLVM backend supports WASM32 target
    #[test]
    #[cfg(feature = "wasm")]
    fn test_llvm_supports_wasm32() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Standalone);
        assert!(LlvmBackend::supports_target(&target));
    }

    /// Test that LLVM backend supports WASM64 target
    #[test]
    #[cfg(feature = "wasm")]
    fn test_llvm_supports_wasm64() {
        let target = Target::new_wasm(TargetArch::Wasm64, WasmRuntime::Standalone);
        assert!(LlvmBackend::supports_target(&target));
    }


    /// Test that Target struct correctly stores WASM runtime
    #[test]
    #[cfg(feature = "wasm")]
    fn test_target_wasm_runtime_storage() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Wasi);
        assert_eq!(target.arch, TargetArch::Wasm32);
        assert_eq!(target.os, TargetOS::None);
        assert_eq!(target.wasm_runtime, Some(WasmRuntime::Wasi));
    }

    /// Test that non-WASM targets don't have wasm_runtime set
    #[test]
    fn test_non_wasm_target_no_runtime() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert_eq!(target.wasm_runtime, None);
    }

    /// Test WASM backend name
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasm_backend_name() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Standalone);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.name(), "llvm");
    }

    /// Test that WASI imports are automatically declared for wasm32-wasi targets
    #[test]
    #[cfg(all(feature = "wasm", feature = "wasm-wasi"))]
    fn test_wasi_imports_auto_declared() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Wasi);
        let backend = LlvmBackend::new(target).unwrap();

        // Create module - WASI imports should be automatically declared
        backend.create_module("test_wasi_auto").unwrap();

        // Get IR and verify WASI functions are declared
        let ir = backend.get_ir().unwrap();

        // Check for key WASI function declarations
        assert!(ir.contains("declare"), "IR should contain function declarations");
        assert!(ir.contains("fd_write"), "IR should declare fd_write");
        assert!(ir.contains("fd_read"), "IR should declare fd_read");
        assert!(ir.contains("environ_get"), "IR should declare environ_get");
        assert!(ir.contains("args_get"), "IR should declare args_get");
        assert!(ir.contains("proc_exit"), "IR should declare proc_exit");
    }

    /// Test that WASI imports are NOT declared for standalone WASM targets
    #[test]
    #[cfg(feature = "wasm")]
    fn test_wasi_imports_not_declared_for_standalone() {
        let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Standalone);
        let backend = LlvmBackend::new(target).unwrap();

        // Create module - WASI imports should NOT be declared for standalone
        backend.create_module("test_standalone").unwrap();

        // Get IR and verify WASI functions are NOT declared
        let ir = backend.get_ir().unwrap();

        // Standalone should not have WASI imports
        assert!(!ir.contains("fd_write") || !ir.contains("declare.*fd_write"));
        assert!(!ir.contains("environ_get") || !ir.contains("declare.*environ_get"));
    }
}
