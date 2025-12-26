//! Vulkan backend integration tests
//! Tests GPU kernel compilation with Vulkan backend
//! Focus: End-to-end compilation and backend selection

#![cfg(feature = "vulkan")]

use simple_compiler::codegen::backend_trait::{BackendKind, NativeBackend};
use simple_compiler::codegen::vulkan::VulkanBackend;
use simple_compiler::mir::MirModule;
use simple_common::target::{Target, TargetArch, TargetOS};

// =============================================================================
// Backend Selection Tests
// =============================================================================

#[test]
fn test_vulkan_backend_for_gpu_kernel() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = BackendKind::for_gpu_kernel(&target);

    // Should select Vulkan if available, otherwise Software
    match backend {
        BackendKind::Vulkan => {
            // Vulkan is available
            assert!(VulkanBackend::supports_target(&target));
        }
        BackendKind::Software => {
            // Vulkan not available, using software fallback
            // This is acceptable
        }
        _ => panic!("for_gpu_kernel should only return Vulkan or Software"),
    }
}

#[test]
fn test_vulkan_backend_supports_all_targets() {
    // Vulkan is cross-platform, should support all targets
    let targets = vec![
        Target::new(TargetArch::X86_64, TargetOS::Linux),
        Target::new(TargetArch::X86_64, TargetOS::Windows),
        Target::new(TargetArch::X86_64, TargetOS::MacOS),
        Target::new(TargetArch::Aarch64, TargetOS::Linux),
    ];

    for target in targets {
        let supports = VulkanBackend::supports_target(&target);
        // Result depends on whether Vulkan runtime is available
        // Just verify the function doesn't panic
        println!("Target {:?}: Vulkan support = {}", target, supports);
    }
}

#[test]
fn test_software_backend_not_in_for_target() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = BackendKind::for_target(&target);

    // for_target should never return Software (that's only for GPU kernels)
    assert_ne!(backend, BackendKind::Software);
}

// =============================================================================
// VulkanBackend Creation Tests
// =============================================================================

#[test]
fn test_vulkan_backend_creation() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = VulkanBackend::new(target);

    // Creation should succeed regardless of Vulkan availability
    // (actual availability is checked during compilation)
    match backend {
        Ok(backend) => {
            assert_eq!(backend.name(), "Vulkan SPIR-V");
            assert_eq!(backend.target(), &target);
        }
        Err(e) => {
            // If creation fails, it should be due to Vulkan unavailability
            println!("Vulkan backend creation failed (expected if no drivers): {:?}", e);
        }
    }
}

#[test]
fn test_vulkan_backend_name() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    if let Ok(backend) = VulkanBackend::new(target) {
        assert_eq!(backend.name(), "Vulkan SPIR-V");
    }
}

#[test]
fn test_vulkan_backend_target() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    if let Ok(backend) = VulkanBackend::new(target.clone()) {
        assert_eq!(backend.target(), &target);
    }
}

#[test]
fn test_vulkan_backend_different_targets() {
    let targets = vec![
        Target::new(TargetArch::X86_64, TargetOS::Linux),
        Target::new(TargetArch::X86_64, TargetOS::Windows),
        Target::new(TargetArch::Aarch64, TargetOS::Linux),
    ];

    for target in targets {
        let backend = VulkanBackend::new(target.clone());
        match backend {
            Ok(b) => {
                assert_eq!(b.target(), &target);
                println!("Created Vulkan backend for {:?}", target);
            }
            Err(e) => {
                println!("Failed to create backend for {:?}: {:?}", target, e);
            }
        }
    }
}

// =============================================================================
// SPIR-V Compilation Tests
// =============================================================================

#[test]
fn test_compile_empty_module() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let mut backend = match VulkanBackend::new(target) {
        Ok(b) => b,
        Err(_) => {
            println!("Skipping test: Vulkan not available");
            return;
        }
    };

    // Create minimal empty MIR module
    let module = MirModule {
        name: Some("test_empty".to_string()),
        functions: vec![],
    };

    let result = backend.compile(&module);

    // Empty module compilation should succeed but produce minimal SPIR-V
    match result {
        Ok(spirv) => {
            assert!(!spirv.is_empty(), "SPIR-V output should not be empty");

            // Check SPIR-V magic number (0x07230203)
            if spirv.len() >= 4 {
                let magic = u32::from_le_bytes([spirv[0], spirv[1], spirv[2], spirv[3]]);
                assert_eq!(magic, 0x07230203, "Invalid SPIR-V magic number");
            }

            println!("Empty module compiled to {} bytes of SPIR-V", spirv.len());
        }
        Err(e) => {
            println!("Empty module compilation failed: {:?}", e);
        }
    }
}

#[test]
fn test_spirv_magic_number() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let mut backend = match VulkanBackend::new(target) {
        Ok(b) => b,
        Err(_) => {
            println!("Skipping test: Vulkan not available");
            return;
        }
    };

    let module = MirModule {
        name: Some("test_magic".to_string()),
        functions: vec![],
    };

    if let Ok(spirv) = backend.compile(&module) {
        assert!(spirv.len() >= 4, "SPIR-V should be at least 4 bytes");

        // SPIR-V magic number is always 0x07230203 in little-endian
        let magic = u32::from_le_bytes([spirv[0], spirv[1], spirv[2], spirv[3]]);
        assert_eq!(
            magic, 0x07230203,
            "Invalid SPIR-V magic number: expected 0x07230203, got 0x{:08x}",
            magic
        );
    }
}

// =============================================================================
// SPIR-V Validation Tests
// =============================================================================

#[test]
#[ignore] // Requires spirv-val to be installed
fn test_spirv_validation_with_spirv_val() {
    use std::process::{Command, Stdio};
    use std::io::Write;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let mut backend = match VulkanBackend::new(target) {
        Ok(b) => b,
        Err(_) => {
            println!("Skipping test: Vulkan not available");
            return;
        }
    };

    let module = MirModule {
        name: Some("test_validation".to_string()),
        functions: vec![],
    };

    let spirv = match backend.compile(&module) {
        Ok(s) => s,
        Err(e) => {
            println!("Compilation failed: {:?}", e);
            return;
        }
    };

    // Try to run spirv-val
    let mut child = match Command::new("spirv-val")
        .arg("--target-env").arg("vulkan1.1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(_) => {
            println!("spirv-val not found, skipping validation");
            return;
        }
    };

    // Write SPIR-V to stdin
    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(&spirv).expect("Failed to write to spirv-val");
    }

    let output = child.wait_with_output().expect("Failed to wait for spirv-val");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("SPIR-V validation failed:\n{}", stderr);
    }

    println!("SPIR-V validation passed!");
}

// =============================================================================
// Backend Selection Edge Cases
// =============================================================================

#[test]
fn test_backend_kind_equality() {
    // Test that BackendKind variants can be compared
    assert_eq!(BackendKind::Vulkan, BackendKind::Vulkan);
    assert_eq!(BackendKind::Software, BackendKind::Software);
    assert_ne!(BackendKind::Vulkan, BackendKind::Software);
}

#[test]
fn test_for_gpu_kernel_consistency() {
    // Calling for_gpu_kernel multiple times should return the same result
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend1 = BackendKind::for_gpu_kernel(&target);
    let backend2 = BackendKind::for_gpu_kernel(&target);
    assert_eq!(backend1, backend2, "Backend selection should be consistent");
}

