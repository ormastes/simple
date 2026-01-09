//! Vulkan backend implementation
//!
//! This module provides the VulkanBackend struct that implements the NativeBackend trait,
//! enabling SPIR-V code generation for GPU kernels.

use crate::codegen::backend_trait::NativeBackend;
use crate::error::CompileError;
use crate::mir::MirModule;
use simple_common::target::Target;

/// Vulkan SPIR-V backend for GPU kernel compilation
pub struct VulkanBackend {
    target: Target,
    validation_layers_enabled: bool,
}

impl VulkanBackend {
    /// Create a new Vulkan backend for the given target
    pub fn new(target: Target) -> Result<Self, CompileError> {
        // Check if Vulkan is available (will implement detection later)
        #[cfg(debug_assertions)]
        let validation_layers_enabled = true;
        #[cfg(not(debug_assertions))]
        let validation_layers_enabled = false;

        Ok(Self {
            target,
            validation_layers_enabled,
        })
    }

    /// Check if Vulkan is available on the system
    fn vulkan_available() -> bool {
        // TODO: [codegen][P1] Implement actual Vulkan availability check
        // For now, assume available if feature is enabled
        true
    }
}

impl NativeBackend for VulkanBackend {
    fn target(&self) -> &Target {
        &self.target
    }

    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError> {
        tracing::info!("Vulkan backend: Compiling module to SPIR-V");

        // Create SPIR-V module builder
        let mut spirv_module = super::spirv_builder::SpirvModule::new()?;

        // Compile the MIR module to SPIR-V
        spirv_module.compile_module(module)?;

        // Serialize to bytecode
        let bytes = spirv_module.into_bytes()?;

        tracing::info!(
            "Vulkan backend: Generated {} bytes of SPIR-V bytecode",
            bytes.len()
        );

        Ok(bytes)
    }

    fn name(&self) -> &'static str {
        "Vulkan SPIR-V"
    }

    fn supports_target(_target: &Target) -> bool
    where
        Self: Sized,
    {
        // Vulkan is cross-platform and works on all targets with drivers
        Self::vulkan_available()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_common::target::{TargetArch, TargetOS};

    #[test]
    fn test_backend_creation() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = VulkanBackend::new(target);
        assert!(backend.is_ok());
    }

    #[test]
    fn test_backend_name() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = VulkanBackend::new(target).unwrap();
        assert_eq!(backend.name(), "Vulkan SPIR-V");
    }

    #[test]
    fn test_supports_target() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert!(VulkanBackend::supports_target(&target));
    }

    // =============================================================================
    // SPIR-V Compilation Tests
    // =============================================================================

    #[test]
    fn test_compile_empty_module() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let mut backend = VulkanBackend::new(target).unwrap();

        let module = MirModule {
            name: Some("test_empty".to_string()),
            functions: vec![],
        };

        let result = backend.compile(&module);
        assert!(result.is_ok(), "Empty module should compile successfully");

        let spirv = result.unwrap();
        assert!(!spirv.is_empty(), "SPIR-V output should not be empty");

        // Verify SPIR-V magic number
        assert!(spirv.len() >= 4, "SPIR-V should be at least 4 bytes");
        let magic = u32::from_le_bytes([spirv[0], spirv[1], spirv[2], spirv[3]]);
        assert_eq!(
            magic, 0x07230203,
            "SPIR-V magic number should be 0x07230203"
        );
    }

    #[test]
    fn test_compile_module_with_name() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let mut backend = VulkanBackend::new(target).unwrap();

        let module = MirModule {
            name: Some("my_gpu_module".to_string()),
            functions: vec![],
        };

        let result = backend.compile(&module);
        assert!(
            result.is_ok(),
            "Module with name should compile successfully"
        );
    }

    #[test]
    fn test_compile_multiple_times() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let mut backend = VulkanBackend::new(target).unwrap();

        let module = MirModule {
            name: Some("test_multi".to_string()),
            functions: vec![],
        };

        // Compile same module multiple times
        let result1 = backend.compile(&module);
        assert!(result1.is_ok());

        let result2 = backend.compile(&module);
        assert!(result2.is_ok());

        // Results should be identical
        let spirv1 = result1.unwrap();
        let spirv2 = result2.unwrap();
        assert_eq!(
            spirv1, spirv2,
            "Compiling same module should produce identical SPIR-V"
        );
    }

    #[test]
    fn test_spirv_header_structure() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let mut backend = VulkanBackend::new(target).unwrap();

        let module = MirModule {
            name: Some("test_header".to_string()),
            functions: vec![],
        };

        let spirv = backend.compile(&module).unwrap();

        // SPIR-V header is 5 words (20 bytes minimum)
        assert!(
            spirv.len() >= 20,
            "SPIR-V should have at least 20 bytes for header"
        );

        // Word 0: Magic number (0x07230203)
        let magic = u32::from_le_bytes([spirv[0], spirv[1], spirv[2], spirv[3]]);
        assert_eq!(magic, 0x07230203);

        // Word 1: Version (we don't check specific version, just verify it's present)
        let version_bytes = [spirv[4], spirv[5], spirv[6], spirv[7]];
        let version = u32::from_le_bytes(version_bytes);
        assert!(version > 0, "SPIR-V version should be non-zero");

        // Words 2-4 exist (generator, bound, schema)
        assert!(spirv.len() >= 20, "SPIR-V header should have all 5 words");
    }

    #[test]
    fn test_backend_target_preservation() {
        let targets = vec![
            Target::new(TargetArch::X86_64, TargetOS::Linux),
            Target::new(TargetArch::X86_64, TargetOS::Windows),
            Target::new(TargetArch::Aarch64, TargetOS::Linux),
        ];

        for target in targets {
            let backend = VulkanBackend::new(target.clone()).unwrap();
            assert_eq!(
                backend.target(),
                &target,
                "Backend should preserve target architecture"
            );
        }
    }

    #[test]
    fn test_validation_layers_debug_mode() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = VulkanBackend::new(target).unwrap();

        // In debug mode, validation layers should be enabled
        #[cfg(debug_assertions)]
        assert!(
            backend.validation_layers_enabled,
            "Validation layers should be enabled in debug builds"
        );

        // In release mode, validation layers should be disabled
        #[cfg(not(debug_assertions))]
        assert!(
            !backend.validation_layers_enabled,
            "Validation layers should be disabled in release builds"
        );
    }

    #[test]
    fn test_compile_result_deterministic() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let mut backend1 = VulkanBackend::new(target.clone()).unwrap();
        let mut backend2 = VulkanBackend::new(target).unwrap();

        let module = MirModule {
            name: Some("determinism_test".to_string()),
            functions: vec![],
        };

        let spirv1 = backend1.compile(&module).unwrap();
        let spirv2 = backend2.compile(&module).unwrap();

        assert_eq!(
            spirv1, spirv2,
            "Different backend instances should produce identical SPIR-V"
        );
    }

    #[test]
    fn test_spirv_size_reasonable() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let mut backend = VulkanBackend::new(target).unwrap();

        let module = MirModule {
            name: Some("size_test".to_string()),
            functions: vec![],
        };

        let spirv = backend.compile(&module).unwrap();

        // Empty module should produce small SPIR-V (< 1KB)
        assert!(
            spirv.len() < 1024,
            "Empty module SPIR-V should be less than 1KB, got {} bytes",
            spirv.len()
        );

        // But should have minimum size for valid SPIR-V
        assert!(
            spirv.len() >= 20,
            "SPIR-V should be at least 20 bytes for header"
        );
    }

    #[test]
    fn test_supports_target_all_platforms() {
        // Vulkan is cross-platform, should support all major platforms
        let platforms = vec![
            (TargetArch::X86_64, TargetOS::Linux),
            (TargetArch::X86_64, TargetOS::Windows),
            (TargetArch::X86_64, TargetOS::MacOS),
            (TargetArch::Aarch64, TargetOS::Linux),
            (TargetArch::Aarch64, TargetOS::MacOS), // Apple Silicon
        ];

        for (arch, os) in platforms {
            let target = Target::new(arch, os);
            let supports = VulkanBackend::supports_target(&target);
            // Just verify it doesn't panic - actual support depends on drivers
            println!("Vulkan support for {:?}/{:?}: {}", arch, os, supports);
        }
    }
}
