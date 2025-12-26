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
        // TODO: Implement actual Vulkan availability check
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

        tracing::info!("Vulkan backend: Generated {} bytes of SPIR-V bytecode", bytes.len());

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
}
