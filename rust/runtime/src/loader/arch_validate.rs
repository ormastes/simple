//! Architecture validation for cross-platform safety.
//!
//! This module provides comprehensive validation to ensure loaded modules
//! are compatible with the current host architecture.

use simple_common::target::{Target, TargetArch, TargetConfig, TargetOS};

use super::smf::header::{Arch, Platform, SmfHeader};
use super::smf::settlement::SettlementHeader;

/// Result of architecture validation.
#[derive(Debug, Clone)]
pub struct ValidationResult {
    /// Whether the validation passed.
    pub passed: bool,
    /// List of validation errors.
    pub errors: Vec<ValidationError>,
    /// List of validation warnings.
    pub warnings: Vec<ValidationWarning>,
}

impl ValidationResult {
    /// Create a successful validation result.
    pub fn ok() -> Self {
        Self {
            passed: true,
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Check if validation passed.
    pub fn is_ok(&self) -> bool {
        self.passed
    }

    /// Check if validation failed.
    pub fn is_err(&self) -> bool {
        !self.passed
    }

    /// Get a summary string.
    pub fn summary(&self) -> String {
        if self.passed {
            if self.warnings.is_empty() {
                "Validation passed".to_string()
            } else {
                format!("Validation passed with {} warning(s)", self.warnings.len())
            }
        } else {
            format!("Validation failed with {} error(s)", self.errors.len())
        }
    }
}

impl std::fmt::Display for ValidationResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.summary())?;

        if !self.errors.is_empty() {
            writeln!(f, "\nErrors:")?;
            for err in &self.errors {
                writeln!(f, "  - {}", err)?;
            }
        }

        if !self.warnings.is_empty() {
            writeln!(f, "\nWarnings:")?;
            for warn in &self.warnings {
                writeln!(f, "  - {}", warn)?;
            }
        }

        Ok(())
    }
}

/// Validation error types.
#[derive(Debug, Clone)]
pub enum ValidationError {
    /// Architecture mismatch between module and host.
    ArchMismatch {
        module_arch: TargetArch,
        host_arch: TargetArch,
    },
    /// Platform/OS mismatch between module and host.
    PlatformMismatch { module_os: TargetOS, host_os: TargetOS },
    /// Pointer size mismatch.
    PointerSizeMismatch { module_bits: usize, host_bits: usize },
    /// Invalid architecture in module header.
    InvalidArch(u8),
    /// Invalid platform in module header.
    InvalidPlatform(u8),
    /// Module requires features not available on host.
    MissingFeature(String),
    /// Cannot execute 32-bit module on this 64-bit host.
    No32BitSupport,
    /// Cannot execute module due to ABI incompatibility.
    AbiIncompatible(String),
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValidationError::ArchMismatch { module_arch, host_arch } => {
                write!(
                    f,
                    "Architecture mismatch: module is {}, host is {}",
                    module_arch, host_arch
                )
            }
            ValidationError::PlatformMismatch { module_os, host_os } => {
                write!(f, "Platform mismatch: module is for {}, host is {}", module_os, host_os)
            }
            ValidationError::PointerSizeMismatch { module_bits, host_bits } => {
                write!(
                    f,
                    "Pointer size mismatch: module is {}-bit, host is {}-bit",
                    module_bits, host_bits
                )
            }
            ValidationError::InvalidArch(v) => {
                write!(f, "Invalid architecture value in header: {}", v)
            }
            ValidationError::InvalidPlatform(v) => {
                write!(f, "Invalid platform value in header: {}", v)
            }
            ValidationError::MissingFeature(feat) => {
                write!(f, "Module requires feature not available on host: {}", feat)
            }
            ValidationError::No32BitSupport => {
                write!(f, "Cannot execute 32-bit modules on this host")
            }
            ValidationError::AbiIncompatible(reason) => {
                write!(f, "ABI incompatible: {}", reason)
            }
        }
    }
}

impl std::error::Error for ValidationError {}

/// Validation warning types.
#[derive(Debug, Clone)]
pub enum ValidationWarning {
    /// Platform is set to 'Any' - may not work on all systems.
    AnyPlatform,
    /// Module was built for a different endianness.
    EndianMismatch,
    /// Module was built with debug info but running in release mode.
    DebugInRelease,
    /// Module uses deprecated features.
    DeprecatedFeature(String),
}

impl std::fmt::Display for ValidationWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValidationWarning::AnyPlatform => {
                write!(f, "Module targets 'any' platform - may have portability issues")
            }
            ValidationWarning::EndianMismatch => {
                write!(f, "Module may have been built with different endianness")
            }
            ValidationWarning::DebugInRelease => {
                write!(f, "Module contains debug info but running in release mode")
            }
            ValidationWarning::DeprecatedFeature(feat) => {
                write!(f, "Module uses deprecated feature: {}", feat)
            }
        }
    }
}

/// Architecture validator for SMF modules.
pub struct ArchValidator {
    /// Host target specification.
    host: Target,
    /// Whether to allow 'Any' platform.
    allow_any_platform: bool,
    /// Whether to allow cross-architecture execution (where possible).
    allow_cross_arch: bool,
}

impl ArchValidator {
    /// Create a new validator for the current host.
    pub fn new() -> Self {
        Self {
            host: Target::host(),
            allow_any_platform: true,
            allow_cross_arch: false,
        }
    }

    /// Create a validator for a specific target.
    pub fn for_target(target: Target) -> Self {
        Self {
            host: target,
            allow_any_platform: true,
            allow_cross_arch: false,
        }
    }

    /// Set whether to allow 'Any' platform modules.
    pub fn allow_any_platform(mut self, allow: bool) -> Self {
        self.allow_any_platform = allow;
        self
    }

    /// Set whether to allow cross-architecture execution.
    pub fn allow_cross_arch(mut self, allow: bool) -> Self {
        self.allow_cross_arch = allow;
        self
    }

    /// Helper to parse and validate architecture from header
    fn parse_arch_from_header(arch_byte: u8, result: &mut ValidationResult) -> Option<TargetArch> {
        match Arch::from_u8(arch_byte) {
            Some(arch) => Some(arch.to_target_arch()),
            None => {
                result.passed = false;
                result.errors.push(ValidationError::InvalidArch(arch_byte));
                None
            }
        }
    }

    /// Validate an SMF header.
    pub fn validate_smf(&self, header: &SmfHeader) -> ValidationResult {
        let mut result = ValidationResult::ok();

        // Parse architecture from header
        let module_arch = match Self::parse_arch_from_header(header.arch, &mut result) {
            Some(arch) => arch,
            None => return result,
        };

        // Parse platform from header
        let module_os = match Platform::from_u8(header.platform) {
            Some(platform) => platform.to_target_os(),
            None => {
                result.passed = false;
                result.errors.push(ValidationError::InvalidPlatform(header.platform));
                return result;
            }
        };

        // Validate architecture
        self.validate_arch(module_arch, &mut result);

        // Validate platform
        self.validate_platform(module_os, &mut result);

        // Check pointer size compatibility
        self.validate_pointer_size(module_arch, &mut result);

        result
    }

    /// Validate a settlement header.
    ///
    /// Note: SettlementHeader only contains arch, not platform.
    /// Platform is assumed to be 'Any' for settlements.
    pub fn validate_settlement(&self, header: &SettlementHeader) -> ValidationResult {
        let mut result = ValidationResult::ok();

        // Parse architecture from header
        let module_arch = match Self::parse_arch_from_header(header.arch, &mut result) {
            Some(arch) => arch,
            None => return result,
        };

        // Settlement headers don't have platform info - assume 'Any'
        let module_os = TargetOS::Any;

        // Validate architecture
        self.validate_arch(module_arch, &mut result);

        // Validate platform (will produce warning for 'Any')
        self.validate_platform(module_os, &mut result);

        // Check pointer size compatibility
        self.validate_pointer_size(module_arch, &mut result);

        result
    }

    /// Validate a target specification.
    pub fn validate_target(&self, target: Target) -> ValidationResult {
        let mut result = ValidationResult::ok();

        self.validate_arch(target.arch, &mut result);
        self.validate_platform(target.os, &mut result);
        self.validate_pointer_size(target.arch, &mut result);

        result
    }

    /// Internal: validate architecture compatibility.
    fn validate_arch(&self, module_arch: TargetArch, result: &mut ValidationResult) {
        if module_arch == self.host.arch {
            return; // Exact match
        }

        if !self.allow_cross_arch {
            result.passed = false;
            result.errors.push(ValidationError::ArchMismatch {
                module_arch,
                host_arch: self.host.arch,
            });
            return;
        }

        // Check for compatible cross-arch cases
        // For now, only allow exact matches
        // Future: could allow x86_64 to run x86 modules with WOW64-style support
        result.passed = false;
        result.errors.push(ValidationError::ArchMismatch {
            module_arch,
            host_arch: self.host.arch,
        });
    }

    /// Internal: validate platform compatibility.
    fn validate_platform(&self, module_os: TargetOS, result: &mut ValidationResult) {
        if module_os == self.host.os {
            return; // Exact match
        }

        if module_os == TargetOS::Any {
            if self.allow_any_platform {
                result.warnings.push(ValidationWarning::AnyPlatform);
            } else {
                result.passed = false;
                result.errors.push(ValidationError::PlatformMismatch {
                    module_os,
                    host_os: self.host.os,
                });
            }
            return;
        }

        result.passed = false;
        result.errors.push(ValidationError::PlatformMismatch {
            module_os,
            host_os: self.host.os,
        });
    }

    /// Internal: validate pointer size compatibility.
    fn validate_pointer_size(&self, module_arch: TargetArch, result: &mut ValidationResult) {
        let module_config = TargetConfig::for_arch(module_arch);
        let host_config = self.host.config();

        if module_config.pointer_bytes != host_config.pointer_bytes {
            // 64-bit host cannot natively run 32-bit code without special support
            if host_config.pointer_bytes == 8 && module_config.pointer_bytes == 4 {
                result.passed = false;
                result.errors.push(ValidationError::No32BitSupport);
            } else {
                result.passed = false;
                result.errors.push(ValidationError::PointerSizeMismatch {
                    module_bits: module_config.pointer_bytes * 8,
                    host_bits: host_config.pointer_bytes * 8,
                });
            }
        }
    }

    /// Get the host target.
    pub fn host(&self) -> Target {
        self.host
    }
}

impl Default for ArchValidator {
    fn default() -> Self {
        Self::new()
    }
}

/// Check if a target is compatible with the current host.
pub fn is_compatible(target: Target) -> bool {
    ArchValidator::new().validate_target(target).is_ok()
}

/// Check if a target is the native host.
pub fn is_native(target: Target) -> bool {
    target == Target::host()
}

/// Get the native host target.
pub fn native_target() -> Target {
    Target::host()
}

/// Get all architectures that can be compiled for (not necessarily executed).
pub fn supported_compile_targets() -> Vec<Target> {
    // All 64-bit targets can be compiled to (Cranelift supports them)
    // 32-bit targets are postponed until LLVM backend
    vec![
        Target::new(TargetArch::X86_64, TargetOS::Linux),
        Target::new(TargetArch::X86_64, TargetOS::Windows),
        Target::new(TargetArch::X86_64, TargetOS::MacOS),
        Target::new(TargetArch::Aarch64, TargetOS::Linux),
        Target::new(TargetArch::Aarch64, TargetOS::MacOS),
        Target::new(TargetArch::Riscv64, TargetOS::Linux),
    ]
}

/// Get all architectures that can be executed on the current host.
pub fn supported_execute_targets() -> Vec<Target> {
    // Only native target can be executed
    vec![Target::host()]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validator_native_target() {
        let validator = ArchValidator::new();
        let result = validator.validate_target(Target::host());
        assert!(result.is_ok(), "Native target should validate: {}", result);
    }

    #[test]
    fn test_validator_mismatched_arch() {
        let validator = ArchValidator::for_target(Target::new(TargetArch::X86_64, TargetOS::Linux));
        let result = validator.validate_target(Target::new(TargetArch::Aarch64, TargetOS::Linux));
        assert!(result.is_err());
        assert!(matches!(result.errors[0], ValidationError::ArchMismatch { .. }));
    }

    #[test]
    fn test_validator_mismatched_platform() {
        let validator = ArchValidator::for_target(Target::new(TargetArch::X86_64, TargetOS::Linux));
        let result = validator.validate_target(Target::new(TargetArch::X86_64, TargetOS::Windows));
        assert!(result.is_err());
        assert!(matches!(result.errors[0], ValidationError::PlatformMismatch { .. }));
    }

    #[test]
    fn test_validator_any_platform_warning() {
        let validator =
            ArchValidator::for_target(Target::new(TargetArch::X86_64, TargetOS::Linux)).allow_any_platform(true);
        let result = validator.validate_target(Target::new(TargetArch::X86_64, TargetOS::Any));
        assert!(result.is_ok());
        assert!(!result.warnings.is_empty());
    }

    #[test]
    fn test_validator_32bit_on_64bit() {
        let validator = ArchValidator::for_target(Target::new(TargetArch::X86_64, TargetOS::Linux));
        let result = validator.validate_target(Target::new(TargetArch::X86, TargetOS::Linux));
        assert!(result.is_err());
        // Should have both arch mismatch and 32-bit support error
        assert!(result
            .errors
            .iter()
            .any(|e| matches!(e, ValidationError::ArchMismatch { .. })));
    }

    #[test]
    fn test_is_compatible() {
        assert!(is_compatible(Target::host()));
    }

    #[test]
    fn test_is_native() {
        assert!(is_native(Target::host()));
        // Non-host target should not be native (unless we happen to be on that exact target)
        let other = Target::new(TargetArch::Riscv64, TargetOS::None);
        if Target::host() != other {
            assert!(!is_native(other));
        }
    }

    #[test]
    fn test_supported_targets() {
        let compile_targets = supported_compile_targets();
        assert!(!compile_targets.is_empty());

        let execute_targets = supported_execute_targets();
        assert_eq!(execute_targets.len(), 1);
        assert_eq!(execute_targets[0], Target::host());
    }

    #[test]
    fn test_validation_result_display() {
        let result = ValidationResult::ok();
        let s = result.to_string();
        assert!(s.contains("passed"));
    }

    #[test]
    fn test_validation_error_display() {
        let err = ValidationError::ArchMismatch {
            module_arch: TargetArch::X86_64,
            host_arch: TargetArch::Aarch64,
        };
        let s = err.to_string();
        assert!(s.contains("x86_64"));
        assert!(s.contains("aarch64"));
    }
}
