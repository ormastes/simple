//! Target architecture abstraction for cross-compilation support.
//!
//! This module provides:
//! - `TargetArch` enum for all supported architectures
//! - `PointerSize` for 32-bit vs 64-bit handling
//! - `TargetConfig` with architecture-specific constants
//! - Functions to detect host architecture and parse target strings

use std::fmt;
use std::str::FromStr;

/// Supported CPU architectures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum TargetArch {
    /// x86-64 (AMD64)
    X86_64 = 0,
    /// ARM64 (AArch64)
    Aarch64 = 1,
    /// x86 32-bit (i686)
    X86 = 2,
    /// ARM 32-bit (ARMv7)
    Arm = 3,
    /// RISC-V 64-bit
    Riscv64 = 4,
    /// RISC-V 32-bit
    Riscv32 = 5,
    /// WebAssembly 32-bit
    Wasm32 = 6,
    /// WebAssembly 64-bit (experimental)
    Wasm64 = 7,
}

impl TargetArch {
    /// Get the architecture for the host machine.
    #[cfg(target_arch = "x86_64")]
    pub const fn host() -> Self {
        TargetArch::X86_64
    }

    #[cfg(target_arch = "aarch64")]
    pub const fn host() -> Self {
        TargetArch::Aarch64
    }

    #[cfg(target_arch = "x86")]
    pub const fn host() -> Self {
        TargetArch::X86
    }

    #[cfg(target_arch = "arm")]
    pub const fn host() -> Self {
        TargetArch::Arm
    }

    #[cfg(target_arch = "riscv64")]
    pub const fn host() -> Self {
        TargetArch::Riscv64
    }

    #[cfg(target_arch = "riscv32")]
    pub const fn host() -> Self {
        TargetArch::Riscv32
    }

    /// Fallback for unsupported host architectures (compile-time error for actual use).
    #[cfg(not(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "x86",
        target_arch = "arm",
        target_arch = "riscv64",
        target_arch = "riscv32"
    )))]
    pub const fn host() -> Self {
        // Default to x86_64 for unknown architectures (will fail at runtime if actually used)
        TargetArch::X86_64
    }

    /// Get the pointer size for this architecture.
    pub const fn pointer_size(&self) -> PointerSize {
        match self {
            TargetArch::X86_64 | TargetArch::Aarch64 | TargetArch::Riscv64 | TargetArch::Wasm64 => {
                PointerSize::Bits64
            }
            TargetArch::X86 | TargetArch::Arm | TargetArch::Riscv32 | TargetArch::Wasm32 => {
                PointerSize::Bits32
            }
        }
    }

    /// Check if this is a 64-bit architecture.
    pub const fn is_64bit(&self) -> bool {
        matches!(self.pointer_size(), PointerSize::Bits64)
    }

    /// Check if this is a 32-bit architecture.
    pub const fn is_32bit(&self) -> bool {
        matches!(self.pointer_size(), PointerSize::Bits32)
    }

    /// Check if this is a WebAssembly architecture.
    pub const fn is_wasm(&self) -> bool {
        matches!(self, TargetArch::Wasm32 | TargetArch::Wasm64)
    }

    /// Get the Cranelift target triple string.
    pub const fn triple_str(&self) -> &'static str {
        match self {
            TargetArch::X86_64 => "x86_64-unknown-linux-gnu",
            TargetArch::Aarch64 => "aarch64-unknown-linux-gnu",
            TargetArch::X86 => "i686-unknown-linux-gnu",
            TargetArch::Arm => "armv7-unknown-linux-gnueabihf",
            TargetArch::Riscv64 => "riscv64gc-unknown-linux-gnu",
            TargetArch::Riscv32 => "riscv32gc-unknown-linux-gnu",
            TargetArch::Wasm32 => "wasm32-unknown-unknown",
            TargetArch::Wasm64 => "wasm64-unknown-unknown",
        }
    }

    /// Get the short name for this architecture.
    pub const fn name(&self) -> &'static str {
        match self {
            TargetArch::X86_64 => "x86_64",
            TargetArch::Aarch64 => "aarch64",
            TargetArch::X86 => "i686",
            TargetArch::Arm => "armv7",
            TargetArch::Riscv64 => "riscv64",
            TargetArch::Riscv32 => "riscv32",
            TargetArch::Wasm32 => "wasm32",
            TargetArch::Wasm64 => "wasm64",
        }
    }

    /// Get all supported architectures.
    pub const fn all() -> &'static [TargetArch] {
        &[
            TargetArch::X86_64,
            TargetArch::Aarch64,
            TargetArch::X86,
            TargetArch::Arm,
            TargetArch::Riscv64,
            TargetArch::Riscv32,
            TargetArch::Wasm32,
            TargetArch::Wasm64,
        ]
    }

    /// Get the configuration for this architecture.
    pub const fn config(&self) -> TargetConfig {
        TargetConfig::for_arch(*self)
    }
}

impl fmt::Display for TargetArch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl FromStr for TargetArch {
    type Err = TargetParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s_lower = s.to_lowercase();
        match s_lower.as_str() {
            "x86_64" | "x86-64" | "amd64" | "x64" => Ok(TargetArch::X86_64),
            "aarch64" | "arm64" => Ok(TargetArch::Aarch64),
            "x86" | "i686" | "i386" | "i586" => Ok(TargetArch::X86),
            "arm" | "armv7" | "armv7l" | "arm32" => Ok(TargetArch::Arm),
            "riscv64" | "riscv64gc" => Ok(TargetArch::Riscv64),
            "riscv32" | "riscv32gc" => Ok(TargetArch::Riscv32),
            "wasm32" | "wasm" => Ok(TargetArch::Wasm32),
            "wasm64" => Ok(TargetArch::Wasm64),
            _ => Err(TargetParseError::UnknownArch(s.to_string())),
        }
    }
}

/// Error when parsing a target architecture.
#[derive(Debug, Clone)]
pub enum TargetParseError {
    UnknownArch(String),
}

impl fmt::Display for TargetParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TargetParseError::UnknownArch(s) => {
                write!(f, "unknown architecture '{}'. Supported: ", s)?;
                let names: Vec<_> = TargetArch::all().iter().map(|a| a.name()).collect();
                write!(f, "{}", names.join(", "))
            }
        }
    }
}

impl std::error::Error for TargetParseError {}

/// Pointer size (32-bit or 64-bit).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PointerSize {
    Bits32,
    Bits64,
}

impl PointerSize {
    /// Size in bytes.
    pub const fn bytes(&self) -> usize {
        match self {
            PointerSize::Bits32 => 4,
            PointerSize::Bits64 => 8,
        }
    }

    /// Size in bits.
    pub const fn bits(&self) -> usize {
        match self {
            PointerSize::Bits32 => 32,
            PointerSize::Bits64 => 64,
        }
    }
}

/// Target-specific configuration constants.
#[derive(Debug, Clone, Copy)]
pub struct TargetConfig {
    /// The target architecture.
    pub arch: TargetArch,
    /// Pointer size in bytes (4 or 8).
    pub pointer_bytes: usize,
    /// Size of RuntimeValue in bytes.
    pub value_bytes: usize,
    /// Tag bits used in tagged pointers.
    pub tag_bits: usize,
    /// Alignment requirement for heap allocations.
    pub heap_align: usize,
    /// Whether this architecture uses little-endian byte order.
    pub is_little_endian: bool,
    /// Default stack size in bytes.
    pub default_stack_size: usize,
}

impl TargetConfig {
    /// Create a configuration for a specific architecture.
    pub const fn for_arch(arch: TargetArch) -> Self {
        match arch.pointer_size() {
            PointerSize::Bits64 => Self {
                arch,
                pointer_bytes: 8,
                value_bytes: 8, // 64-bit tagged values
                tag_bits: 3,    // 3 bits = 8 tags
                heap_align: 8,  // 8-byte alignment for pointers
                is_little_endian: true,
                default_stack_size: 8 * 1024 * 1024, // 8 MB
            },
            PointerSize::Bits32 => Self {
                arch,
                pointer_bytes: 4,
                value_bytes: 8, // Still use 64-bit values for consistent semantics
                tag_bits: 3,    // Same tagging scheme
                heap_align: 8,  // 8-byte alignment for 64-bit values
                is_little_endian: true,
                default_stack_size: 2 * 1024 * 1024, // 2 MB
            },
        }
    }

    /// Get the mask for tag bits.
    pub const fn tag_mask(&self) -> u64 {
        (1u64 << self.tag_bits) - 1
    }

    /// Get the maximum pointer value that can fit with tag bits.
    pub const fn max_tagged_ptr(&self) -> u64 {
        match self.arch.pointer_size() {
            PointerSize::Bits64 => !self.tag_mask(),
            PointerSize::Bits32 => (u32::MAX as u64) & !self.tag_mask(),
        }
    }

    /// Check if this is the host architecture.
    pub fn is_host(&self) -> bool {
        self.arch == TargetArch::host()
    }
}

impl Default for TargetConfig {
    fn default() -> Self {
        Self::for_arch(TargetArch::host())
    }
}

/// Supported operating systems.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum TargetOS {
    /// Platform-agnostic (bare metal or any OS)
    Any = 0,
    /// Linux
    Linux = 1,
    /// Windows
    Windows = 2,
    /// macOS
    MacOS = 3,
    /// FreeBSD
    FreeBSD = 4,
    /// Bare metal (no OS)
    None = 5,
}

impl TargetOS {
    /// Get the OS for the host machine.
    #[cfg(target_os = "linux")]
    pub const fn host() -> Self {
        TargetOS::Linux
    }

    #[cfg(target_os = "windows")]
    pub const fn host() -> Self {
        TargetOS::Windows
    }

    #[cfg(target_os = "macos")]
    pub const fn host() -> Self {
        TargetOS::MacOS
    }

    #[cfg(target_os = "freebsd")]
    pub const fn host() -> Self {
        TargetOS::FreeBSD
    }

    #[cfg(not(any(
        target_os = "linux",
        target_os = "windows",
        target_os = "macos",
        target_os = "freebsd"
    )))]
    pub const fn host() -> Self {
        TargetOS::Any
    }

    /// Get the short name for this OS.
    pub const fn name(&self) -> &'static str {
        match self {
            TargetOS::Any => "any",
            TargetOS::Linux => "linux",
            TargetOS::Windows => "windows",
            TargetOS::MacOS => "macos",
            TargetOS::FreeBSD => "freebsd",
            TargetOS::None => "none",
        }
    }
}

impl fmt::Display for TargetOS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// WebAssembly runtime environment
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum WasmRuntime {
    /// Standalone WASM (no imports except memory)
    Standalone = 0,
    /// WASI (WebAssembly System Interface) - POSIX-like syscalls
    Wasi = 1,
    /// Browser environment (web-sys, wasm-bindgen)
    Browser = 2,
    /// Emscripten compatibility layer
    Emscripten = 3,
}

impl WasmRuntime {
    /// Get the short name for this runtime.
    pub const fn name(&self) -> &'static str {
        match self {
            WasmRuntime::Standalone => "standalone",
            WasmRuntime::Wasi => "wasi",
            WasmRuntime::Browser => "browser",
            WasmRuntime::Emscripten => "emscripten",
        }
    }
}

impl fmt::Display for WasmRuntime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Full target specification (architecture + OS + optional WASM runtime).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Target {
    pub arch: TargetArch,
    pub os: TargetOS,
    /// WebAssembly runtime environment (only applicable for WASM targets)
    pub wasm_runtime: Option<WasmRuntime>,
}

impl Target {
    /// Create a new target specification.
    pub const fn new(arch: TargetArch, os: TargetOS) -> Self {
        Self {
            arch,
            os,
            wasm_runtime: None,
        }
    }

    /// Create a new WASM target with runtime environment.
    pub const fn new_wasm(arch: TargetArch, runtime: WasmRuntime) -> Self {
        Self {
            arch,
            os: TargetOS::None,
            wasm_runtime: Some(runtime),
        }
    }

    /// Get the host target.
    pub const fn host() -> Self {
        Self {
            arch: TargetArch::host(),
            os: TargetOS::host(),
            wasm_runtime: None,
        }
    }

    /// Get the configuration for this target.
    pub const fn config(&self) -> TargetConfig {
        TargetConfig::for_arch(self.arch)
    }

    /// Check if this is the host target.
    pub fn is_host(&self) -> bool {
        self.arch == TargetArch::host() && self.os == TargetOS::host()
    }

    /// Parse a target triple string (e.g., "x86_64-linux", "aarch64-macos", "wasm32-wasi").
    pub fn parse(s: &str) -> Result<Self, TargetParseError> {
        let parts: Vec<&str> = s.split('-').collect();

        let arch = parts
            .first()
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or(TargetArch::host());

        // Detect WASM runtime from triple
        let wasm_runtime = if matches!(arch, TargetArch::Wasm32 | TargetArch::Wasm64) {
            parts.get(1).and_then(|s| match s.to_lowercase().as_str() {
                "wasi" => Some(WasmRuntime::Wasi),
                "unknown" => {
                    // Check third part for "emscripten"
                    Some(parts.get(2).map_or(WasmRuntime::Standalone, |p| {
                        match p.to_lowercase().as_str() {
                            "emscripten" => WasmRuntime::Emscripten,
                            _ => WasmRuntime::Standalone,
                        }
                    }))
                }
                _ => Some(WasmRuntime::Standalone),
            })
        } else {
            None
        };

        let os = parts
            .get(1)
            .map(|s| match s.to_lowercase().as_str() {
                "linux" | "gnu" => TargetOS::Linux,
                "windows" | "win" | "msvc" => TargetOS::Windows,
                "macos" | "darwin" | "apple" => TargetOS::MacOS,
                "freebsd" => TargetOS::FreeBSD,
                "none" | "bare" | "unknown" | "wasi" => TargetOS::None,
                _ => TargetOS::Any,
            })
            .unwrap_or(TargetOS::host());

        Ok(Self {
            arch,
            os,
            wasm_runtime,
        })
    }

    /// Get the triple string for Cranelift.
    pub const fn triple_str(&self) -> &'static str {
        self.arch.triple_str()
    }
}

impl Default for Target {
    fn default() -> Self {
        Self::host()
    }
}

impl fmt::Display for Target {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.arch, self.os)
    }
}

impl FromStr for Target {
    type Err = TargetParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_host_arch() {
        let host = TargetArch::host();
        // Should be a valid arch
        assert!(TargetArch::all().contains(&host));
    }

    #[test]
    fn test_parse_arch() {
        assert_eq!("x86_64".parse::<TargetArch>().unwrap(), TargetArch::X86_64);
        assert_eq!("amd64".parse::<TargetArch>().unwrap(), TargetArch::X86_64);
        assert_eq!(
            "aarch64".parse::<TargetArch>().unwrap(),
            TargetArch::Aarch64
        );
        assert_eq!("arm64".parse::<TargetArch>().unwrap(), TargetArch::Aarch64);
        assert_eq!("i686".parse::<TargetArch>().unwrap(), TargetArch::X86);
        assert_eq!("armv7".parse::<TargetArch>().unwrap(), TargetArch::Arm);
        assert_eq!(
            "riscv64".parse::<TargetArch>().unwrap(),
            TargetArch::Riscv64
        );
        assert_eq!(
            "riscv32".parse::<TargetArch>().unwrap(),
            TargetArch::Riscv32
        );
    }

    #[test]
    fn test_pointer_size() {
        assert!(TargetArch::X86_64.is_64bit());
        assert!(TargetArch::Aarch64.is_64bit());
        assert!(TargetArch::Riscv64.is_64bit());

        assert!(TargetArch::X86.is_32bit());
        assert!(TargetArch::Arm.is_32bit());
        assert!(TargetArch::Riscv32.is_32bit());
    }

    #[test]
    fn test_target_config() {
        let config_64 = TargetArch::X86_64.config();
        assert_eq!(config_64.pointer_bytes, 8);
        assert_eq!(config_64.value_bytes, 8);

        let config_32 = TargetArch::X86.config();
        assert_eq!(config_32.pointer_bytes, 4);
        assert_eq!(config_32.value_bytes, 8); // Still 64-bit values
    }

    #[test]
    fn test_parse_target() {
        let target = Target::parse("x86_64-linux").unwrap();
        assert_eq!(target.arch, TargetArch::X86_64);
        assert_eq!(target.os, TargetOS::Linux);

        let target = Target::parse("aarch64-macos").unwrap();
        assert_eq!(target.arch, TargetArch::Aarch64);
        assert_eq!(target.os, TargetOS::MacOS);
    }

    #[test]
    fn test_target_display() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert_eq!(format!("{}", target), "x86_64-linux");
    }
}
