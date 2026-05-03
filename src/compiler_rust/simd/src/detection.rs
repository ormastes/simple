//! SIMD feature and profile detection.
//!
//! This module provides runtime detection of CPU SIMD capabilities together
//! with one canonical tier model used by the stdlib, loader, and caches.

use std::fmt;
use std::str::FromStr;

/// Canonical SIMD tier used across packaging, loader selection, and runtime
/// capability reporting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SimdTier {
    /// Baseline scalar implementation.
    #[default]
    Scalar,
    /// x86_64 with SSE2.
    X86_64Sse2,
    /// x86_64 with AVX2.
    X86_64Avx2,
    /// x86_64 with AVX-512.
    X86_64Avx512,
    /// AArch64 with NEON.
    Aarch64Neon,
    /// AArch64 with SVE.
    Aarch64Sve,
    /// AArch64 with SVE2.
    Aarch64Sve2,
    /// RISC-V 64 with vector extension.
    Riscv64Rvv,
    /// WebAssembly SIMD128.
    Wasm128,
}

impl SimdTier {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Scalar => "scalar",
            Self::X86_64Sse2 => "x86_64_sse2",
            Self::X86_64Avx2 => "x86_64_avx2",
            Self::X86_64Avx512 => "x86_64_avx512",
            Self::Aarch64Neon => "aarch64_neon",
            Self::Aarch64Sve => "aarch64_sve",
            Self::Aarch64Sve2 => "aarch64_sve2",
            Self::Riscv64Rvv => "riscv64_rvv",
            Self::Wasm128 => "wasm128",
        }
    }

    pub const fn is_scalar(self) -> bool {
        matches!(self, Self::Scalar)
    }

    pub const fn family(self) -> &'static str {
        match self {
            Self::Scalar => "scalar",
            Self::X86_64Sse2 | Self::X86_64Avx2 | Self::X86_64Avx512 => "x86_64",
            Self::Aarch64Neon | Self::Aarch64Sve | Self::Aarch64Sve2 => "aarch64",
            Self::Riscv64Rvv => "riscv64",
            Self::Wasm128 => "wasm",
        }
    }

    pub fn compatible_with(self, host: SimdTier) -> bool {
        if matches!(self, Self::Scalar) {
            return true;
        }
        if self.family() != host.family() {
            return false;
        }
        self.rank() <= host.rank()
    }

    pub const fn rank(self) -> u8 {
        match self {
            Self::Scalar => 0,
            Self::X86_64Sse2 => 1,
            Self::X86_64Avx2 => 2,
            Self::X86_64Avx512 => 3,
            Self::Aarch64Neon => 1,
            Self::Aarch64Sve => 2,
            Self::Aarch64Sve2 => 3,
            Self::Riscv64Rvv => 1,
            Self::Wasm128 => 1,
        }
    }

    pub fn compatible_fallbacks(self) -> &'static [SimdTier] {
        match self {
            Self::Scalar => &[Self::Scalar],
            Self::X86_64Sse2 => &[Self::X86_64Sse2, Self::Scalar],
            Self::X86_64Avx2 => &[Self::X86_64Avx2, Self::X86_64Sse2, Self::Scalar],
            Self::X86_64Avx512 => &[Self::X86_64Avx512, Self::X86_64Avx2, Self::X86_64Sse2, Self::Scalar],
            Self::Aarch64Neon => &[Self::Aarch64Neon, Self::Scalar],
            Self::Aarch64Sve => &[Self::Aarch64Sve, Self::Aarch64Neon, Self::Scalar],
            Self::Aarch64Sve2 => &[Self::Aarch64Sve2, Self::Aarch64Sve, Self::Aarch64Neon, Self::Scalar],
            Self::Riscv64Rvv => &[Self::Riscv64Rvv, Self::Scalar],
            Self::Wasm128 => &[Self::Wasm128, Self::Scalar],
        }
    }

    pub fn best_available_implementation(self) -> SimdTier {
        match self {
            Self::X86_64Avx512 => Self::X86_64Avx2,
            Self::Aarch64Sve | Self::Aarch64Sve2 => Self::Aarch64Neon,
            Self::Wasm128 => Self::Scalar,
            other => other,
        }
    }
}

impl fmt::Display for SimdTier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for SimdTier {
    type Err = &'static str;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value.trim() {
            "scalar" => Ok(Self::Scalar),
            "x86_64_sse2" | "sse2" => Ok(Self::X86_64Sse2),
            "x86_64_avx512" | "avx512" => Ok(Self::X86_64Avx512),
            "x86_64_avx2" => Ok(Self::X86_64Avx2),
            "avx2" => Ok(Self::X86_64Avx2),
            "aarch64_neon" | "neon" => Ok(Self::Aarch64Neon),
            "aarch64_sve" | "sve" => Ok(Self::Aarch64Sve),
            "aarch64_sve2" | "sve2" => Ok(Self::Aarch64Sve2),
            "riscv64_rvv" => Ok(Self::Riscv64Rvv),
            "rvv" => Ok(Self::Riscv64Rvv),
            "wasm128" | "wasm_simd128" => Ok(Self::Wasm128),
            _ => Err("unknown SIMD tier"),
        }
    }
}

/// SIMD feature flags.
#[derive(Debug, Clone, Copy, Default)]
pub struct SimdFeatures {
    /// SSE support (128-bit vectors).
    pub sse: bool,
    /// SSE2 support.
    pub sse2: bool,
    /// SSE3 support.
    pub sse3: bool,
    /// SSSE3 support.
    pub ssse3: bool,
    /// SSE4.1 support.
    pub sse4_1: bool,
    /// SSE4.2 support.
    pub sse4_2: bool,
    /// AVX support (256-bit vectors).
    pub avx: bool,
    /// AVX2 support.
    pub avx2: bool,
    /// AVX-512F support (512-bit vectors).
    pub avx512f: bool,
    /// FMA support (fused multiply-add).
    pub fma: bool,
    /// ARM NEON support.
    pub neon: bool,
    /// ARM SVE support.
    pub sve: bool,
    /// ARM SVE2 support.
    pub sve2: bool,
    /// RISC-V Vector extension support.
    pub rvv: bool,
    /// WebAssembly SIMD128 support.
    pub wasm128: bool,
}

impl SimdFeatures {
    /// Detect SIMD features at runtime.
    #[cfg(target_arch = "x86_64")]
    pub fn detect() -> Self {
        SimdFeatures {
            sse: std::is_x86_feature_detected!("sse"),
            sse2: std::is_x86_feature_detected!("sse2"),
            sse3: std::is_x86_feature_detected!("sse3"),
            ssse3: std::is_x86_feature_detected!("ssse3"),
            sse4_1: std::is_x86_feature_detected!("sse4.1"),
            sse4_2: std::is_x86_feature_detected!("sse4.2"),
            avx: std::is_x86_feature_detected!("avx"),
            avx2: std::is_x86_feature_detected!("avx2"),
            avx512f: std::is_x86_feature_detected!("avx512f"),
            fma: std::is_x86_feature_detected!("fma"),
            neon: false,
            sve: false,
            sve2: false,
            rvv: false,
            wasm128: false,
        }
    }

    /// Detect SIMD features at runtime.
    #[cfg(target_arch = "x86")]
    pub fn detect() -> Self {
        SimdFeatures {
            sse: std::is_x86_feature_detected!("sse"),
            sse2: std::is_x86_feature_detected!("sse2"),
            sse3: std::is_x86_feature_detected!("sse3"),
            ssse3: std::is_x86_feature_detected!("ssse3"),
            sse4_1: std::is_x86_feature_detected!("sse4.1"),
            sse4_2: std::is_x86_feature_detected!("sse4.2"),
            avx: std::is_x86_feature_detected!("avx"),
            avx2: std::is_x86_feature_detected!("avx2"),
            avx512f: false, // AVX-512 not available on 32-bit
            fma: std::is_x86_feature_detected!("fma"),
            neon: false,
            sve: false,
            sve2: false,
            rvv: false,
            wasm128: false,
        }
    }

    /// Detect SIMD features at runtime (ARM).
    #[cfg(target_arch = "aarch64")]
    pub fn detect() -> Self {
        SimdFeatures {
            sse: false,
            sse2: false,
            sse3: false,
            ssse3: false,
            sse4_1: false,
            sse4_2: false,
            avx: false,
            avx2: false,
            avx512f: false,
            fma: true,  // NEON includes FMA
            neon: true, // NEON is always available on AArch64
            sve: cfg!(target_feature = "sve"),
            sve2: cfg!(target_feature = "sve2"),
            rvv: false,
            wasm128: false,
        }
    }

    /// Detect SIMD features at runtime (RISC-V 64).
    #[cfg(target_arch = "riscv64")]
    pub fn detect() -> Self {
        SimdFeatures {
            sse: false,
            sse2: false,
            sse3: false,
            ssse3: false,
            sse4_1: false,
            sse4_2: false,
            avx: false,
            avx2: false,
            avx512f: false,
            fma: false,
            neon: false,
            sve: false,
            sve2: false,
            rvv: cfg!(target_feature = "v"),
            wasm128: false,
        }
    }

    /// Detect SIMD features at runtime (WASM).
    #[cfg(target_arch = "wasm32")]
    pub fn detect() -> Self {
        SimdFeatures {
            sse: false,
            sse2: false,
            sse3: false,
            ssse3: false,
            sse4_1: false,
            sse4_2: false,
            avx: false,
            avx2: false,
            avx512f: false,
            fma: false,
            neon: false,
            sve: false,
            sve2: false,
            rvv: false,
            wasm128: cfg!(target_feature = "simd128"),
        }
    }

    /// Fallback for unsupported architectures.
    #[cfg(not(any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "wasm32"
    )))]
    pub fn detect() -> Self {
        SimdFeatures::default()
    }

    /// Get the canonical SIMD tier for this host.
    pub fn detect_profile(&self) -> SimdTier {
        if self.avx512f {
            SimdTier::X86_64Avx512
        } else if self.avx2 {
            SimdTier::X86_64Avx2
        } else if self.sse2 {
            SimdTier::X86_64Sse2
        } else if self.sve2 {
            SimdTier::Aarch64Sve2
        } else if self.sve {
            SimdTier::Aarch64Sve
        } else if self.neon {
            SimdTier::Aarch64Neon
        } else if self.rvv {
            SimdTier::Riscv64Rvv
        } else if self.wasm128 {
            SimdTier::Wasm128
        } else {
            SimdTier::Scalar
        }
    }

    /// Check if any SIMD is available.
    pub fn has_simd(&self) -> bool {
        self.sse2 || self.neon || self.sve || self.sve2 || self.rvv || self.wasm128
    }

    /// Check if 256-bit vectors are available.
    pub fn has_256bit(&self) -> bool {
        self.avx
    }

    /// Check if 512-bit vectors are available.
    pub fn has_512bit(&self) -> bool {
        self.avx512f
    }

    /// Get the preferred vector width for f32 in lanes.
    pub fn preferred_f32_width(&self) -> usize {
        if self.avx512f {
            16
        } else if self.avx {
            8
        } else if self.sse2 || self.neon {
            4
        } else {
            1 // Scalar fallback
        }
    }

    /// Get the preferred vector width for f64 in lanes.
    pub fn preferred_f64_width(&self) -> usize {
        if self.avx512f {
            8
        } else if self.avx {
            4
        } else if self.sse2 || self.neon {
            2
        } else {
            1
        }
    }

    /// Get the preferred vector width for i32 in lanes.
    pub fn preferred_i32_width(&self) -> usize {
        self.preferred_f32_width()
    }
}

/// Get the preferred SIMD width for a given element type.
pub fn preferred_width<T>() -> usize {
    let features = SimdFeatures::detect();

    let size = std::mem::size_of::<T>();
    match size {
        4 => features.preferred_f32_width(),
        8 => features.preferred_f64_width(),
        2 => features.preferred_f32_width() * 2,
        1 => features.preferred_f32_width() * 4,
        _ => 1,
    }
}

/// Check if SIMD is available on this platform.
pub fn simd_available() -> bool {
    SimdFeatures::detect().has_simd()
}

/// Detect the canonical SIMD tier for the current host.
pub fn detect_profile() -> SimdTier {
    SimdFeatures::detect().detect_profile()
}

/// Resolve the active SIMD tier after env/config downscoping.
pub fn active_profile() -> SimdTier {
    crate::host_config::active_simd_tier()
}

/// Get the canonical SIMD tier name for the current host.
pub fn profile_name() -> &'static str {
    detect_profile().as_str()
}

/// Get the active SIMD tier name after env/config downscoping.
pub fn active_profile_name() -> &'static str {
    active_profile().as_str()
}

/// Check if AVX (256-bit) is available.
pub fn has_avx() -> bool {
    SimdFeatures::detect().avx
}

/// Check if AVX2 is available.
pub fn has_avx2() -> bool {
    SimdFeatures::detect().avx2
}

/// Check if AVX-512 is available.
pub fn has_avx512() -> bool {
    SimdFeatures::detect().avx512f
}

/// Check if FMA (fused multiply-add) is available.
pub fn has_fma() -> bool {
    SimdFeatures::detect().fma
}

/// Check if ARM NEON is available.
pub fn has_neon() -> bool {
    SimdFeatures::detect().neon
}

/// Check if RISC-V vector support is available.
pub fn has_rvv() -> bool {
    SimdFeatures::detect().rvv
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_feature_detection() {
        let features = SimdFeatures::detect();

        // On any modern x86_64 or ARM64, we should have some SIMD
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        assert!(features.has_simd());

        println!("SIMD Features: {:?}", features);
        println!("Preferred f32 width: {}", features.preferred_f32_width());
        println!("Preferred f64 width: {}", features.preferred_f64_width());
    }

    #[test]
    fn test_preferred_width() {
        let width = preferred_width::<f32>();
        assert!(width >= 1);
        assert!(width <= 16);
    }

    #[test]
    fn test_simd_available() {
        // This should work on any supported platform
        let available = simd_available();
        println!("SIMD available: {}", available);
    }

    #[test]
    fn test_profile_roundtrip() {
        for value in [
            "scalar",
            "x86_64_sse2",
            "x86_64_avx2",
            "x86_64_avx512",
            "aarch64_neon",
            "aarch64_sve",
            "aarch64_sve2",
            "riscv64_rvv",
            "wasm128",
        ] {
            let tier = SimdTier::from_str(value).expect("parse tier");
            assert_eq!(tier.as_str(), value);
        }
    }

    #[test]
    fn test_detect_profile_matches_feature_flags() {
        let features = SimdFeatures::detect();
        let profile = features.detect_profile();
        if features.avx512f {
            assert_eq!(profile, SimdTier::X86_64Avx512);
        } else if features.avx2 {
            assert_eq!(profile, SimdTier::X86_64Avx2);
        } else if features.sse2 {
            assert_eq!(profile, SimdTier::X86_64Sse2);
        } else if features.sve2 {
            assert_eq!(profile, SimdTier::Aarch64Sve2);
        } else if features.sve {
            assert_eq!(profile, SimdTier::Aarch64Sve);
        } else if features.neon {
            assert_eq!(profile, SimdTier::Aarch64Neon);
        } else if features.rvv {
            assert_eq!(profile, SimdTier::Riscv64Rvv);
        } else if features.wasm128 {
            assert_eq!(profile, SimdTier::Wasm128);
        } else {
            assert_eq!(profile, SimdTier::Scalar);
        }
    }

    #[test]
    fn test_compatibility_ordering() {
        assert!(SimdTier::X86_64Sse2.compatible_with(SimdTier::X86_64Avx2));
        assert!(SimdTier::X86_64Avx2.compatible_with(SimdTier::X86_64Avx512));
        assert!(!SimdTier::X86_64Avx512.compatible_with(SimdTier::X86_64Avx2));
        assert!(SimdTier::Aarch64Sve.compatible_with(SimdTier::Aarch64Sve2));
        assert!(SimdTier::Aarch64Neon.compatible_with(SimdTier::Aarch64Sve2));
        assert!(!SimdTier::Aarch64Neon.compatible_with(SimdTier::X86_64Avx2));
        assert!(SimdTier::Scalar.compatible_with(SimdTier::Riscv64Rvv));
    }

    #[test]
    fn test_fallback_ordering() {
        assert_eq!(
            SimdTier::X86_64Avx512.compatible_fallbacks(),
            &[
                SimdTier::X86_64Avx512,
                SimdTier::X86_64Avx2,
                SimdTier::X86_64Sse2,
                SimdTier::Scalar,
            ]
        );
        assert_eq!(
            SimdTier::Aarch64Sve2.compatible_fallbacks(),
            &[
                SimdTier::Aarch64Sve2,
                SimdTier::Aarch64Sve,
                SimdTier::Aarch64Neon,
                SimdTier::Scalar,
            ]
        );
    }
}
