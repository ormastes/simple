//! SIMD Feature Detection
//!
//! This module provides runtime detection of CPU SIMD capabilities.

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
            fma: true, // NEON includes FMA
            neon: true, // NEON is always available on AArch64
        }
    }

    /// Fallback for unsupported architectures.
    #[cfg(not(any(target_arch = "x86_64", target_arch = "x86", target_arch = "aarch64")))]
    pub fn detect() -> Self {
        SimdFeatures::default()
    }

    /// Check if any SIMD is available.
    pub fn has_simd(&self) -> bool {
        self.sse2 || self.neon
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
}
