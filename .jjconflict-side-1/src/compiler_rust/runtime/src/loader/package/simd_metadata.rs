use simple_simd::SimdTier;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantMetadata {
    pub target_triple: Option<String>,
    pub simd_tier: SimdTier,
}

impl Default for VariantMetadata {
    fn default() -> Self {
        Self {
            target_triple: None,
            simd_tier: SimdTier::Scalar,
        }
    }
}

impl VariantMetadata {
    pub fn validate_host(&self, target_triple: Option<&str>, simd_tier: SimdTier) -> Result<(), String> {
        if let Some(expected) = self.target_triple.as_deref() {
            if let Some(actual) = target_triple {
                if expected != actual {
                    return Err(format!(
                        "package target triple mismatch: expected {expected}, got {actual}"
                    ));
                }
            }
        }

        if !self.simd_tier.compatible_with(simd_tier) {
            return Err(format!(
                "package SIMD tier mismatch: package {}, host {}",
                self.simd_tier, simd_tier
            ));
        }

        Ok(())
    }
}
