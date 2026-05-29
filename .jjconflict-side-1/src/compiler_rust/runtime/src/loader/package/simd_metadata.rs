use simple_simd::SimdTier;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantMetadata {
    pub target_triple: Option<String>,
    pub simd_tier: SimdTier,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeVariantResource {
    pub target_triple: String,
    pub simd_tier: SimdTier,
    pub resource_path: String,
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

pub fn select_best_runtime_variant<'a>(
    variants: &'a [RuntimeVariantResource],
    target_triple: &str,
    simd_tier: SimdTier,
) -> Option<&'a RuntimeVariantResource> {
    for fallback in simd_tier.compatible_fallbacks() {
        let fallback = fallback.best_available_implementation();
        if let Some(entry) = variants
            .iter()
            .find(|entry| runtime_variant_matches(entry, target_triple, fallback))
        {
            return Some(entry);
        }
    }
    None
}

pub fn runtime_variant_matches(entry: &RuntimeVariantResource, target_triple: &str, simd_tier: SimdTier) -> bool {
    !entry.resource_path.is_empty()
        && entry.target_triple == target_triple
        && entry.simd_tier.best_available_implementation() == simd_tier
}
