//! Hardware-aware stdlib variant selection helpers.

use std::path::{Path, PathBuf};

use simple_simd::{active_simd_tier as resolved_active_simd_tier, SimdTier};

pub fn active_simd_tier() -> SimdTier {
    resolved_active_simd_tier()
}

pub fn active_simd_tier_name() -> &'static str {
    active_simd_tier().as_str()
}

pub fn stdlib_root_candidates(root: &Path) -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    let tier = active_simd_tier();

    for &fallback in tier.compatible_fallbacks() {
        if fallback.is_scalar() {
            continue;
        }
        append_tier_candidates(&mut candidates, root, fallback);
    }

    candidates.push(root.to_path_buf());
    candidates
}

fn append_tier_candidates(out: &mut Vec<PathBuf>, root: &Path, tier: SimdTier) {
    let tier_name = tier.as_str();
    let root_str = root.to_string_lossy().replace('\\', "/");

    let maybe_push = |out: &mut Vec<PathBuf>, candidate: PathBuf| {
        if !out.iter().any(|existing| existing == &candidate) {
            out.push(candidate);
        }
    };

    if root_str.ends_with("/src/lib/std/src")
        || root_str.ends_with("/simple/std_lib/src")
        || root_str.ends_with("/std_lib/src")
    {
        if let Some(parent) = root.parent() {
            maybe_push(out, parent.join("variants").join(tier_name).join("src"));
        }
    }

    if root_str.ends_with("/src/lib") || root_str.ends_with("/src/std") {
        maybe_push(out, root.join("variants").join(tier_name));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;
    use std::sync::{Mutex, OnceLock};
    use simple_simd::{host_cpu_config, reset_host_cpu_config_cache_for_tests, HostCpuConfig};

    fn simd_tier_env_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    fn with_simd_envs<T>(simd_tier: Option<&str>, cpu_config_path: Option<&Path>, f: impl FnOnce() -> T) -> T {
        let _guard = simd_tier_env_lock().lock().unwrap();
        let previous_simd_tier = std::env::var("SIMPLE_SIMD_TIER").ok();
        let previous_cpu_config_path = std::env::var("SIMPLE_CPU_CONFIG_PATH").ok();

        match simd_tier {
            Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
            None => std::env::remove_var("SIMPLE_SIMD_TIER"),
        }

        match cpu_config_path {
            Some(path) => std::env::set_var("SIMPLE_CPU_CONFIG_PATH", path),
            None => std::env::remove_var("SIMPLE_CPU_CONFIG_PATH"),
        }

        reset_host_cpu_config_cache_for_tests();
        let result = f();
        reset_host_cpu_config_cache_for_tests();

        match previous_simd_tier.as_deref() {
            Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
            None => std::env::remove_var("SIMPLE_SIMD_TIER"),
        }

        match previous_cpu_config_path.as_deref() {
            Some(value) => std::env::set_var("SIMPLE_CPU_CONFIG_PATH", value),
            None => std::env::remove_var("SIMPLE_CPU_CONFIG_PATH"),
        }
        reset_host_cpu_config_cache_for_tests();
        result
    }

    fn with_simd_tier_env<T>(value: Option<&str>, f: impl FnOnce() -> T) -> T {
        with_simd_envs(value, None, f)
    }

    fn render_string_list(values: &[String]) -> String {
        format!(
            "[{}]",
            values
                .iter()
                .map(|value| format!("\"{value}\""))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn render_tier_list(values: &[SimdTier]) -> String {
        format!(
            "[{}]",
            values
                .iter()
                .map(|value| format!("\"{}\"", value.as_str()))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn instruction_sets_for_tier(tier: SimdTier) -> &'static [&'static str] {
        match tier {
            SimdTier::Scalar => &[],
            SimdTier::X86_64Sse2 => &["sse2"],
            SimdTier::X86_64Avx2 => &["sse2", "avx2"],
            SimdTier::X86_64Avx512 => &["sse2", "avx2", "avx512f"],
            SimdTier::Aarch64Neon => &["neon"],
            SimdTier::Aarch64Sve => &["neon", "sve"],
            SimdTier::Aarch64Sve2 => &["neon", "sve", "sve2"],
            SimdTier::Riscv64Rvv => &["rvv"],
            SimdTier::Wasm128 => &["wasm128"],
        }
    }

    fn config_document(base: &HostCpuConfig, enabled_tier: SimdTier) -> String {
        let enabled_instruction_sets = instruction_sets_for_tier(enabled_tier)
            .iter()
            .filter(|instruction_set| {
                base.simple_support
                    .instruction_sets
                    .iter()
                    .any(|supported| supported == **instruction_set)
            })
            .map(|instruction_set| (*instruction_set).to_string())
            .collect::<Vec<_>>();

        format!(
            concat!(
                "version: 1\n",
                "target_triple: \"{}\"\n",
                "generated_by: \"test\"\n",
                "support:\n",
                "    simd_tier: \"{}\"\n",
                "    instruction_sets: {}\n",
                "simple_support:\n",
                "    simd_tier_fallbacks: {}\n",
                "    instruction_sets: {}\n",
                "enabled:\n",
                "    simd_tier: \"{}\"\n",
                "    instruction_sets: {}\n"
            ),
            base.target_triple,
            base.support.simd_tier.as_str(),
            render_string_list(&base.support.instruction_sets),
            render_tier_list(&base.simple_support.simd_tier_fallbacks),
            render_string_list(&base.simple_support.instruction_sets),
            enabled_tier.as_str(),
            render_string_list(&enabled_instruction_sets),
        )
    }

    fn base_host_config() -> (tempfile::TempDir, HostCpuConfig) {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("seed_cpu_config.sdn");
        let base = with_simd_envs(None, Some(&path), || host_cpu_config().unwrap());
        (temp, base)
    }

    #[test]
    fn scalar_roots_keep_baseline_only() {
        with_simd_tier_env(Some("scalar"), || {
            let roots = stdlib_root_candidates(Path::new("/tmp/proj/src/lib"));
            assert_eq!(roots, vec![PathBuf::from("/tmp/proj/src/lib")]);
        });
    }

    #[test]
    fn variant_roots_prepend_tier_specific_tree() {
        with_simd_tier_env(Some("x86_64_avx512"), || {
            let roots = stdlib_root_candidates(Path::new("/tmp/proj/src/lib/std/src"));
            assert_eq!(
                roots,
                vec![
                    PathBuf::from("/tmp/proj/src/lib/std/variants/x86_64_avx512/src"),
                    PathBuf::from("/tmp/proj/src/lib/std/variants/x86_64_avx2/src"),
                    PathBuf::from("/tmp/proj/src/lib/std/variants/x86_64_sse2/src"),
                    PathBuf::from("/tmp/proj/src/lib/std/src"),
                ]
            );
        });
    }

    #[test]
    fn simple_std_lib_layout_uses_variant_src_tree() {
        with_simd_tier_env(Some("x86_64_avx2"), || {
            let roots = stdlib_root_candidates(Path::new("/tmp/proj/simple/std_lib/src"));
            assert_eq!(
                roots,
                vec![
                    PathBuf::from("/tmp/proj/simple/std_lib/variants/x86_64_avx2/src"),
                    PathBuf::from("/tmp/proj/simple/std_lib/variants/x86_64_sse2/src"),
                    PathBuf::from("/tmp/proj/simple/std_lib/src"),
                ]
            );
        });
    }

    #[test]
    fn source_std_layout_uses_variant_directory() {
        with_simd_tier_env(Some("x86_64_avx2"), || {
            let roots = stdlib_root_candidates(Path::new("/tmp/proj/src/std"));
            assert_eq!(
                roots,
                vec![
                    PathBuf::from("/tmp/proj/src/std/variants/x86_64_avx2"),
                    PathBuf::from("/tmp/proj/src/std/variants/x86_64_sse2"),
                    PathBuf::from("/tmp/proj/src/std"),
                ]
            );
        });
    }

    #[test]
    fn config_enabled_tier_is_used_without_override() {
        let (temp, base) = base_host_config();
        let path = temp.path().join("configured_cpu_config.sdn");
        let configured_tier = base
            .simple_support
            .simd_tier_fallbacks
            .iter()
            .rev()
            .copied()
            .find(|tier| *tier != base.enabled.simd_tier)
            .unwrap_or(base.enabled.simd_tier);
        fs::write(&path, config_document(&base, configured_tier)).unwrap();

        with_simd_envs(None, Some(&path), || {
            assert_eq!(active_simd_tier(), configured_tier);
            assert_eq!(active_simd_tier_name(), configured_tier.as_str());
        });
    }

    #[test]
    fn explicit_override_takes_precedence_over_config_enabled_tier() {
        let (temp, base) = base_host_config();
        let path = temp.path().join("configured_cpu_config.sdn");
        let configured_tier = base
            .simple_support
            .simd_tier_fallbacks
            .iter()
            .rev()
            .copied()
            .find(|tier| *tier != base.enabled.simd_tier)
            .unwrap_or(base.enabled.simd_tier);
        fs::write(&path, config_document(&base, configured_tier)).unwrap();

        with_simd_envs(Some(base.enabled.simd_tier.as_str()), Some(&path), || {
            assert_eq!(active_simd_tier(), base.enabled.simd_tier);
            assert_eq!(active_simd_tier_name(), base.enabled.simd_tier.as_str());
        });
    }

    #[test]
    fn invalid_override_falls_back_to_configured_enabled_tier() {
        let (temp, base) = base_host_config();
        let path = temp.path().join("configured_cpu_config.sdn");
        let configured_tier = base
            .simple_support
            .simd_tier_fallbacks
            .iter()
            .rev()
            .copied()
            .find(|tier| *tier != base.enabled.simd_tier)
            .unwrap_or(base.enabled.simd_tier);
        fs::write(&path, config_document(&base, configured_tier)).unwrap();

        with_simd_envs(Some("definitely-not-a-tier"), Some(&path), || {
            assert_eq!(active_simd_tier(), configured_tier);
            assert_eq!(active_simd_tier_name(), configured_tier.as_str());
        });
    }

    #[test]
    fn configured_enabled_tier_changes_stdlib_root_order_without_override() {
        let (temp, base) = base_host_config();
        let path = temp.path().join("configured_cpu_config.sdn");
        let configured_tier = base
            .simple_support
            .simd_tier_fallbacks
            .iter()
            .rev()
            .copied()
            .find(|tier| !tier.is_scalar())
            .unwrap_or(base.enabled.simd_tier);
        fs::write(&path, config_document(&base, configured_tier)).unwrap();

        with_simd_envs(None, Some(&path), || {
            assert_eq!(active_simd_tier(), configured_tier);
            let roots = stdlib_root_candidates(Path::new("/tmp/proj/src/lib/std/src"));
            let mut expected = configured_tier
                .compatible_fallbacks()
                .iter()
                .filter(|tier| !tier.is_scalar())
                .map(|tier| PathBuf::from(format!("/tmp/proj/src/lib/std/variants/{}/src", tier.as_str())))
                .collect::<Vec<_>>();
            expected.push(PathBuf::from("/tmp/proj/src/lib/std/src"));
            assert_eq!(roots, expected);
        });
    }
}
