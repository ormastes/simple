use simple_common::Target;
use simple_sdn::{parse_document, SdnValue};
use std::collections::BTreeSet;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use crate::{detect_profile, SimdFeatures, SimdTier};

const CPU_CONFIG_FILE_NAME: &str = "cpu_config.sdn";
const SIMPLE_CPU_CONFIG_PATH: &str = "SIMPLE_CPU_CONFIG_PATH";
const SIMPLE_SUPPORT_INSTRUCTION_SETS: &[&str] = &["sse2", "avx2", "avx512f", "neon", "sve", "sve2", "rvv", "wasm128"];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpuCapabilitySection {
    pub simd_tier: SimdTier,
    pub instruction_sets: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpleSupportSection {
    pub simd_tier_fallbacks: Vec<SimdTier>,
    pub instruction_sets: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostCpuConfig {
    pub version: i64,
    pub target_triple: String,
    pub generated_by: String,
    pub support: CpuCapabilitySection,
    pub simple_support: SimpleSupportSection,
    pub enabled: CpuCapabilitySection,
}

#[derive(Debug)]
pub enum HostCpuConfigError {
    Io(std::io::Error),
    Parse(String),
    MissingPath,
}

impl fmt::Display for HostCpuConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(err) => write!(f, "I/O error: {err}"),
            Self::Parse(err) => write!(f, "parse error: {err}"),
            Self::MissingPath => write!(f, "could not determine CPU config path"),
        }
    }
}

impl std::error::Error for HostCpuConfigError {}

impl From<std::io::Error> for HostCpuConfigError {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

#[derive(Clone)]
struct CachedConfig {
    path: PathBuf,
    source: Option<String>,
    config: HostCpuConfig,
}

fn config_cache() -> &'static Mutex<Option<CachedConfig>> {
    static CACHE: OnceLock<Mutex<Option<CachedConfig>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(None))
}

#[doc(hidden)]
pub fn reset_host_cpu_config_cache_for_tests() {
    *config_cache().lock().unwrap() = None;
}

pub fn active_simd_tier() -> SimdTier {
    if let Ok(value) = std::env::var("SIMPLE_SIMD_TIER") {
        if let Ok(tier) = value.parse::<SimdTier>() {
            return tier;
        }
    }

    host_cpu_config()
        .map(|config| config.enabled.simd_tier)
        .unwrap_or_else(|_| detect_profile().best_available_implementation())
}

pub fn host_cpu_config() -> Result<HostCpuConfig, HostCpuConfigError> {
    let path = cpu_config_path().ok_or(HostCpuConfigError::MissingPath)?;
    let source = config_file_source(&path)?;
    let mut guard = config_cache().lock().unwrap();
    if let Some(cached) = guard.as_ref() {
        if cached.path == path && cached.source == source {
            return Ok(cached.config.clone());
        }
    }

    let config = load_or_initialize_config(&path)?;
    let source = config_file_source(&path)?;
    *guard = Some(CachedConfig {
        path,
        source,
        config: config.clone(),
    });
    Ok(config)
}

pub fn cpu_config_path() -> Option<PathBuf> {
    if let Ok(path) = std::env::var(SIMPLE_CPU_CONFIG_PATH) {
        let trimmed = path.trim();
        if !trimmed.is_empty() {
            return Some(PathBuf::from(trimmed));
        }
    }

    let triple = Target::host().triple_str();
    if let Some(cache_dir) = dirs_next::cache_dir() {
        return Some(
            cache_dir
                .join("simple")
                .join("host")
                .join(triple)
                .join(CPU_CONFIG_FILE_NAME),
        );
    }
    let home = dirs_next::home_dir()?;
    Some(
        home.join(".simple")
            .join("cache")
            .join("host")
            .join(triple)
            .join(CPU_CONFIG_FILE_NAME),
    )
}

fn load_or_initialize_config(path: &Path) -> Result<HostCpuConfig, HostCpuConfigError> {
    let detected = detected_config();
    if path.exists() {
        let source = fs::read_to_string(path)?;
        let parsed = parse_config_document(&source, &detected)?;
        let canonical = canonicalize_enabled(parsed.clone(), &detected);
        let _changed = canonical != parsed;
        write_config(path, &canonical)?;
        return Ok(canonical);
    }

    write_config(path, &detected)?;
    Ok(detected)
}

fn config_file_source(path: &Path) -> Result<Option<String>, HostCpuConfigError> {
    match fs::read_to_string(path) {
        Ok(source) => Ok(Some(source)),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(err) => Err(err.into()),
    }
}

fn detected_config() -> HostCpuConfig {
    let host_tier = detect_profile();
    let support_instruction_sets = detected_instruction_sets(SimdFeatures::detect());
    let simple_support_tiers = simple_supported_tiers_for_host(host_tier);
    let simple_support_instruction_sets = supported_instruction_sets_for_tiers(&simple_support_tiers)
        .into_iter()
        .filter(|value| support_instruction_sets.iter().any(|supported| supported == value))
        .map(str::to_string)
        .collect::<Vec<_>>();
    let enabled_instruction_sets =
        intersect_instruction_sets_in_canonical_order(&support_instruction_sets, &simple_support_instruction_sets);

    HostCpuConfig {
        version: 1,
        target_triple: Target::host().triple_str().to_string(),
        generated_by: format!("simple-simd {}", env!("CARGO_PKG_VERSION")),
        support: CpuCapabilitySection {
            simd_tier: host_tier,
            instruction_sets: support_instruction_sets.clone(),
        },
        simple_support: SimpleSupportSection {
            simd_tier_fallbacks: simple_support_tiers.clone(),
            instruction_sets: simple_support_instruction_sets,
        },
        enabled: CpuCapabilitySection {
            simd_tier: simple_support_tiers.first().copied().unwrap_or(SimdTier::Scalar),
            instruction_sets: enabled_instruction_sets,
        },
    }
}

fn parse_config_document(source: &str, detected: &HostCpuConfig) -> Result<HostCpuConfig, HostCpuConfigError> {
    let doc = parse_document(source).map_err(|err| HostCpuConfigError::Parse(err.to_string()))?;
    let version = doc.get("version").and_then(SdnValue::as_i64).unwrap_or(1);
    let target_triple = doc
        .get("target_triple")
        .and_then(SdnValue::as_str)
        .unwrap_or(&detected.target_triple)
        .to_string();
    let generated_by = doc
        .get("generated_by")
        .and_then(SdnValue::as_str)
        .unwrap_or(&detected.generated_by)
        .to_string();

    let support = parse_capability_section(
        doc.get("support"),
        detected.support.simd_tier,
        &detected.support.instruction_sets,
    );
    let simple_support = parse_simple_support_section(doc.get("simple_support"), &detected.simple_support);
    let enabled = parse_capability_section(
        doc.get("enabled"),
        detected.enabled.simd_tier,
        &detected.enabled.instruction_sets,
    );

    Ok(HostCpuConfig {
        version,
        target_triple,
        generated_by,
        support,
        simple_support,
        enabled,
    })
}

fn parse_capability_section(
    value: Option<&SdnValue>,
    default_tier: SimdTier,
    default_instruction_sets: &[String],
) -> CpuCapabilitySection {
    let Some(value) = value else {
        return CpuCapabilitySection {
            simd_tier: default_tier,
            instruction_sets: default_instruction_sets.to_vec(),
        };
    };
    let simd_tier = value
        .get("simd_tier")
        .and_then(SdnValue::as_str)
        .and_then(|raw| raw.parse::<SimdTier>().ok())
        .unwrap_or(default_tier);
    let instruction_sets = value
        .get("instruction_sets")
        .and_then(string_array)
        .unwrap_or_else(|| default_instruction_sets.to_vec());
    CpuCapabilitySection {
        simd_tier,
        instruction_sets,
    }
}

fn parse_simple_support_section(value: Option<&SdnValue>, detected: &SimpleSupportSection) -> SimpleSupportSection {
    let Some(value) = value else {
        return detected.clone();
    };
    let simd_tier_fallbacks = value
        .get("simd_tier_fallbacks")
        .and_then(simd_tier_array)
        .unwrap_or_else(|| detected.simd_tier_fallbacks.clone());
    let instruction_sets = value
        .get("instruction_sets")
        .and_then(string_array)
        .unwrap_or_else(|| detected.instruction_sets.clone());
    SimpleSupportSection {
        simd_tier_fallbacks,
        instruction_sets,
    }
}

fn canonicalize_enabled(mut parsed: HostCpuConfig, detected: &HostCpuConfig) -> HostCpuConfig {
    parsed.version = detected.version;
    parsed.target_triple = detected.target_triple.clone();
    parsed.generated_by = detected.generated_by.clone();
    parsed.support = detected.support.clone();
    parsed.simple_support = detected.simple_support.clone();

    let allowed_instruction_sets = allowed_instruction_sets_in_canonical_order(detected);
    let requested_instruction_sets = parsed.enabled.instruction_sets.clone();
    parsed.enabled.instruction_sets = allowed_instruction_sets
        .iter()
        .filter(|value| requested_instruction_sets.iter().any(|requested| requested == *value))
        .cloned()
        .collect();

    if parsed.enabled.instruction_sets.is_empty() && !allowed_instruction_sets.is_empty() {
        parsed.enabled.instruction_sets = allowed_instruction_sets;
    }

    parsed.enabled.simd_tier = select_enabled_tier(parsed.enabled.simd_tier, detected);
    parsed
}

fn select_enabled_tier(requested: SimdTier, detected: &HostCpuConfig) -> SimdTier {
    let requested = requested.best_available_implementation();
    let supported = &detected.simple_support.simd_tier_fallbacks;
    if supported.contains(&requested) {
        return requested;
    }
    supported.first().copied().unwrap_or(SimdTier::Scalar)
}

fn allowed_instruction_sets_in_canonical_order(config: &HostCpuConfig) -> Vec<String> {
    intersect_instruction_sets_in_canonical_order(
        &config.support.instruction_sets,
        &config.simple_support.instruction_sets,
    )
}

fn simple_supported_tiers_for_host(host_tier: SimdTier) -> Vec<SimdTier> {
    let mut tiers = Vec::new();
    for fallback in host_tier.compatible_fallbacks() {
        let fallback = fallback.best_available_implementation();
        if !tiers.contains(&fallback) {
            tiers.push(fallback);
        }
    }
    if tiers.is_empty() {
        tiers.push(SimdTier::Scalar);
    }
    tiers
}

fn detected_instruction_sets(features: SimdFeatures) -> Vec<String> {
    let mut instruction_sets = Vec::new();
    if features.sse2 {
        instruction_sets.push("sse2".to_string());
    }
    if features.avx2 {
        instruction_sets.push("avx2".to_string());
    }
    if features.avx512f {
        instruction_sets.push("avx512f".to_string());
    }
    if features.neon {
        instruction_sets.push("neon".to_string());
    }
    if features.sve {
        instruction_sets.push("sve".to_string());
    }
    if features.sve2 {
        instruction_sets.push("sve2".to_string());
    }
    if features.rvv {
        instruction_sets.push("rvv".to_string());
    }
    if features.wasm128 {
        instruction_sets.push("wasm128".to_string());
    }
    instruction_sets
}

fn supported_instruction_sets_for_tiers(tiers: &[SimdTier]) -> Vec<&'static str> {
    let mut instruction_sets = Vec::new();
    for tier in tiers {
        for instruction_set in instruction_sets_for_tier(*tier).iter().copied() {
            if !instruction_sets.contains(&instruction_set) {
                instruction_sets.push(instruction_set);
            }
        }
    }
    instruction_sets
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

fn intersect_instruction_sets_in_canonical_order(support: &[String], simple_support: &[String]) -> Vec<String> {
    let support = support.iter().map(String::as_str).collect::<BTreeSet<_>>();
    let simple_support = simple_support.iter().map(String::as_str).collect::<BTreeSet<_>>();
    SIMPLE_SUPPORT_INSTRUCTION_SETS
        .iter()
        .copied()
        .filter(|value| support.contains(value) && simple_support.contains(value))
        .map(str::to_string)
        .collect()
}

fn string_array(value: &SdnValue) -> Option<Vec<String>> {
    let array = value.as_array()?;
    let mut values = Vec::with_capacity(array.len());
    for entry in array {
        values.push(entry.as_str()?.to_string());
    }
    Some(values)
}

fn simd_tier_array(value: &SdnValue) -> Option<Vec<SimdTier>> {
    let array = value.as_array()?;
    let mut values = Vec::with_capacity(array.len());
    for entry in array {
        values.push(entry.as_str()?.parse().ok()?);
    }
    Some(values)
}

fn write_config(path: &Path, config: &HostCpuConfig) -> Result<(), HostCpuConfigError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, render_config(config))?;
    Ok(())
}

fn render_config(config: &HostCpuConfig) -> String {
    format!(
        concat!(
            "version: {}\n",
            "target_triple: {}\n",
            "generated_by: \"{}\"\n",
            "support:\n",
            "    simd_tier: {}\n",
            "    instruction_sets: {}\n",
            "simple_support:\n",
            "    simd_tier_fallbacks: {}\n",
            "    instruction_sets: {}\n",
            "enabled:\n",
            "    simd_tier: {}\n",
            "    instruction_sets: {}\n"
        ),
        config.version,
        quoted(&config.target_triple),
        config.generated_by,
        quoted(config.support.simd_tier.as_str()),
        render_string_list(&config.support.instruction_sets),
        render_tier_list(&config.simple_support.simd_tier_fallbacks),
        render_string_list(&config.simple_support.instruction_sets),
        quoted(config.enabled.simd_tier.as_str()),
        render_string_list(&config.enabled.instruction_sets),
    )
}

fn render_string_list(values: &[String]) -> String {
    format!(
        "[{}]",
        values.iter().map(|value| quoted(value)).collect::<Vec<_>>().join(", ")
    )
}

fn render_tier_list(values: &[SimdTier]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| quoted(value.as_str()))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn quoted(value: &str) -> String {
    format!("\"{value}\"")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    fn env_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    fn with_cpu_config_path<T>(path: &Path, f: impl FnOnce() -> T) -> T {
        let _guard = env_lock().lock().unwrap_or_else(|err| err.into_inner());
        let previous = std::env::var(SIMPLE_CPU_CONFIG_PATH).ok();
        std::env::set_var(SIMPLE_CPU_CONFIG_PATH, path);
        *config_cache().lock().unwrap_or_else(|err| err.into_inner()) = None;
        let result = f();
        *config_cache().lock().unwrap_or_else(|err| err.into_inner()) = None;
        match previous.as_deref() {
            Some(value) => std::env::set_var(SIMPLE_CPU_CONFIG_PATH, value),
            None => std::env::remove_var(SIMPLE_CPU_CONFIG_PATH),
        }
        result
    }

    fn with_cpu_config_override<T>(path: &str, f: impl FnOnce() -> T) -> T {
        let _guard = env_lock().lock().unwrap_or_else(|err| err.into_inner());
        let previous = std::env::var(SIMPLE_CPU_CONFIG_PATH).ok();
        std::env::set_var(SIMPLE_CPU_CONFIG_PATH, path);
        *config_cache().lock().unwrap_or_else(|err| err.into_inner()) = None;
        let result = f();
        *config_cache().lock().unwrap_or_else(|err| err.into_inner()) = None;
        match previous.as_deref() {
            Some(value) => std::env::set_var(SIMPLE_CPU_CONFIG_PATH, value),
            None => std::env::remove_var(SIMPLE_CPU_CONFIG_PATH),
        }
        result
    }

    #[test]
    fn writes_and_reads_cpu_config_round_trip() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("cpu_config.sdn");

        with_cpu_config_path(&path, || {
            let config = host_cpu_config().unwrap();
            assert_eq!(config.version, 1);
            assert_eq!(config.target_triple, Target::host().triple_str());
            assert!(path.exists());

            let parsed = host_cpu_config().unwrap();
            assert_eq!(parsed, config);
        });
    }

    #[test]
    fn clamps_invalid_enabled_values_and_rewrites_file() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("cpu_config.sdn");

        with_cpu_config_path(&path, || {
            let detected = detected_config();
            let mut config = detected.clone();
            config.enabled.simd_tier = SimdTier::Wasm128;
            config.enabled.instruction_sets = vec!["definitely_not_real".to_string()];
            fs::write(&path, render_config(&config)).unwrap();

            let config = host_cpu_config().unwrap();
            assert_eq!(config.enabled.simd_tier, detected.enabled.simd_tier);
            assert_eq!(config.enabled.instruction_sets, detected.enabled.instruction_sets);

            let rewritten = fs::read_to_string(&path).unwrap();
            assert!(rewritten.contains(detected.enabled.simd_tier.as_str()));
            assert!(!rewritten.contains("definitely_not_real"));
        });
    }

    #[test]
    fn cpu_config_path_honors_trimmed_override() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("nested").join("custom_cpu_config.sdn");
        let override_value = format!("  {}  ", path.display());

        let rendered = with_cpu_config_override(&override_value, || {
            let resolved = cpu_config_path().unwrap();
            assert_eq!(resolved, path);
            host_cpu_config().unwrap();
            fs::read_to_string(&path).unwrap()
        });

        assert!(rendered.contains("version: 1"));
    }

    #[test]
    fn active_simd_tier_prefers_env_override_over_config() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("cpu_config.sdn");

        with_cpu_config_path(&path, || {
            let mut config = detected_config();
            config.enabled.simd_tier = SimdTier::Scalar;
            config.enabled.instruction_sets.clear();
            fs::write(&path, render_config(&config)).unwrap();

            let previous = std::env::var("SIMPLE_SIMD_TIER").ok();
            std::env::set_var("SIMPLE_SIMD_TIER", "x86_64_avx2");
            let active = active_simd_tier();
            match previous.as_deref() {
                Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
                None => std::env::remove_var("SIMPLE_SIMD_TIER"),
            }

            assert_eq!(active, SimdTier::X86_64Avx2);
        });
    }

    #[test]
    fn active_simd_tier_uses_config_enabled_tier_without_override() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("cpu_config.sdn");

        with_cpu_config_path(&path, || {
            let mut config = detected_config();
            config.enabled.simd_tier = SimdTier::Scalar;
            config.enabled.instruction_sets.clear();
            fs::write(&path, render_config(&config)).unwrap();

            let source = fs::read_to_string(&path).unwrap();
            let doc = parse_document(&source).unwrap();
            let enabled = doc.get("enabled").unwrap();
            assert_eq!(enabled.get("simd_tier").and_then(SdnValue::as_str), Some("scalar"));

            let parsed = host_cpu_config().unwrap();
            assert_eq!(parsed.enabled.simd_tier, SimdTier::Scalar);
            assert_eq!(active_simd_tier(), SimdTier::Scalar);
        });
    }

    #[test]
    fn host_cpu_config_reloads_after_on_disk_edit_in_same_process() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("cpu_config.sdn");

        with_cpu_config_path(&path, || {
            let initial = host_cpu_config().unwrap();
            fs::write(&path, "enabled: [\n").unwrap();

            let err = host_cpu_config().unwrap_err();
            assert!(matches!(err, HostCpuConfigError::Parse(_)));

            fs::write(&path, render_config(&initial)).unwrap();
            let reloaded = host_cpu_config().unwrap();
            assert_eq!(reloaded, initial);
        });
    }

    #[test]
    fn canonical_rewrite_uses_simple_supported_intersection() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("cpu_config.sdn");

        with_cpu_config_path(&path, || {
            let detected = detected_config();
            let mut config = detected.clone();
            config.enabled.instruction_sets = vec![
                "wasm128".to_string(),
                "avx2".to_string(),
                "sse2".to_string(),
                "sse2".to_string(),
            ];
            fs::write(&path, render_config(&config)).unwrap();

            let rewritten = host_cpu_config().unwrap();
            let allowed = allowed_instruction_sets_in_canonical_order(&detected);
            assert_eq!(rewritten.enabled.instruction_sets, allowed);
            assert_eq!(
                rewritten.simple_support.instruction_sets,
                detected.simple_support.instruction_sets
            );

            let source = fs::read_to_string(&path).unwrap();
            if !allowed.is_empty() {
                assert!(source.contains(&format!("instruction_sets: {}", render_string_list(&allowed))));
            }
            assert!(!source.contains("wasm128"));
        });
    }

    #[test]
    fn simple_support_excludes_unimplemented_host_only_instruction_sets() {
        let avx512_host = simple_supported_tiers_for_host(SimdTier::X86_64Avx512);
        let avx512_sets = supported_instruction_sets_for_tiers(&avx512_host);
        assert_eq!(
            avx512_host,
            vec![SimdTier::X86_64Avx2, SimdTier::X86_64Sse2, SimdTier::Scalar]
        );
        assert_eq!(avx512_sets, vec!["sse2", "avx2"]);

        let sve2_host = simple_supported_tiers_for_host(SimdTier::Aarch64Sve2);
        let sve2_sets = supported_instruction_sets_for_tiers(&sve2_host);
        assert_eq!(sve2_host, vec![SimdTier::Aarch64Neon, SimdTier::Scalar]);
        assert_eq!(sve2_sets, vec!["neon"]);

        let wasm_host = simple_supported_tiers_for_host(SimdTier::Wasm128);
        let wasm_sets = supported_instruction_sets_for_tiers(&wasm_host);
        assert_eq!(wasm_host, vec![SimdTier::Scalar]);
        assert!(wasm_sets.is_empty());
    }
}
