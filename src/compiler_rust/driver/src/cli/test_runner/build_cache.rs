//! Build cache for compiled test artifacts.
//!
//! Provides hash-based caching of compiled test files (SMF and native binaries)
//! to avoid recompilation when source hasn't changed.

use std::cell::RefCell;
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use simple_compiler::{CompilerPipeline, ProjectContext};
use simple_simd::{active_simd_tier, detect_profile};

/// Cache directory for compiled test artifacts
const CACHE_DIR: &str = "tmp/test_cache";

/// Build cache for test compilation artifacts.
///
/// Uses interior mutability (`RefCell`) for hash and content caches so that
/// methods can populate them through `&self` references without requiring
/// callers to hold `&mut self`.
pub struct BuildCache {
    cache_dir: PathBuf,
    force_rebuild: bool,
    /// Per-path hash cache — avoids re-reading + re-hashing the same file.
    hash_cache: RefCell<HashMap<PathBuf, u64>>,
    /// Per-path content cache — lets compile_test_to_native reuse the bytes
    /// that source_hash already read instead of reading the file a second time.
    content_cache: RefCell<HashMap<PathBuf, Vec<u8>>>,
}

impl BuildCache {
    /// Create a new build cache.
    pub fn new(force_rebuild: bool) -> Self {
        let cache_dir = PathBuf::from(CACHE_DIR);
        if !cache_dir.exists() {
            let _ = fs::create_dir_all(&cache_dir);
        }
        Self {
            cache_dir,
            force_rebuild,
            hash_cache: RefCell::new(HashMap::new()),
            content_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Compute a hash for the source file content (cached).
    ///
    /// The first call for a given path reads the file and stores both the
    /// hash and the raw bytes.  Subsequent calls return the cached hash
    /// without any I/O.
    fn source_hash(&self, path: &Path) -> Option<u64> {
        // Fast path: already computed
        if let Some(&h) = self.hash_cache.borrow().get(path) {
            return Some(h);
        }
        // Slow path: read, hash, cache
        let content = fs::read(path).ok()?;
        let mut hasher = DefaultHasher::new();
        content.hash(&mut hasher);
        path.hash(&mut hasher);
        active_simd_tier().as_str().hash(&mut hasher);
        let hash = hasher.finish();
        self.hash_cache.borrow_mut().insert(path.to_path_buf(), hash);
        self.content_cache.borrow_mut().insert(path.to_path_buf(), content);
        Some(hash)
    }

    /// Get the cached artifact path for a source file with given extension.
    fn artifact_path(&self, source: &Path, ext: &str) -> Option<PathBuf> {
        let hash = self.source_hash(source)?;
        Some(self.cache_dir.join(format!("{:016x}.{}", hash, ext)))
    }

    /// Check if a source file needs to be rebuilt.
    pub fn needs_rebuild(&self, source: &Path, ext: &str) -> bool {
        if self.force_rebuild {
            return true;
        }
        match self.artifact_path(source, ext) {
            Some(artifact) => !artifact.exists(),
            None => true,
        }
    }

    /// Compute the cached SMF artifact path for a source file.
    pub fn smf_artifact_path(&self, source: &Path) -> Result<PathBuf, String> {
        self.artifact_path(source, "smf")
            .ok_or_else(|| format!("Failed to compute hash for {}", source.display()))
    }

    /// Compile a test file to SMF format. Returns the path to the SMF artifact.
    pub fn compile_test_to_smf(&self, source: &Path) -> Result<PathBuf, String> {
        let output = self
            .artifact_path(source, "smf")
            .ok_or_else(|| format!("Failed to compute hash for {}", source.display()))?;

        if !self.needs_rebuild(source, "smf") {
            return Ok(output);
        }

        let mut pipeline = CompilerPipeline::new().map_err(|e| format!("Failed to create compiler pipeline: {}", e))?;

        // Enable test mode to activate SPipe DSL parsing
        pipeline.set_test_mode(true);

        pipeline
            .compile(source, &output)
            .map_err(|e| format!("Failed to compile {} to SMF: {}", source.display(), e))?;

        Ok(output)
    }

    /// Compile a test file to a native binary (ELF). Returns the path to the binary.
    pub fn compile_test_to_native(&self, source: &Path) -> Result<PathBuf, String> {
        let output = self
            .artifact_path(source, "elf")
            .ok_or_else(|| format!("Failed to compute hash for {}", source.display()))?;

        if !self.needs_rebuild(source, "elf") {
            return Ok(output);
        }

        self.compile_test_to_native_via_entry_closure(source, &output)?;

        // Make executable on Unix
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if let Ok(metadata) = fs::metadata(&output) {
                let mut perms = metadata.permissions();
                perms.set_mode(0o755);
                let _ = fs::set_permissions(&output, perms);
            }
        }

        Ok(output)
    }

    fn compile_test_to_native_via_entry_closure(&self, source: &Path, output: &Path) -> Result<(), String> {
        let project_source = source
            .file_name()
            .and_then(|name| name.to_str())
            .filter(|name| name.starts_with(".spipe_wrapped_entry_"))
            .and_then(|name| {
                source
                    .parent()
                    .map(|parent| parent.join(name.trim_start_matches(".spipe_wrapped_entry_")))
            })
            .filter(|candidate| candidate.exists())
            .unwrap_or_else(|| source.to_path_buf());

        let project_root = detect_native_test_project_root(&project_source)
            .or_else(|| ProjectContext::detect(&project_source).ok().map(|ctx| ctx.root))
            .ok_or_else(|| format!("Failed to detect project root for {}", source.display()))?;
        let project = ProjectContext::new(project_root)
            .map_err(|e| format!("Failed to detect project for {}: {}", source.display(), e))?;

        let mut config = NativeBuildConfig {
            entry_closure: true,
            incremental: false,
            clean: false,
            runtime_bundle: "runtime".to_string(),
            opt_level: simple_compiler::optimizations::NativeOptimizationLevel::default_for_native_executable(),
            ..Default::default()
        };

        if let Ok(backend) = std::env::var("SIMPLE_BACKEND") {
            let normalized = match backend.as_str() {
                "llvm-lib" | "llvmlib" => "llvm",
                other => other,
            };
            if !normalized.is_empty() {
                config.backend = normalized.to_string();
            }
        }

        let mut builder = NativeProjectBuilder::new(project.root.clone(), output.to_path_buf())
            .config(config)
            .entry_file(source.to_path_buf());

        for dir in native_test_source_dirs(&project.root, &project_source) {
            builder = builder.source_dir(dir);
        }

        builder
            .build()
            .map(|_| ())
            .map_err(|e| format!("Failed to compile {} to native binary: {}", source.display(), e))
    }

    /// Clean the cache directory.
    pub fn clean(&self) -> Result<(), String> {
        if self.cache_dir.exists() {
            fs::remove_dir_all(&self.cache_dir).map_err(|e| format!("Failed to clean cache: {}", e))?;
            fs::create_dir_all(&self.cache_dir).map_err(|e| format!("Failed to recreate cache dir: {}", e))?;
        }
        Ok(())
    }

    /// Remove artifacts for a specific source file.
    pub fn invalidate(&self, source: &Path) {
        for ext in &["smf", "elf"] {
            if let Some(path) = self.artifact_path(source, ext) {
                let _ = fs::remove_file(path);
            }
        }
    }
}

fn native_test_source_dirs(project_root: &Path, entry_path: &Path) -> Vec<PathBuf> {
    let rel_entry = entry_path
        .strip_prefix(project_root)
        .ok()
        .and_then(|path| path.to_str());

    let candidates = if rel_entry
        .is_some_and(|path| path.starts_with("test/unit/lib/") || path.starts_with("test/integration/lib/"))
    {
        vec![project_root.join("src/lib"), project_root.join("test")]
    } else if rel_entry
        .is_some_and(|path| path.starts_with("test/unit/compiler/") || path.starts_with("test/integration/compiler/"))
    {
        vec![
            project_root.join("src/compiler"),
            project_root.join("src/lib"),
            project_root.join("test"),
        ]
    } else if rel_entry
        .is_some_and(|path| path.starts_with("test/unit/app/") || path.starts_with("test/integration/app/"))
    {
        vec![
            project_root.join("src/app"),
            project_root.join("src/lib"),
            project_root.join("test"),
        ]
    } else {
        vec![
            project_root.join("src"),
            project_root.join("src/compiler"),
            project_root.join("src/app"),
            project_root.join("src/lib"),
            project_root.join("test"),
        ]
    };

    let mut dirs = Vec::new();
    for candidate in candidates {
        if candidate.is_dir() && !dirs.contains(&candidate) {
            dirs.push(candidate);
        }
    }

    if dirs.is_empty() {
        let fallback = project_root.join("src");
        if fallback.is_dir() {
            dirs.push(fallback);
        }
    }

    dirs
}

fn detect_native_test_project_root(source: &Path) -> Option<PathBuf> {
    let mut current = source.parent();
    while let Some(dir) = current {
        let src_dir = dir.join("src");
        let test_dir = dir.join("test");
        if src_dir.is_dir() && test_dir.is_dir() {
            return Some(dir.to_path_buf());
        }
        current = dir.parent();
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Mutex, OnceLock};
    use tempfile::tempdir;

    fn env_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    fn render_cpu_config(
        target_triple: &str,
        support_tier: &str,
        support_sets: &[&str],
        simple_fallbacks: &[&str],
        simple_sets: &[&str],
        enabled_tier: &str,
        enabled_sets: &[&str],
    ) -> String {
        fn render_list(values: &[&str]) -> String {
            format!("[{}]", values.join(", "))
        }

        format!(
            "version: 1\n\
             target_triple: {target_triple}\n\
             generated_by: simple-simd\n\
             support {{\n\
               simd_tier: {support_tier}\n\
               instruction_sets: {support_sets}\n\
             }}\n\
             simple_support {{\n\
               simd_tier_fallbacks: {simple_fallbacks}\n\
               instruction_sets: {simple_sets}\n\
             }}\n\
             enabled {{\n\
               simd_tier: {enabled_tier}\n\
               instruction_sets: {enabled_sets}\n\
             }}\n",
            support_sets = render_list(support_sets),
            simple_fallbacks = render_list(simple_fallbacks),
            simple_sets = render_list(simple_sets),
            enabled_sets = render_list(enabled_sets),
        )
    }

    #[test]
    fn test_source_hash_deterministic() {
        // Two calls with same path should produce same hash
        let path = Path::new("test/fixtures/sample.spl");
        let cache = BuildCache::new(false);
        let h1 = cache.source_hash(path);
        let h2 = cache.source_hash(path);
        // Both None if file doesn't exist, but they should match
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_needs_rebuild_force() {
        let cache = BuildCache::new(true);
        assert!(cache.needs_rebuild(Path::new("nonexistent.spl"), "smf"));
    }

    #[test]
    fn test_native_test_source_dirs_prefers_lib_roots_for_lib_specs() {
        let tmp = tempdir().expect("tempdir");
        fs::create_dir_all(tmp.path().join("src/lib")).expect("lib dir");
        fs::create_dir_all(tmp.path().join("test")).expect("test dir");
        let entry = tmp.path().join("test/unit/lib/db/accel_spec.spl");
        fs::create_dir_all(entry.parent().unwrap()).expect("entry dir");
        fs::write(&entry, "").expect("entry file");

        let dirs = native_test_source_dirs(tmp.path(), &entry);

        assert_eq!(dirs, vec![tmp.path().join("src/lib"), tmp.path().join("test"),]);
    }

    #[test]
    fn test_native_test_source_dirs_falls_back_to_src() {
        let tmp = tempdir().expect("tempdir");
        fs::create_dir_all(tmp.path().join("src")).expect("src dir");
        let entry = tmp.path().join("test/misc/demo_spec.spl");
        fs::create_dir_all(entry.parent().unwrap()).expect("entry dir");
        fs::write(&entry, "").expect("entry file");

        let dirs = native_test_source_dirs(tmp.path(), &entry);

        assert_eq!(dirs, vec![tmp.path().join("src")]);
    }

    #[test]
    fn test_native_test_source_dirs_keeps_compiler_roots_for_compiler_specs() {
        let tmp = tempdir().expect("tempdir");
        fs::create_dir_all(tmp.path().join("src/compiler")).expect("compiler dir");
        fs::create_dir_all(tmp.path().join("src/lib")).expect("lib dir");
        fs::create_dir_all(tmp.path().join("test")).expect("test dir");
        let entry = tmp.path().join("test/unit/compiler/native/foo_spec.spl");
        fs::create_dir_all(entry.parent().unwrap()).expect("entry dir");
        fs::write(&entry, "").expect("entry file");

        let dirs = native_test_source_dirs(tmp.path(), &entry);

        assert_eq!(
            dirs,
            vec![
                tmp.path().join("src/compiler"),
                tmp.path().join("src/lib"),
                tmp.path().join("test"),
            ]
        );
    }

    #[test]
    fn test_source_hash_uses_configured_active_simd_tier() {
        let _guard = env_lock().lock().unwrap_or_else(|err| err.into_inner());
        let temp = tempdir().expect("tempdir");
        let source = temp.path().join("demo_spec.spl");
        let config_path = temp.path().join("cpu_config.sdn");
        fs::write(&source, "test body").expect("source file");

        let detected = detect_profile();
        let active_tier = detected.best_available_implementation();
        let configured_tier = match active_tier {
            simple_simd::SimdTier::X86_64Avx2 => simple_simd::SimdTier::X86_64Sse2,
            simple_simd::SimdTier::X86_64Avx512 => simple_simd::SimdTier::X86_64Avx2,
            simple_simd::SimdTier::Aarch64Neon => simple_simd::SimdTier::Scalar,
            simple_simd::SimdTier::Riscv64Rvv => simple_simd::SimdTier::Scalar,
            _ => return,
        };

        let (support_sets, simple_fallbacks, simple_sets, enabled_sets): (&[&str], &[&str], &[&str], &[&str]) =
            match active_tier {
                simple_simd::SimdTier::X86_64Avx512 => (
                    &["sse2", "avx2", "avx512f"],
                    &["x86_64_avx2", "x86_64_sse2", "scalar"],
                    &["sse2", "avx2"],
                    &["sse2", "avx2"],
                ),
                simple_simd::SimdTier::X86_64Avx2 => (
                    &["sse2", "avx2"],
                    &["x86_64_avx2", "x86_64_sse2", "scalar"],
                    &["sse2", "avx2"],
                    &["sse2"],
                ),
                simple_simd::SimdTier::Aarch64Neon => (&["neon"], &["aarch64_neon", "scalar"], &["neon"], &[]),
                simple_simd::SimdTier::Riscv64Rvv => (&["rvv"], &["riscv64_rvv", "scalar"], &["rvv"], &[]),
                _ => return,
            };

        let previous_config_path = std::env::var("SIMPLE_CPU_CONFIG_PATH").ok();
        let previous_override = std::env::var("SIMPLE_SIMD_TIER").ok();
        std::env::set_var("SIMPLE_CPU_CONFIG_PATH", &config_path);
        std::env::remove_var("SIMPLE_SIMD_TIER");

        fs::write(
            &config_path,
            render_cpu_config(
                simple_target::Target::host().triple_str(),
                active_tier.as_str(),
                support_sets,
                simple_fallbacks,
                simple_sets,
                configured_tier.as_str(),
                enabled_sets,
            ),
        )
        .expect("cpu_config.sdn");

        let cache = BuildCache::new(false);
        let configured_hash = cache.source_hash(&source).expect("configured hash");

        let mut active_hasher = DefaultHasher::new();
        fs::read(&source).expect("source bytes").hash(&mut active_hasher);
        source.hash(&mut active_hasher);
        configured_tier.as_str().hash(&mut active_hasher);
        let expected_active_hash = active_hasher.finish();

        let mut detected_hasher = DefaultHasher::new();
        fs::read(&source).expect("source bytes").hash(&mut detected_hasher);
        source.hash(&mut detected_hasher);
        detected.as_str().hash(&mut detected_hasher);
        let detected_hash = detected_hasher.finish();

        match previous_config_path.as_deref() {
            Some(value) => std::env::set_var("SIMPLE_CPU_CONFIG_PATH", value),
            None => std::env::remove_var("SIMPLE_CPU_CONFIG_PATH"),
        }
        match previous_override.as_deref() {
            Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
            None => std::env::remove_var("SIMPLE_SIMD_TIER"),
        }

        assert_eq!(configured_hash, expected_active_hash);
        assert_ne!(configured_hash, detected_hash);
    }
}
