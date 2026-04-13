//! Native project builder: compile all .spl files -> .o -> linked binary.
//!
//! Orchestrates the full native build pipeline:
//! 1. Discover .spl files in source directories
//! 2. Compile each file in parallel (Parse -> Mono -> HIR -> MIR -> Cranelift -> .o)
//! 3. Link all .o files into a native binary
//!
//! Supports incremental compilation via content-hash keyed .o cache,
//! and auto-detected linker selection via `LinkerBuilder`.

mod config;
mod compiler;
mod discovery;
mod linker;
mod imports;
mod mangle;
mod stubs;
mod tools;
#[cfg(test)]
mod tests;

pub use config::*;
pub use compiler::*;
pub use linker::*;
pub use imports::*;
pub use tools::*;

use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

/// Safe canonicalize that avoids `libc::realpath` which segfaults in
/// self-hosted Cranelift-compiled binaries.  Falls back to manual
/// absolute-path resolution when the stdlib call fails or when running
/// in a self-hosted context.
pub(crate) fn safe_canonicalize(path: &Path) -> PathBuf {
    // Do NOT call std::fs::canonicalize -- it uses libc::realpath which
    // segfaults in self-hosted Cranelift-compiled binaries.
    // Manual absolute-path resolution instead:
    let abs = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().unwrap_or_default().join(path)
    };
    // Resolve . and ..
    let mut out = PathBuf::new();
    for comp in abs.components() {
        match comp {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            c => out.push(c),
        }
    }
    out
}

/// CLI-provided runtime library directory override.
/// Set before building; read by `find_native_all_library()` and `find_runtime_library()`.
pub(crate) static RUNTIME_PATH_OVERRIDE: OnceLock<PathBuf> = OnceLock::new();

/// Set the runtime path override (called from CLI arg parsing).
pub fn set_runtime_path_override(path: PathBuf) {
    let _ = RUNTIME_PATH_OVERRIDE.set(path);
}

/// CLI-provided cross-compilation target override.
/// Set before building; read by `compile_file_to_object()` to select the right backend target.
static TARGET_OVERRIDE: OnceLock<simple_common::target::Target> = OnceLock::new();

/// Set the cross-compilation target override (called from CLI arg parsing).
pub fn set_target_override(target: simple_common::target::Target) {
    let _ = TARGET_OVERRIDE.set(target);
}

/// Get the effective compilation target (override or host).
pub(crate) fn effective_target() -> simple_common::target::Target {
    TARGET_OVERRIDE
        .get()
        .copied()
        .unwrap_or_else(simple_common::target::Target::host)
}

/// Cross-module import resolution data shared across compilation units.
///
/// Groups the four `Arc`-wrapped maps that are always passed together during
/// parallel and sequential compilation of native projects.
#[derive(Clone)]
pub(crate) struct ModuleImports {
    /// Map from unmangled function name to its unique mangled name.
    pub import_map: std::sync::Arc<std::collections::HashMap<String, String>>,
    /// Set of function names that have multiple definitions (ambiguous).
    pub ambiguous_names: std::sync::Arc<std::collections::HashSet<String>>,
    /// Map from unmangled name to all mangled variants.
    pub all_mangled: std::sync::Arc<std::collections::HashMap<String, Vec<String>>>,
    /// Per-module re-export maps.
    pub re_exports: std::sync::Arc<std::collections::HashMap<String, std::collections::HashMap<String, String>>>,
    /// Global struct definitions: struct_name -> [(field_name, field_type_name)].
    /// Shared across all compilation units for consistent cross-module field offsets.
    pub struct_defs: std::sync::Arc<std::collections::HashMap<String, Vec<(String, String)>>>,
    /// When true, pass `struct_defs` to the HIR lowerer so cross-module field
    /// accesses (e.g. `fb_info.addr.addr`) can resolve to real FieldGet instructions
    /// instead of falling through to dynamic MethodCall (which becomes
    /// `rt_function_not_found`). Safe only when the compiled file set is small
    /// enough that the "most fields wins" ambiguity heuristic in
    /// `get_field_info` is unlikely to mis-resolve — currently set only for
    /// `--entry-closure` builds.
    pub populate_global_struct_defs: bool,
}

/// Configuration for native project builds.
#[derive(Debug, Clone)]
pub struct NativeBuildConfig {
    /// Per-file compilation timeout in seconds.
    pub file_timeout: u64,
    /// Stack size per compilation thread.
    pub stack_size: usize,
    /// Whether to use parallel compilation.
    pub parallel: bool,
    /// Strip symbols from output binary.
    pub strip: bool,
    /// Verbose output.
    pub verbose: bool,
    /// Number of threads (None = all available).
    pub num_threads: Option<usize>,
    /// Enable incremental compilation (default: true).
    pub incremental: bool,
    /// Cache directory for incremental builds (default: .simple/native_cache).
    pub cache_dir: Option<PathBuf>,
    /// Force clean rebuild (delete cache before building).
    pub clean: bool,
    /// Disable name mangling for cross-module resolution (default: false = mangling enabled).
    pub no_mangle: bool,
    /// Codegen backend: "llvm" (default) or "cranelift".
    /// LLVM produces correct cross-module struct field access; Cranelift has
    /// a known FieldGet offset bug for fields at byte_offset > 0.
    pub backend: String,
    /// Explicit runtime library directory (overrides env var and auto-discovery).
    pub runtime_path: Option<PathBuf>,
    /// Runtime bundle selection: "auto", "runtime", or "all".
    pub runtime_bundle: String,
    /// Discover files from the explicit entrypoint's reachable import closure.
    pub entry_closure: bool,
    /// Cross-compilation target (e.g. "riscv32-unknown-none"). None = host.
    pub target: Option<simple_common::target::Target>,
    /// Linker script path for freestanding/OS targets.
    pub linker_script: Option<PathBuf>,
}

impl Default for NativeBuildConfig {
    fn default() -> Self {
        Self {
            file_timeout: 60,
            stack_size: 16 * 1024 * 1024,
            parallel: true,
            strip: false,
            verbose: false,
            num_threads: None,
            incremental: true,
            cache_dir: None,
            clean: false,
            no_mangle: false,
            backend: if cfg!(feature = "llvm") { "llvm" } else { "cranelift" }.to_string(),
            runtime_path: None,
            runtime_bundle: "auto".to_string(),
            entry_closure: false,
            target: None,
            linker_script: None,
        }
    }
}

/// Result of a native build.
#[derive(Debug)]
pub struct NativeBuildResult {
    /// Output binary path.
    pub output: PathBuf,
    /// Number of files compiled successfully.
    pub compiled: usize,
    /// Number of files that failed.
    pub failed: usize,
    /// Number of files served from cache.
    pub cached: usize,
    /// Total compilation time.
    pub compile_time: Duration,
    /// Link time.
    pub link_time: Duration,
    /// Output binary size in bytes.
    pub binary_size: u64,
    /// Files that failed with their error messages.
    pub failures: Vec<(PathBuf, String)>,
}

/// Builder for compiling a Simple project to a native binary.
pub struct NativeProjectBuilder {
    /// Source directories to scan for .spl files.
    pub(crate) source_dirs: Vec<PathBuf>,
    /// Project root directory.
    pub(crate) project_root: PathBuf,
    /// Source root for module prefix computation (typically project_root/src).
    pub(crate) source_root: PathBuf,
    /// Output binary path.
    pub(crate) output: PathBuf,
    /// Build configuration.
    pub(crate) config: NativeBuildConfig,
    /// Entry file whose `main` becomes `spl_main` (the program entry point).
    pub(crate) entry_file: Option<PathBuf>,
}

impl NativeProjectBuilder {
    /// Create a new builder.
    pub fn new(project_root: PathBuf, output: PathBuf) -> Self {
        // Skip canonicalize -- it segfaults in self-hosted binaries (Cranelift/libc interaction)
        let project_root = if project_root.is_absolute() {
            project_root
        } else {
            std::env::current_dir().unwrap_or_default().join(&project_root)
        };
        let source_root = project_root.join("src");
        Self {
            source_dirs: vec![],
            project_root,
            source_root,
            output,
            config: NativeBuildConfig::default(),
            entry_file: None,
        }
    }

    /// Add a source directory to scan.
    /// Preserves the logical path so symlinked source roots keep their module prefix.
    pub fn source_dir(mut self, dir: PathBuf) -> Self {
        let absolute = if dir.is_absolute() {
            dir
        } else {
            self.project_root.join(dir)
        };
        self.source_dirs.push(absolute);
        self
    }

    /// Set build configuration.
    pub fn config(mut self, config: NativeBuildConfig) -> Self {
        self.config = config;
        self
    }

    /// Set verbose mode.
    pub fn verbose(mut self, v: bool) -> Self {
        self.config.verbose = v;
        self
    }

    /// Set strip mode.
    pub fn strip(mut self, s: bool) -> Self {
        self.config.strip = s;
        self
    }

    /// Set number of threads.
    pub fn threads(mut self, n: usize) -> Self {
        self.config.num_threads = Some(n);
        self
    }

    /// Set per-file timeout.
    pub fn timeout(mut self, secs: u64) -> Self {
        self.config.file_timeout = secs;
        self
    }

    /// Set the entry file whose `main` function becomes the program entry point (`spl_main`).
    pub fn entry_file(mut self, path: PathBuf) -> Self {
        self.entry_file = Some(safe_canonicalize(&path));
        self
    }

    /// Resolve the cache directory path.
    /// Includes target triple in the path to prevent cross-target contamination
    /// (e.g., host Mach-O objects being served for a riscv64-elf build).
    pub(crate) fn cache_dir(&self) -> PathBuf {
        let base = self
            .config
            .cache_dir
            .clone()
            .unwrap_or_else(|| self.project_root.join(".simple/native_cache"));
        let target = effective_target();
        if target.is_host() {
            base
        } else {
            base.join(target.triple_str())
        }
    }

    pub(crate) fn effective_source_root_for(&self, path: &Path) -> PathBuf {
        let canonical_path = safe_canonicalize(path);
        let mut best: Option<PathBuf> = None;
        let mut best_depth = 0usize;
        for dir in &self.source_dirs {
            let canonical_dir = safe_canonicalize(dir);
            if canonical_path.starts_with(&canonical_dir) {
                let depth = canonical_dir.components().count();
                if depth > best_depth {
                    best_depth = depth;
                    best = Some(canonical_dir);
                }
            }
        }
        best.unwrap_or_else(|| self.source_root.clone())
    }

    pub(crate) fn effective_source_root(&self) -> PathBuf {
        if let Some(entry_file) = &self.entry_file {
            return self.effective_source_root_for(entry_file);
        }
        self.source_dirs
            .first()
            .map(|dir| safe_canonicalize(dir))
            .unwrap_or_else(|| self.source_root.clone())
    }

    /// Build the project.
    pub fn build(self) -> Result<NativeBuildResult, String> {
        // 1. Discover files
        let files = self.discover_files()?;
        if files.is_empty() {
            return Err("No .spl files found in source directories".to_string());
        }
        if self.config.verbose {
            eprintln!("Found {} .spl files", files.len());
        }

        // 2. Set up incremental state
        let cache_dir = self.cache_dir();
        let objects_dir = cache_dir.join("objects");

        if self.config.clean {
            if self.config.verbose {
                eprintln!("Clean build: removing cache at {}", cache_dir.display());
            }
            let _ = std::fs::remove_dir_all(&cache_dir);
        }

        let use_incremental = self.config.incremental && !self.config.clean;
        if use_incremental {
            std::fs::create_dir_all(&objects_dir).map_err(|e| format!("create cache dir: {e}"))?;
        }

        // 3. Create temp directory for .o files
        let mut temp_dir = Some(tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?);
        let temp_dir_path = temp_dir.as_ref().unwrap().path().to_path_buf();

        // 4. Read all source files and determine dirty set
        let compile_start = Instant::now();
        let mut file_sources: Vec<(PathBuf, String)> = Vec::new();
        for path in &files {
            let mut source = std::fs::read_to_string(path)
                .map_err(|e| (path.clone(), format!("read: {e}")))
                .map_err(|(p, m)| format!("{}: {}", p.display(), m))?;
            // Normalize CRLF -> LF for cross-platform compatibility
            if source.contains('\r') {
                source = source.replace('\r', "");
            }
            file_sources.push((path.clone(), source));
        }

        // Deduplicate files for compilation (symlink aliases compile once, but
        // all paths remain in file_sources for import map indexing).
        let compile_indices: std::collections::HashSet<usize> =
            Self::deduplicate_for_compilation(&files).into_iter().collect();

        // Determine which files need recompilation via content hash
        let mut to_compile: Vec<(usize, PathBuf, String)> = Vec::new();
        let mut cached_objects: Vec<(usize, PathBuf)> = Vec::new();

        if use_incremental {
            // Canonicalize entry early so we can force-recompile the entry file
            let canon_entry_for_cache: Option<PathBuf> = self.entry_file.as_ref().map(|p| safe_canonicalize(p));
            for (i, (path, source)) in file_sources.iter().enumerate() {
                // Skip symlink aliases -- only compile each physical file once
                if !compile_indices.contains(&i) {
                    continue;
                }
                // Always recompile the entry file (its main->spl_main renaming depends on is_entry)
                let is_entry = is_entry_file(path, &canon_entry_for_cache);
                if !is_entry {
                    let per_file_root = self.effective_source_root_for(path);
                    let module_prefix = crate::codegen::common_backend::module_prefix_from_path(
                        path,
                        &per_file_root,
                    );
                    let hash = object_cache_key(
                        source,
                        is_entry,
                        &self.config.backend,
                        self.config.no_mangle,
                        &module_prefix,
                    );
                    let cached_o = objects_dir.join(format!("{:016x}.o", hash));
                    if cached_o.exists() {
                        // Cache hit: copy to temp dir
                        let obj_path = temp_dir_path.join(format!("mod_{}.o", i));
                        if std::fs::copy(&cached_o, &obj_path).is_ok() {
                            cached_objects.push((i, obj_path));
                            continue;
                        }
                    }
                }
                to_compile.push((i, path.clone(), source.clone()));
            }
        } else {
            for (i, (path, source)) in file_sources.iter().enumerate() {
                // Skip symlink aliases -- only compile each physical file once
                if !compile_indices.contains(&i) {
                    continue;
                }
                to_compile.push((i, path.clone(), source.clone()));
            }
        }

        let cached_count = cached_objects.len();
        if self.config.verbose && use_incremental {
            eprintln!("Incremental: {} cached, {} to compile", cached_count, to_compile.len());
        }

        // Canonicalize the entry file path for comparison during compilation
        let canonical_entry: Option<PathBuf> = self.entry_file.as_ref().map(|p| safe_canonicalize(p));
        if self.config.verbose {
            match &canonical_entry {
                Some(p) => eprintln!("Canonical entry: {}", p.display()),
                None => eprintln!("Canonical entry: <none>"),
            }
        }

        // 4b. Discovery phase: build import map for cross-module function resolution.
        let imports = if !self.config.no_mangle {
            let result = build_import_map(&file_sources, &self.source_dirs, &self.source_root);
            if self.config.verbose {
                eprintln!(
                    "Import map: {} unique, {} ambiguous function entries, {} modules with re-exports",
                    result.map.len(),
                    result.ambiguous.len(),
                    result.re_exports.len()
                );
                if let Ok(symbol) = std::env::var("SIMPLE_DEBUG_IMPORT_SYMBOL") {
                    if let Some(candidates) = result.all_mangled.get(&symbol) {
                        eprintln!("Import candidates for {}:", symbol);
                        for candidate in candidates {
                            eprintln!("  {}", candidate);
                        }
                    } else {
                        eprintln!("Import candidates for {}: <none>", symbol);
                    }
                }
            }
            ModuleImports {
                import_map: std::sync::Arc::new(result.map),
                ambiguous_names: std::sync::Arc::new(result.ambiguous),
                all_mangled: std::sync::Arc::new(result.all_mangled),
                re_exports: std::sync::Arc::new(result.re_exports),
                struct_defs: std::sync::Arc::new(result.struct_defs),
                populate_global_struct_defs: self.config.entry_closure,
            }
        } else {
            ModuleImports {
                import_map: std::sync::Arc::new(std::collections::HashMap::new()),
                ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
                all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
                re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
                struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
                populate_global_struct_defs: false,
            }
        };

        // 5. Compile dirty files
        let results = if self.config.parallel {
            self.compile_entries_parallel(&to_compile, &temp_dir_path, &canonical_entry, &imports)
        } else {
            self.compile_entries_sequential(&to_compile, &temp_dir_path, &canonical_entry, &imports)
        };
        let compile_time = compile_start.elapsed();

        // Collect results
        let mut object_paths: Vec<PathBuf> = cached_objects.into_iter().map(|(_, p)| p).collect();
        let mut failures = Vec::new();
        let mut freshly_compiled: Vec<(usize, PathBuf)> = Vec::new();

        for result in results {
            match result {
                Ok((idx, path)) => {
                    freshly_compiled.push((idx, path.clone()));
                    object_paths.push(path);
                }
                Err((path, msg)) => failures.push((path, msg)),
            }
        }

        let compiled = object_paths.len();
        let failed = failures.len();

        // Always log individual failures when present (bootstrap visibility).
        if failed > 0 {
            eprintln!("\nFAILED FILES ({}):", failed);
            for (path, msg) in &failures {
                eprintln!("  - {} => {}", path.display(), msg);
            }
            eprintln!(); // spacer
        }

        if failed > 0 {
            // Only abort if compiler-critical files failed (src/compiler/, src/app/)
            // Exclude non-essential app modules (dashboards, examples)
            let non_critical = ["llm_dashboard", "web_dashboard", "obsidian", "korean_stock"];
            let critical_failures: Vec<_> = failures
                .iter()
                .filter(|(path, _)| {
                    let p = path.display().to_string();
                    if non_critical.iter().any(|s| p.contains(s)) {
                        return false;
                    }
                    p.contains("/src/compiler/")
                        || p.contains("\\src\\compiler\\")
                        || p.contains("/src/app/")
                        || p.contains("\\src\\app\\")
                })
                .collect();

            if !critical_failures.is_empty() {
                let summary = critical_failures
                    .iter()
                    .map(|(path, msg)| format!("{}: {}", path.display(), msg))
                    .collect::<Vec<_>>()
                    .join("\n");
                return Err(format!(
                    "native-build aborted: {} critical file(s) failed to compile\n{}",
                    critical_failures.len(),
                    summary
                ));
            }

            eprintln!("\nWarning: {} non-critical file(s) failed to compile (skipped)", failed);
        }

        if self.config.verbose {
            eprintln!(
                "Compiled: {}/{} ({} cached, {} fresh, {} failed) in {:.1}s",
                compiled,
                files.len(),
                cached_count,
                freshly_compiled.len(),
                failed,
                compile_time.as_secs_f64()
            );
        }

        if failed > 0 {
            // Only abort if compiler-critical files failed (src/compiler/, src/app/)
            // Exclude non-essential app modules (dashboards, examples)
            let non_critical = ["llm_dashboard", "web_dashboard", "obsidian", "korean_stock"];
            let critical_failures: Vec<_> = failures
                .iter()
                .filter(|(path, _)| {
                    let p = path.display().to_string();
                    if non_critical.iter().any(|s| p.contains(s)) {
                        return false;
                    }
                    p.contains("/src/compiler/")
                        || p.contains("\\src\\compiler\\")
                        || p.contains("/src/app/")
                        || p.contains("\\src\\app\\")
                })
                .collect();

            if !critical_failures.is_empty() {
                let summary = critical_failures
                    .iter()
                    .map(|(path, msg)| format!("{}: {}", path.display(), msg))
                    .collect::<Vec<_>>()
                    .join("\n");
                return Err(format!(
                    "native-build aborted: {} critical file(s) failed to compile\n{}",
                    critical_failures.len(),
                    summary
                ));
            }

            eprintln!("\nWarning: {} non-critical file(s) failed to compile (skipped)", failed);
        }

        if object_paths.is_empty() {
            return Err(format!("All {} files failed to compile", files.len()));
        }

        // 6. Cache freshly compiled objects
        if use_incremental {
            for (idx, obj_path) in &freshly_compiled {
                if let Some((path, source)) = file_sources.get(*idx) {
                    let is_entry = is_entry_file(path, &canonical_entry);
                    let per_file_root = self.effective_source_root_for(path);
                    let module_prefix = crate::codegen::common_backend::module_prefix_from_path(
                        path,
                        &per_file_root,
                    );
                    let hash = object_cache_key(
                        source,
                        is_entry,
                        &self.config.backend,
                        self.config.no_mangle,
                        &module_prefix,
                    );
                    let cached_o = objects_dir.join(format!("{:016x}.o", hash));
                    let _ = std::fs::copy(obj_path, cached_o);
                }
            }
        }

        // 7. Link
        let link_start = Instant::now();
        let link_result = self.link_objects(&object_paths, &imports);
        let link_time = link_start.elapsed();

        // On link failure, optionally keep objects for debugging
        if let Err(e) = link_result {
            if let Some(dir) = temp_dir.take() {
                let path = dir.keep();
                eprintln!("Link failed. Objects kept at: {}", path.display());
            }
            return Err(e);
        }

        // Optionally keep the temporary object directory for debugging.
        if std::env::var("SIMPLE_KEEP_NATIVE_OBJS").is_ok() {
            if let Some(dir) = temp_dir.take() {
                let path = dir.keep();
                eprintln!("Keeping native object files in {}", path.display());
            }
        }

        let binary_size = std::fs::metadata(&self.output).map(|m| m.len()).unwrap_or(0);

        if self.config.verbose {
            eprintln!(
                "Linked: {} ({} KB) in {:.1}s",
                self.output.display(),
                binary_size / 1024,
                link_time.as_secs_f64()
            );
        }

        Ok(NativeBuildResult {
            output: self.output,
            compiled: freshly_compiled.len(),
            failed,
            cached: cached_count,
            compile_time,
            link_time,
            binary_size,
            failures,
        })
    }
}

/// Check if a file path matches the canonical entry file path.
pub(crate) fn is_entry_file(file_path: &Path, canonical_entry: &Option<PathBuf>) -> bool {
    match canonical_entry {
        Some(entry) => {
            let p = safe_canonicalize(file_path);
            let is_entry = p == *entry;
            if is_entry {
                return true;
            }
            if std::env::var("SIMPLE_DEBUG_ENTRY").is_ok() {
                eprintln!("[entry-debug] no match: {} vs {}", p.display(), entry.display());
            }
            false
        }
        None => false,
    }
}

pub(crate) fn same_file_path(a: &Path, b: &Path) -> bool {
    let canon_a = safe_canonicalize(a);
    let canon_b = safe_canonicalize(b);
    canon_a == canon_b
}

/// Compute a content hash for a source string (same algorithm as SourceInfo).
pub(crate) fn content_hash(content: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    content.hash(&mut hasher);
    hasher.finish()
}

/// Compute the object cache key for a module.
///
/// The generated object is not determined by source text alone: entry modules
/// rename `main` to `spl_main`, backend choice changes codegen, and
/// no-mangle mode changes symbol emission. All of that must be part of the
/// cache key or an object from a previous build can be linked under the wrong
/// role.
///
/// The `module_prefix` is also part of the key: two files with identical
/// content but different paths (e.g. `src/app/mcp/startup_log.spl` and
/// `src/app/simple_lsp_mcp/startup_log.spl`) produce different mangled
/// symbol names, so their cached objects cannot be shared. Without this,
/// building one app after the other would reuse the other app's object and
/// leave all cross-module calls unresolved (linked as stubs returning nil).
pub(crate) fn object_cache_key(
    content: &str,
    is_entry: bool,
    backend: &str,
    no_mangle: bool,
    module_prefix: &str,
) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    content.hash(&mut hasher);
    is_entry.hash(&mut hasher);
    backend.hash(&mut hasher);
    no_mangle.hash(&mut hasher);
    module_prefix.hash(&mut hasher);
    hasher.finish()
}

/// Recursively collect .spl files from a directory.
/// Skips broken symlinks and non-regular files.
pub(crate) fn collect_spl_files_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        let ft = match entry.file_type() {
            Ok(ft) => ft,
            Err(_) => continue,
        };
        if ft.is_dir() {
            collect_spl_files_recursive(&path, out);
        } else if ft.is_symlink() {
            if path.is_file() && path.extension().is_some_and(|e| e == "spl") {
                out.push(path);
            }
        } else if path.extension().is_some_and(|e| e == "spl") {
            if let Some(p) = path.to_str() {
                if p.contains("check.spl") {
                    continue;
                }
            }
            if path.is_file() {
                out.push(path);
            }
        }
    }
}

/// Find the best source root for a given file from a list of source directories.
/// Returns the most specific (deepest) source dir that contains the file,
/// or falls back to the fallback root.
pub(crate) fn source_root_for_file(file_path: &Path, source_dirs: &[PathBuf], fallback: &Path) -> PathBuf {
    let canonical_path = safe_canonicalize(file_path);
    let mut best: Option<PathBuf> = None;
    let mut best_depth = 0usize;
    for dir in source_dirs {
        let canonical_dir = safe_canonicalize(dir);
        if canonical_path.starts_with(&canonical_dir) {
            let depth = canonical_dir.components().count();
            if depth > best_depth {
                best_depth = depth;
                best = Some(canonical_dir);
            }
        }
    }
    best.unwrap_or_else(|| fallback.to_path_buf())
}
