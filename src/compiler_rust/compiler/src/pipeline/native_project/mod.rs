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
pub(crate) mod inline_asm_emit;
mod linker;
mod imports;
mod mangle;
mod module_global_init;
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

use simple_parser::Parser;

use crate::optimizations::NativeOptimizationLevel;
use crate::security::build_security_inventory;
use crate::stdlib_variant::active_simd_tier_name;

pub(crate) fn native_project_rust_trace_enabled() -> bool {
    matches!(
        std::env::var("SIMPLE_NATIVE_BUILD_RUST_TRACE").as_deref(),
        Ok("1") | Ok("true") | Ok("yes") | Ok("on")
    )
}

/// Initialize the rayon global thread pool with appropriate stack size and
/// thread count for compilation workloads.
///
/// Compilation threads need large stacks (16 MiB) because monomorphization,
/// HIR lowering, and codegen can produce deep call stacks. Without this,
/// rayon's default 2 MiB stacks can overflow on complex modules.
///
/// The pool is initialized exactly once per process via `std::sync::Once`.
/// Subsequent calls are no-ops (safe for tests and repeated builds).
///
/// Thread count resolution order:
/// 1. Explicit `num_threads` from `NativeBuildConfig`
/// 2. `SIMPLE_BOOTSTRAP_THREADS` environment variable
/// 3. `std::thread::available_parallelism()` (all cores)
fn init_rayon_pool(config: &NativeBuildConfig) {
    use std::sync::Once;
    static POOL_INIT: Once = Once::new();

    let num_threads = config
        .num_threads
        .or_else(|| {
            std::env::var("SIMPLE_BOOTSTRAP_THREADS")
                .ok()
                .and_then(|s| s.parse::<usize>().ok())
                .filter(|&n| n > 0)
        })
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1));

    let stack_size = config.stack_size;

    POOL_INIT.call_once(|| {
        let result = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .stack_size(stack_size)
            .thread_name(|idx| format!("spl-compile-{}", idx))
            .build_global();
        if let Err(e) = result {
            // Pool was already initialized (e.g., by a test or library user).
            // This is not fatal — we just use whatever pool exists.
            eprintln!("[rayon] pool already initialized, using existing: {e}");
        }
    });
}

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
    // Resolve . and .. and symlinks
    let mut out = PathBuf::new();
    for comp in abs.components() {
        match comp {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            c => {
                out.push(c);
                if out.is_symlink() {
                    if let Ok(target) = std::fs::read_link(&out) {
                        if target.is_absolute() {
                            out = target;
                        } else {
                            out.pop();
                            out.push(&target);
                        }
                    }
                }
            }
        }
    }
    out
}

/// CLI-provided runtime library directory override.
/// Set before building; read by `find_native_all_library()` and `find_runtime_library()`.
pub(crate) static RUNTIME_PATH_OVERRIDE: OnceLock<PathBuf> = OnceLock::new();

/// Set the runtime path override (called from CLI arg parsing).
pub fn set_runtime_path_override(path: PathBuf) {
    let _set_result = RUNTIME_PATH_OVERRIDE.set(path);
}

/// CLI-provided cross-compilation target override.
/// Set before building; read by `compile_file_to_object()` to select the right backend target.
static TARGET_OVERRIDE: OnceLock<simple_common::target::Target> = OnceLock::new();

/// Set the cross-compilation target override (called from CLI arg parsing).
pub fn set_target_override(target: simple_common::target::Target) {
    let _set_result = TARGET_OVERRIDE.set(target);
}

/// Get the effective compilation target (override or host).
pub(crate) fn effective_target() -> simple_common::target::Target {
    TARGET_OVERRIDE
        .get()
        .copied()
        .unwrap_or_else(simple_common::target::Target::host)
}

/// Grouped duplicate struct definitions: bare type name → list of field-lists.
type DuplicateStructDefs = std::sync::Arc<std::collections::HashMap<String, Vec<Vec<(String, simple_parser::Type)>>>>;
/// Enum definitions: enum name → list of (variant name, optional payload arity).
type EnumDefs = std::sync::Arc<std::collections::HashMap<String, Vec<(String, Option<usize>)>>>;

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
    /// Project-wide trait implementations used to validate virtual dispatch.
    pub trait_impls: std::sync::Arc<std::collections::HashMap<String, Vec<String>>>,
    /// Global struct definitions: struct_name -> [(field_name, field_type_name)].
    /// Shared across all compilation units for consistent cross-module field offsets.
    pub struct_defs: std::sync::Arc<std::collections::HashMap<String, Vec<(String, simple_parser::Type)>>>,
    /// Duplicate global struct/class definitions grouped by bare type name.
    /// Used only for bounded field-name disambiguation when `struct_defs`
    /// lost information due to same-name collisions across modules.
    pub duplicate_struct_defs: DuplicateStructDefs,
    /// Global enum definitions: enum_name -> [(variant_name, payload_arity)].
    /// Shared across all compilation units. The HIR lowerer consumes this in
    /// `compile_file_to_object` to eagerly seed `module.types.name_to_id` and
    /// `globals` with real enum TypeIds for cross-module enum receivers
    /// (W15-H follow-up to W13-F: 29 stage4 sites where
    /// `expr/access.rs::lower_field_access` was emitting `Global(EnumName)`
    /// with `ty=ANY` because the enum reached the file via re-export but
    /// not via a direct `use` chain that triggered `preregister_imported_type_names`).
    pub enum_defs: EnumDefs,
    /// Set of mangled names that correspond to module-level data (`val`/`var`/
    /// `const`/`static`) rather than functions. Consulted by the cranelift
    /// backend so cross-module imported data constants are declared as
    /// `Linkage::Import` DATA (load value from memory) instead of being
    /// misrouted through the function-import fast path (which would return
    /// the symbol's address as the "value").
    pub data_exports: std::sync::Arc<std::collections::HashSet<String>>,
    /// Mangled function name → declared parameter count for cross-module free
    /// functions. Used to strip spurious nil receivers from module-qualified
    /// calls (see `ImportMapResult::fn_arities`).
    pub fn_arities: std::sync::Arc<std::collections::HashMap<String, usize>>,
    pub fn_return_types: std::sync::Arc<std::collections::HashMap<String, simple_parser::Type>>,
    /// When true, pass `struct_defs` to the HIR lowerer so cross-module field
    /// accesses (e.g. `fb_info.addr.addr`) can resolve to real FieldGet instructions
    /// instead of falling through to dynamic MethodCall (which becomes
    /// `rt_function_not_found`). Safe only when the compiled file set is small
    /// enough that the "most fields wins" ambiguity heuristic in
    /// `get_field_info` is unlikely to mis-resolve — currently set only for
    /// `--entry-closure` builds.
    pub populate_global_struct_defs: bool,
    /// When true, pass `enum_defs` to the HIR lowerer so cross-module enum
    /// receivers (`TypeKind.Inferred`, `TokenKind.KwPub`, etc.) resolve via
    /// the enum-variant early-return in `expr/access.rs::lower_field_access`
    /// instead of falling through to the field-access fallback that emits
    /// `Cannot infer field type` (W13-F class 1, fixed in W15-H).
    /// Always-on for both bootstrap and non-bootstrap builds — populating
    /// this map only adds enum names to the type registry of files that
    /// don't already have them; existing local definitions (registered in
    /// Pass 0 of `module_pass.rs::lower_module`) take precedence.
    pub populate_global_enum_defs: bool,
}

/// Configuration for native project builds.
#[derive(Debug, Clone)]
pub struct NativeBuildConfig {
    /// Per-file compilation timeout in seconds.
    pub file_timeout: u64,
    /// Stack size per compilation thread (also applied to rayon pool workers).
    /// Monomorphization and HIR lowering can produce deep call stacks,
    /// requiring 16 MiB or more per thread.
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
    /// Runtime bundle selection: "auto", "simple-core", the bootstrap
    /// fallback "core-c-bootstrap" (legacy aliases: "runtime"/"core"/"core_c"),
    /// or the explicit hosted lane ("hosted"/"rust-hosted"/"all" aliases).
    pub runtime_bundle: String,
    /// Discover files from the explicit entrypoint's reachable import closure.
    pub entry_closure: bool,
    /// Cross-compilation target (e.g. "riscv32-unknown-none"). None = host.
    pub target: Option<simple_common::target::Target>,
    /// Linker script path for freestanding/OS targets.
    pub linker_script: Option<PathBuf>,
    /// Optimization profile for native executable builds.
    pub opt_level: NativeOptimizationLevel,
    /// Emit a static archive from compiled Simple objects instead of linking
    /// an executable.
    pub emit_archive: bool,
}

impl Default for NativeBuildConfig {
    fn default() -> Self {
        Self {
            // Large legitimate files (3000+-line controllers, big re-export hubs)
            // need more than 60s for full parse->lowering->codegen; they compile
            // fine, just slowly. Raised to avoid spurious bootstrap aborts.
            file_timeout: 300,
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
            opt_level: NativeOptimizationLevel::default_for_native_executable(),
            emit_archive: false,
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
    #[must_use]
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
    #[must_use]
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
    #[must_use]
    pub fn config(mut self, config: NativeBuildConfig) -> Self {
        self.config = config;
        self
    }

    /// Set verbose mode.
    #[must_use]
    pub fn verbose(mut self, v: bool) -> Self {
        self.config.verbose = v;
        self
    }

    /// Set strip mode.
    #[must_use]
    pub fn strip(mut self, s: bool) -> Self {
        self.config.strip = s;
        self
    }

    /// Set number of threads.
    #[must_use]
    pub fn threads(mut self, n: usize) -> Self {
        self.config.num_threads = Some(n);
        self
    }

    /// Set per-file timeout.
    #[must_use]
    pub fn timeout(mut self, secs: u64) -> Self {
        self.config.file_timeout = secs;
        self
    }

    /// Set the entry file whose `main` function becomes the program entry point (`spl_main`).
    #[must_use]
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
    ///
    /// # Errors
    ///
    /// Returns an error when file discovery, source loading, incremental cache
    /// setup, compilation, or linking fails.
    pub fn build(self) -> Result<NativeBuildResult, String> {
        if self
            .config
            .target
            .is_some_and(|target| target.os == simple_common::target::TargetOS::FreeBSD && !target.is_host())
        {
            return Err("cross-target FreeBSD executable and archive builds are unsupported without a FreeBSD toolchain and sysroot; build on FreeBSD or emit an object instead".to_string());
        }

        crate::codegen::inline_asm::clear_inline_asm_blocks();

        let rust_trace = native_project_rust_trace_enabled();
        if rust_trace {
            eprintln!("[native-rust-trace] builder start:");
            eprintln!("  project_root={}", self.project_root.display());
            eprintln!("  source_root={}", self.source_root.display());
            eprintln!(
                "  source_dirs={}",
                self.source_dirs
                    .iter()
                    .map(|p| p.display().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            eprintln!(
                "  entry_file={}",
                self.entry_file
                    .as_ref()
                    .map_or("<none>".to_string(), |p| p.display().to_string())
            );
            eprintln!("  entry_closure={}", self.config.entry_closure);
            eprintln!("  cache_dir={}", self.cache_dir().display());
        }

        // 0. Initialize rayon thread pool with compilation-appropriate stack
        //    size and thread count. This must happen before any par_iter usage.
        if self.config.parallel {
            init_rayon_pool(&self.config);
        }

        // 1. Discover files
        let (files, file_sources) = if self.config.entry_closure {
            let entry_file = self
                .entry_file
                .as_ref()
                .ok_or_else(|| "entry-closure requires --entry".to_string())?;
            let file_sources = self.discover_reachable_files_with_sources(entry_file)?;
            let files = file_sources.iter().map(|(path, _)| path.clone()).collect();
            (files, file_sources)
        } else {
            let files = self.discover_files()?;
            let mut file_sources = Vec::with_capacity(files.len());
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
            (files, file_sources)
        };
        if files.is_empty() {
            return Err("No .spl files found in source directories".to_string());
        }
        if rust_trace {
            eprintln!("[native-rust-trace] discovered {} file(s)", files.len());
            for (idx, path) in files.iter().take(12).enumerate() {
                eprintln!("  discovered[{idx}]={}", path.display());
            }
            if files.len() > 12 {
                eprintln!("  discovered_more={}", files.len() - 12);
            }
        }
        if self.config.verbose {
            eprintln!("Found {0} .spl files", files.len());
        }

        // 2. Set up incremental state
        let cache_dir = self.cache_dir();
        let objects_dir = cache_dir.join("objects");

        if self.config.clean {
            if self.config.verbose {
                eprintln!(
                    "Clean build: removing cache at {cache_dir_display}",
                    cache_dir_display = cache_dir.display()
                );
            }
            let _remove_cache_result = std::fs::remove_dir_all(&cache_dir);
        }

        let use_incremental = self.config.incremental && !self.config.clean;
        if use_incremental {
            std::fs::create_dir_all(&objects_dir).map_err(|e| format!("create cache dir: {e}"))?;
        }

        // 3. Create temp directory for .o files
        let mut temp_dir = Some(tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?);
        let temp_dir_path = temp_dir
            .as_ref()
            .map(|dir| dir.path().to_path_buf())
            .ok_or_else(|| "tempdir unexpectedly missing".to_string())?;

        // 4. Read all source files and determine dirty set
        let compile_start = Instant::now();
        // Deduplicate files for compilation (symlink aliases compile once, but
        // all paths remain in file_sources for import map indexing).
        let compile_indices: std::collections::HashSet<usize> = if self.config.entry_closure {
            // Entry-closure discovery already canonicalizes and deduplicates the
            // reachable file set, so we can compile every discovered file directly.
            (0..files.len()).collect()
        } else {
            Self::deduplicate_for_compilation(&files).into_iter().collect()
        };

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
                if !is_entry && !source_may_emit_inline_asm_sidecar(source) {
                    let per_file_root = self.effective_source_root_for(path);
                    let module_prefix = crate::codegen::common_backend::module_prefix_from_path(path, &per_file_root);
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
        if rust_trace {
            eprintln!(
                "[native-rust-trace] dirty set: cached={} to_compile={} use_incremental={}",
                cached_count,
                to_compile.len(),
                use_incremental
            );
            for (idx, path, _) in to_compile.iter().take(12) {
                eprintln!("  compile[{idx}]={}", path.display());
            }
        }
        if self.config.verbose && use_incremental {
            eprintln!("Incremental: {cached_count} cached, {} to compile", to_compile.len());
        }

        // Canonicalize the entry file path for comparison during compilation
        let canonical_entry: Option<PathBuf> = self.entry_file.as_ref().map(|p| safe_canonicalize(p));
        if self.config.verbose {
            match &canonical_entry {
                Some(p) => eprintln!("Canonical entry: {entry_display}", entry_display = p.display()),
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
                        eprintln!("Import candidates for {symbol}:");
                        for candidate in candidates {
                            eprintln!("  {candidate}");
                        }
                    } else {
                        eprintln!("Import candidates for {symbol}: <none>");
                    }
                }
            }
            ModuleImports {
                import_map: std::sync::Arc::new(result.map),
                ambiguous_names: std::sync::Arc::new(result.ambiguous),
                all_mangled: std::sync::Arc::new(result.all_mangled),
                re_exports: std::sync::Arc::new(result.re_exports),
                trait_impls: std::sync::Arc::new(result.trait_impls),
                struct_defs: std::sync::Arc::new(result.struct_defs),
                duplicate_struct_defs: std::sync::Arc::new(result.duplicate_struct_defs),
                enum_defs: std::sync::Arc::new(result.enum_defs),
                data_exports: std::sync::Arc::new(result.data_exports),
                fn_arities: std::sync::Arc::new(result.fn_arities),
                fn_return_types: std::sync::Arc::new(result.fn_return_types),
                populate_global_struct_defs: true,
                populate_global_enum_defs: true,
            }
        } else {
            ModuleImports {
                import_map: std::sync::Arc::new(std::collections::HashMap::new()),
                ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
                all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
                re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
                trait_impls: std::sync::Arc::new(std::collections::HashMap::new()),
                struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
                duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
                enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
                data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
                fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
                fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
                populate_global_struct_defs: false,
                populate_global_enum_defs: false,
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
        let mut object_paths_with_indices: Vec<(usize, PathBuf)> = cached_objects;
        let mut failures = Vec::new();
        let mut freshly_compiled: Vec<(usize, PathBuf)> = Vec::new();

        for result in results {
            match result {
                Ok((idx, path)) => {
                    freshly_compiled.push((idx, path.clone()));
                    object_paths_with_indices.push((idx, path));
                }
                Err((path, msg)) => failures.push((path, msg)),
            }
        }

        object_paths_with_indices.sort_by_key(|(idx, _)| *idx);
        let mut object_paths: Vec<PathBuf> = object_paths_with_indices.into_iter().map(|(_, path)| path).collect();

        let compiled = object_paths.len();
        let failed = failures.len();

        // Always log individual failures when present (bootstrap visibility).
        if failed > 0 {
            eprintln!("\nFAILED FILES ({failed}):");
            for (path, msg) in &failures {
                eprintln!("  - {} => {}", path.display(), msg);
            }
            eprintln!(); // spacer
            let summary = failures
                .iter()
                .map(|(path, msg)| format!("{}: {}", path.display(), msg))
                .collect::<Vec<_>>()
                .join("\n");
            return Err(format!(
                "native-build aborted: {failed} file(s) failed to compile\n{summary}"
            ));
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

        if object_paths.is_empty() {
            return Err(format!("All {0} files failed to compile", files.len()));
        }

        if let Some(security_registry_o) = self.generate_security_registry_init_object(&temp_dir_path, &file_sources)? {
            object_paths.push(security_registry_o);
        }

        // 6. Cache freshly compiled objects
        if use_incremental {
            for (idx, obj_path) in &freshly_compiled {
                if let Some((path, source)) = file_sources.get(*idx) {
                    let is_entry = is_entry_file(path, &canonical_entry);
                    let per_file_root = self.effective_source_root_for(path);
                    let module_prefix = crate::codegen::common_backend::module_prefix_from_path(path, &per_file_root);
                    let hash = object_cache_key(
                        source,
                        is_entry,
                        &self.config.backend,
                        self.config.no_mangle,
                        &module_prefix,
                    );
                    let cached_o = objects_dir.join(format!("{:016x}.o", hash));
                    let _copy_result = std::fs::copy(obj_path, cached_o);
                }
            }
        }

        // 7. Link or archive
        let link_start = Instant::now();
        let mut final_object_paths = object_paths;
        if self.config.emit_archive {
            if let Some(init_o) = self.generate_init_caller(&temp_dir_path, &final_object_paths, None)? {
                final_object_paths.push(init_o);
            }
        }
        let link_result = if self.config.emit_archive {
            self.archive_objects(&final_object_paths)
        } else {
            self.link_objects(&final_object_paths, &imports)
        };
        let link_time = link_start.elapsed();

        // On link failure, optionally keep objects for debugging
        if let Err(e) = link_result {
            if let Some(dir) = temp_dir.take() {
                let path = dir.keep();
                eprintln!(
                    "Link failed. Objects kept at: {path_display}",
                    path_display = path.display()
                );
            }
            return Err(e);
        }

        // Optionally keep the temporary object directory for debugging.
        if std::env::var("SIMPLE_KEEP_NATIVE_OBJS").is_ok() {
            if let Some(dir) = temp_dir.take() {
                let path = dir.keep();
                eprintln!(
                    "Keeping native object files in {path_display}",
                    path_display = path.display()
                );
            }
        }

        let binary_size = std::fs::metadata(&self.output).map(|m| m.len()).unwrap_or(0);

        if self.config.verbose {
            eprintln!(
                "{}: {} ({} KB) in {:.1}s",
                if self.config.emit_archive { "Archived" } else { "Linked" },
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

    fn archive_objects(&self, object_paths: &[PathBuf]) -> Result<(), String> {
        if let Some(parent) = self.output.parent() {
            std::fs::create_dir_all(parent).map_err(|e| format!("create archive output dir: {e}"))?;
        }
        if self.output.exists() {
            std::fs::remove_file(&self.output)
                .map_err(|e| format!("remove existing archive {}: {e}", self.output.display()))?;
        }
        let ar = find_archive_tool();
        let output = archive_create_command(&ar, &self.output, object_paths, false, false)
            .output()
            .map_err(|e| format!("run archive tool {ar}: {e}"))?;
        if output.status.success() {
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output.stderr);
            Err(format!("archive failed ({}): {}", ar, stderr))
        }
    }

    fn generate_security_registry_init_object(
        &self,
        temp_dir: &Path,
        file_sources: &[(PathBuf, String)],
    ) -> Result<Option<PathBuf>, String> {
        if !effective_target().is_host() {
            return Ok(None);
        }
        let Some(registry_sdn) = security_registry_sdn_from_sources(file_sources)? else {
            return Ok(None);
        };

        let cxx = tools::find_cxx_compiler();
        let is_clang_cl = cxx.contains("clang-cl");
        let escaped = cxx_raw_string_literal(&registry_sdn);
        let loader_decl = if is_clang_cl {
            r#"extern "C" unsigned long long rt_security_load_registry_sdn(const unsigned char*, unsigned long long);"#
        } else {
            r#"extern "C" unsigned long long rt_security_load_registry_sdn(const unsigned char*, unsigned long long) __attribute__((weak));"#
        };
        let source = format!(
            r#"
{loader_decl}
static const unsigned char SIMPLE_SECURITY_REGISTRY_SDN[] = R"SECURITY_SDN({escaped})SECURITY_SDN";
extern "C" void __module_init_security_registry(void) {{
    if (rt_security_load_registry_sdn) {{
        rt_security_load_registry_sdn(SIMPLE_SECURITY_REGISTRY_SDN, sizeof(SIMPLE_SECURITY_REGISTRY_SDN) - 1);
    }}
}}
"#
        );
        let source_path = temp_dir.join("_security_registry_init.cpp");
        std::fs::write(&source_path, source).map_err(|e| format!("write security registry init: {e}"))?;

        let object_path = temp_dir.join("_security_registry_init.o");
        let status = if is_clang_cl {
            std::process::Command::new(&cxx)
                .arg("/c")
                .arg("/O2")
                .arg("/Gy")
                .arg(format!("/Fo{}", object_path.display()))
                .arg(&source_path)
                .status()
                .map_err(|e| format!("compile security registry init: {e}"))?
        } else {
            std::process::Command::new(&cxx)
                .args(["-c", "-O2", "-ffunction-sections", "-fdata-sections", "-o"])
                .arg(&object_path)
                .arg(&source_path)
                .status()
                .map_err(|e| format!("compile security registry init: {e}"))?
        };
        if !status.success() {
            return Err(format!("compile security registry init failed ({})", cxx));
        }
        Ok(Some(object_path))
    }
}

fn security_registry_sdn_from_sources(file_sources: &[(PathBuf, String)]) -> Result<Option<String>, String> {
    let mut registry_sdn = String::new();
    for (path, source) in file_sources {
        if !source_may_declare_security(source) {
            continue;
        }
        let filtered_source =
            crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(source, effective_target().arch);
        let mut parser = Parser::new(&filtered_source);
        let mut ast = parser
            .parse()
            .map_err(|err| format!("parse security registry source {}: {}", path.display(), err))?;
        crate::pipeline::cfg_strip::strip_inactive_cfg_arch_fns(&mut ast, effective_target().arch);
        let module = crate::hir::lower_with_context_lenient(&ast, path)
            .map_err(|err| format!("lower security registry source {}: {}", path.display(), err))?;
        let inventory = build_security_inventory(&module);
        if inventory.security_aop_sdn.contains("require_policy:")
            || inventory.security_aop_sdn.contains("enter_sandbox:")
            || inventory.sandbox_lowering_sdn.contains("lowered_backend:")
        {
            registry_sdn.push_str("# source: ");
            registry_sdn.push_str(&path.display().to_string());
            registry_sdn.push('\n');
            registry_sdn.push_str(&inventory.security_aop_sdn);
            registry_sdn.push('\n');
            registry_sdn.push_str(&inventory.sandbox_lowering_sdn);
            registry_sdn.push('\n');
        }
    }
    if registry_sdn.trim().is_empty() {
        Ok(None)
    } else {
        Ok(Some(registry_sdn))
    }
}

fn source_may_emit_inline_asm_sidecar(source: &str) -> bool {
    source.lines().any(|line| {
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            return false;
        }
        trimmed == "asm"
            || trimmed.starts_with("asm ")
            || trimmed.starts_with("asm{")
            || trimmed.starts_with("asm {")
            || trimmed.starts_with("asm(")
            || trimmed.starts_with("asm:")
    })
}

fn source_may_declare_security(source: &str) -> bool {
    source.lines().any(|line| {
        let trimmed = line.trim_start();
        trimmed.starts_with("security ") || trimmed.starts_with("sandbox ") || trimmed.starts_with("capability ")
    })
}

fn cxx_raw_string_literal(value: &str) -> String {
    value.replace(")SECURITY_SDN\"", ")SECURITY_SDN_\"")
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

/// Fingerprint of the currently running compiler executable.
///
/// Computed once per process (via `OnceLock`) and mixed into every object
/// cache key. The `.simple/native_cache/objects` cache keys on source content
/// only, so when the *compiler itself* changes (a codegen fix to the seed),
/// the generated object for identical source text can silently differ from
/// what's already cached under the old key — but the cache never notices,
/// because nothing about the compiler binary was ever part of the key. That
/// forced every agent to pass `--clean` after any seed rebuild.
///
/// This hashes the full bytes of `std::env::current_exe()`, so it changes
/// deterministically whenever the compiler binary changes and stays stable
/// (and cache hits keep working) across repeated builds with the same
/// binary. Falls back to mtime+size if the exe can't be read (e.g. sandboxed
/// environments), and to a constant if neither is available.
fn compiler_fingerprint() -> u64 {
    static FINGERPRINT: OnceLock<u64> = OnceLock::new();
    *FINGERPRINT.get_or_init(|| {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        match std::env::current_exe() {
            Ok(exe) => match std::fs::read(&exe) {
                Ok(bytes) => {
                    bytes.hash(&mut hasher);
                }
                Err(_) => {
                    if let Ok(meta) = std::fs::metadata(&exe) {
                        meta.len().hash(&mut hasher);
                        if let Ok(modified) = meta.modified() {
                            modified.hash(&mut hasher);
                        }
                    }
                }
            },
            Err(_) => {
                "unknown-compiler-exe".hash(&mut hasher);
            }
        }
        hasher.finish()
    })
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
///
/// CPU profile also affects object code. A freestanding x86_64 build for
/// QEMU's baseline CPU must not reuse cached host-feature objects that contain
/// BMI/AVX instructions.
///
/// The running compiler's own fingerprint (see `compiler_fingerprint`) is
/// also mixed in: identical source compiled by two different compiler
/// binaries (e.g. before/after a seed codegen fix) must not collide on the
/// same cached `.o`, or codegen changes get silently masked by stale cache
/// hits.
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
    std::env::var("SIMPLE_NATIVE_CPU").unwrap_or_default().hash(&mut hasher);
    active_simd_tier_name().hash(&mut hasher);
    compiler_fingerprint().hash(&mut hasher);
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
