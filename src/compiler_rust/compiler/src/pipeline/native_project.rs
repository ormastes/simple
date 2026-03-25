//! Native project builder: compile all .spl files → .o → linked binary.
//!
//! Orchestrates the full native build pipeline:
//! 1. Discover .spl files in source directories
//! 2. Compile each file in parallel (Parse → Mono → HIR → MIR → Cranelift → .o)
//! 3. Link all .o files into a native binary
//!
//! Supports incremental compilation via content-hash keyed .o cache,
//! and auto-detected linker selection via `LinkerBuilder`.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use rayon::prelude::*;

use crate::codegen::common_backend::module_prefix_from_path;
use crate::codegen::Codegen;
use crate::hir::Lowerer;
use crate::incremental::SourceInfo;
use crate::module_resolver::ModuleResolver;
use crate::monomorphize::monomorphize_module;

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
    /// Codegen backend: "cranelift" (default) or "llvm".
    pub backend: String,
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
            backend: "cranelift".to_string(),
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
    source_dirs: Vec<PathBuf>,
    /// Project root directory.
    project_root: PathBuf,
    /// Source root for module prefix computation (typically project_root/src).
    source_root: PathBuf,
    /// Output binary path.
    output: PathBuf,
    /// Build configuration.
    config: NativeBuildConfig,
    /// Entry file whose `main` becomes `spl_main` (the program entry point).
    entry_file: Option<PathBuf>,
}

impl NativeProjectBuilder {
    /// Create a new builder.
    pub fn new(project_root: PathBuf, output: PathBuf) -> Self {
        let project_root = std::fs::canonicalize(&project_root).unwrap_or(project_root);
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
        self.entry_file = Some(std::fs::canonicalize(&path).unwrap_or(path));
        self
    }

    /// Resolve the cache directory path.
    fn cache_dir(&self) -> PathBuf {
        self.config
            .cache_dir
            .clone()
            .unwrap_or_else(|| self.project_root.join(".simple/native_cache"))
    }

    /// Build the project.
    pub fn build(self) -> Result<NativeBuildResult, String> {
        // 1. Discover files
        let files = self.discover_files();
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
            // Normalize CRLF → LF for cross-platform compatibility
            if source.contains('\r') {
                source = source.replace('\r', "");
            }
            file_sources.push((path.clone(), source));
        }

        // Determine which files need recompilation via content hash
        let mut to_compile: Vec<(usize, PathBuf, String)> = Vec::new();
        let mut cached_objects: Vec<(usize, PathBuf)> = Vec::new();

        if use_incremental {
            // Canonicalize entry early so we can force-recompile the entry file
            let canon_entry_for_cache: Option<PathBuf> =
                self.entry_file.as_ref().and_then(|p| std::fs::canonicalize(p).ok());
            for (i, (path, source)) in file_sources.iter().enumerate() {
                // Always recompile the entry file (its main→spl_main renaming depends on is_entry)
                let is_entry = is_entry_file(path, &canon_entry_for_cache);
                if !is_entry {
                    let hash = object_cache_key(source, is_entry, &self.config.backend, self.config.no_mangle);
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
                to_compile.push((i, path.clone(), source.clone()));
            }
        }

        let cached_count = cached_objects.len();
        if self.config.verbose && use_incremental {
            eprintln!("Incremental: {} cached, {} to compile", cached_count, to_compile.len());
        }

        // Canonicalize the entry file path for comparison during compilation
        let canonical_entry: Option<PathBuf> = self.entry_file.as_ref().and_then(|p| std::fs::canonicalize(p).ok());
        if self.config.verbose {
            match &canonical_entry {
                Some(p) => eprintln!("Canonical entry: {}", p.display()),
                None => eprintln!("Canonical entry: <none>"),
            }
        }

        // 4b. Discovery phase: build import map for cross-module function resolution.
        // Parse all files to find top-level function definitions and compute their
        // mangled names. Functions with unique names get direct import map entries;
        // ambiguous names (multiple definitions) are left unresolved.
        let imports = if !self.config.no_mangle {
            let result = build_import_map(&file_sources, &self.source_root);
            if self.config.verbose {
                eprintln!(
                    "Import map: {} unique, {} ambiguous function entries, {} modules with re-exports",
                    result.map.len(),
                    result.ambiguous.len(),
                    result.re_exports.len()
                );
            }
            ModuleImports {
                import_map: std::sync::Arc::new(result.map),
                ambiguous_names: std::sync::Arc::new(result.ambiguous),
                all_mangled: std::sync::Arc::new(result.all_mangled),
                re_exports: std::sync::Arc::new(result.re_exports),
            }
        } else {
            ModuleImports {
                import_map: std::sync::Arc::new(std::collections::HashMap::new()),
                ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
                all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
                re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
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
            let critical_failures: Vec<_> = failures
                .iter()
                .filter(|(path, _)| {
                    let p = path.display().to_string();
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
            let critical_failures: Vec<_> = failures
                .iter()
                .filter(|(path, _)| {
                    let p = path.display().to_string();
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
                    let hash = object_cache_key(source, is_entry, &self.config.backend, self.config.no_mangle);
                    let cached_o = objects_dir.join(format!("{:016x}.o", hash));
                    let _ = std::fs::copy(obj_path, cached_o);
                }
            }
        }

        // 7. Link
        let link_start = Instant::now();
        let link_result = self.link_objects(&object_paths);
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

    /// Discover all .spl files in source directories.
    fn discover_files(&self) -> Vec<PathBuf> {
        let mut files = Vec::new();
        for dir in &self.source_dirs {
            if dir.is_dir() {
                collect_spl_files_recursive(dir, &mut files);
            }
        }
        if let Some(entry_file) = &self.entry_file {
            let canonical_entry = std::fs::canonicalize(entry_file).unwrap_or_else(|_| entry_file.clone());
            if !files.iter().any(|path| same_file_path(path, &canonical_entry)) {
                files.push(canonical_entry);
            }
        }
        files.sort();
        files.dedup_by(|a, b| same_file_path(a, b));
        files
    }

    /// Compile entries (index, path, source) in parallel using rayon.
    fn compile_entries_parallel(
        &self,
        entries: &[(usize, PathBuf, String)],
        temp_dir: &Path,
        canonical_entry: &Option<PathBuf>,
        imports: &ModuleImports,
    ) -> Vec<Result<(usize, PathBuf), (PathBuf, String)>> {
        // Configure rayon thread pool if needed
        if let Some(n) = self.config.num_threads {
            let _ = rayon::ThreadPoolBuilder::new().num_threads(n).build_global();
        }

        let project_root = self.project_root.clone();
        let source_root = self.source_root.clone();
        let file_timeout = self.config.file_timeout;
        let stack_size = self.config.stack_size;
        let verbose = self.config.verbose;
        let temp_dir = temp_dir.to_path_buf();
        let total = entries.len();
        let no_mangle = self.config.no_mangle;
        let canonical_entry = canonical_entry.clone();
        let imports = imports.clone();

        entries
            .par_iter()
            .enumerate()
            .map(|(progress_i, (idx, path, source))| {
                let is_entry = is_entry_file(path, &canonical_entry);
                if verbose && is_entry {
                    eprintln!("  [entry] {}", path.display());
                }
                match compile_file_safe(
                    source.clone(),
                    path.clone(),
                    project_root.clone(),
                    source_root.clone(),
                    file_timeout,
                    stack_size,
                    no_mangle,
                    is_entry,
                    imports.clone(),
                ) {
                    Ok(obj_code) => {
                        let obj_path = temp_dir.join(format!("mod_{}.o", idx));
                        std::fs::write(&obj_path, &obj_code).map_err(|e| (path.clone(), format!("write .o: {e}")))?;
                        if verbose && (progress_i + 1) % 50 == 0 {
                            eprintln!("  [{}/{}] compiled", progress_i + 1, total);
                        }
                        Ok((*idx, obj_path))
                    }
                    Err(e) => {
                        let msg = format!("{}: {}", path.display(), e);
                        Err((path.clone(), msg))
                    }
                }
            })
            .collect()
    }

    /// Compile entries sequentially (fallback).
    fn compile_entries_sequential(
        &self,
        entries: &[(usize, PathBuf, String)],
        temp_dir: &Path,
        canonical_entry: &Option<PathBuf>,
        imports: &ModuleImports,
    ) -> Vec<Result<(usize, PathBuf), (PathBuf, String)>> {
        let total = entries.len();
        entries
            .iter()
            .enumerate()
            .map(|(progress_i, (idx, path, source))| {
                let is_entry = is_entry_file(path, canonical_entry);
                if self.config.verbose && is_entry {
                    eprintln!("  [entry] {}", path.display());
                }
                match compile_file_safe(
                    source.clone(),
                    path.clone(),
                    self.project_root.clone(),
                    self.source_root.clone(),
                    self.config.file_timeout,
                    self.config.stack_size,
                    self.config.no_mangle,
                    is_entry,
                    imports.clone(),
                ) {
                    Ok(obj_code) => {
                        let obj_path = temp_dir.join(format!("mod_{}.o", idx));
                        std::fs::write(&obj_path, &obj_code).map_err(|e| (path.clone(), format!("write .o: {e}")))?;
                        if self.config.verbose && (progress_i + 1) % 10 == 0 {
                            eprintln!("  [{}/{}] compiled", progress_i + 1, total);
                        }
                        Ok((*idx, obj_path))
                    }
                    Err(e) => {
                        let msg = format!("{}: {}", path.display(), e);
                        Err((path.clone(), msg))
                    }
                }
            })
            .collect()
    }

    /// Compile the C++ main stub to an object file.
    ///
    /// Uses C++ (clang++) so that the linker inserts C++ runtime initialization
    /// hooks (crtbegin/crtend, __cxa_atexit registration). This is required
    /// because libsimple_native_all.a contains LLVM C++ objects that need
    /// proper static constructor/destructor ordering.
    fn compile_main_stub(&self, temp_dir: &Path) -> Result<PathBuf, String> {
        let main_cpp = temp_dir.join("_main_stub.cpp");
        let cxx = find_cxx_compiler();
        let is_msvc = cxx.contains("clang-cl") || simple_common::platform::cc_detect::is_msvc_target(&cxx);

        let stub_code = if is_msvc {
            // MSVC/clang-cl: no __attribute__((weak)), use pragma alternativename
            r#"
extern "C" {
    int spl_main(void);
    void rt_set_args(int argc, char** argv);
    void __simple_runtime_init(void);
    void __simple_runtime_shutdown(void);
}
#pragma comment(linker, "/ALTERNATENAME:spl_main=_spl_main_stub")
#pragma comment(linker, "/ALTERNATENAME:rt_set_args=_rt_set_args_stub")
#pragma comment(linker, "/ALTERNATENAME:__simple_runtime_init=___simple_runtime_init_stub")
#pragma comment(linker, "/ALTERNATENAME:__simple_runtime_shutdown=___simple_runtime_shutdown_stub")
extern "C" int _spl_main_stub(void) { return 0; }
extern "C" void _rt_set_args_stub(int, char**) {}
extern "C" void ___simple_runtime_init_stub(void) {}
extern "C" void ___simple_runtime_shutdown_stub(void) {}
int main(int argc, char** argv) {
    __simple_runtime_init();
    rt_set_args(argc, argv);
    int r = spl_main();
    __simple_runtime_shutdown();
    return r;
}
"#
        } else {
            // GCC/MinGW: use __attribute__((weak))
            r#"
extern "C" {
    int __attribute__((weak)) spl_main(void);
    void __attribute__((weak)) rt_set_args(int argc, char** argv);
    void __attribute__((weak)) __simple_runtime_init(void);
    void __attribute__((weak)) __simple_runtime_shutdown(void);
    void __attribute__((weak)) __simple_call_module_inits(void);
}
int main(int argc, char** argv) {
    if (__simple_runtime_init) __simple_runtime_init();
    if (__simple_call_module_inits) __simple_call_module_inits();
    if (rt_set_args) rt_set_args(argc, argv);
    int r = spl_main ? spl_main() : 0;
    if (__simple_runtime_shutdown) __simple_runtime_shutdown();
    return r;
}
"#
        };

        std::fs::write(&main_cpp, stub_code).map_err(|e| format!("write main stub: {e}"))?;

        let main_o = temp_dir.join("_main_stub.o");
        // Use C++ compiler for main stub — ensures C++ runtime init hooks
        let output = if cxx.contains("clang-cl") {
            std::process::Command::new(&cxx)
                .arg("/c")
                .arg(format!("/Fo{}", main_o.display()))
                .arg(&main_cpp)
                .output()
                .map_err(|e| format!("compile main stub: {e}"))?
        } else {
            std::process::Command::new(&cxx)
                .args(["-c", "-o"])
                .arg(&main_o)
                .arg(&main_cpp)
                .output()
                .map_err(|e| format!("compile main stub: {e}"))?
        };
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("Failed to compile main stub ({}): {}", cxx, stderr));
        }
        Ok(main_o)
    }

    /// Generate a constructor function that calls all __module_init_* functions.
    /// Scans object files with `nm` to find init function names.
    fn generate_init_caller(&self, temp_dir: &Path, object_paths: &[PathBuf]) -> Result<Option<PathBuf>, String> {
        // Scan objects for __module_init_* symbols
        let mut init_names = Vec::new();
        for obj in object_paths {
            let output = std::process::Command::new("nm")
                .arg("-g") // global symbols only
                .arg(obj)
                .output()
                .map_err(|e| format!("nm: {e}"))?;
            if output.status.success() {
                let stdout = String::from_utf8_lossy(&output.stdout);
                for line in stdout.lines() {
                    if let Some(name) = line.split_whitespace().last() {
                        let name = name.strip_prefix('_').unwrap_or(name);
                        if name.starts_with("__module_init_") {
                            // Sanitize dots → _dot_ for C identifier validity
                            let sanitized = name.replace('.', "_dot_");
                            init_names.push(sanitized);
                        }
                    }
                }
            }
        }
        if init_names.is_empty() {
            return Ok(None);
        }
        init_names.sort();
        init_names.dedup();

        // Generate C source — NOT constructor, called from main() AFTER runtime init
        let mut code = String::from("// Auto-generated: calls all __module_init_* functions\n");
        code.push_str("extern \"C\" {\n");
        for name in &init_names {
            code.push_str(&format!("    void __attribute__((weak)) {}(void);\n", name));
        }
        code.push_str("}\n");
        code.push_str("extern \"C\" void __simple_call_module_inits(void) {\n");
        for name in &init_names {
            code.push_str(&format!("    if ({}) {}();\n", name, name));
        }
        code.push_str("}\n");

        let init_cpp = temp_dir.join("_init_all.cpp");
        std::fs::write(&init_cpp, &code).map_err(|e| format!("write init_all: {e}"))?;

        let init_o = temp_dir.join("_init_all.o");
        let cxx = find_cxx_compiler();
        let status = std::process::Command::new(&cxx)
            .arg("-c")
            .arg("-O2")
            .arg(&init_cpp)
            .arg("-o")
            .arg(&init_o)
            .status()
            .map_err(|e| format!("compile init_all: {e}"))?;
        if !status.success() {
            return Err("compile init_all.cpp failed".into());
        }
        Ok(Some(init_o))
    }

    /// Compile C runtime sources to object files.
    ///
    /// Currently disabled: the Rust runtime library (libsimple_runtime.a) already
    /// provides all 916+ rt_* symbols. Compiling the C sources would cause duplicate
    /// symbol errors with the Rust runtime.
    fn compile_c_runtime(&self, _temp_dir: &Path) -> Result<Vec<PathBuf>, String> {
        Ok(Vec::new())
    }

    /// Link object files into a native binary using LinkerBuilder.
    fn link_objects(&self, object_paths: &[PathBuf]) -> Result<(), String> {
        let temp_dir = object_paths[0].parent().ok_or("no parent for object path")?;

        // Compile the C main stub (defines main() which calls spl_main())
        let main_o = self.compile_main_stub(temp_dir)?;

        // Generate module init caller: scans object files for __module_init_* symbols
        // and generates a __attribute__((constructor)) function that calls them all.
        // This replaces .init_array (which corrupts Mach-O due to object crate bug).
        let init_o = self.generate_init_caller(temp_dir, object_paths)?;

        // Use clang/clang++ as the linker driver — it handles CRT files (crt1.o, crti.o, crtn.o),
        // libc initialization, and library paths automatically.
        // When libsimple_native_all.a is present (always contains LLVM C++ objects),
        // use clang++ to ensure proper C++ runtime initialization ordering.
        let cc = if find_native_all_library().is_some() {
            find_cxx_compiler()
        } else {
            find_c_compiler()
        };
        let is_clang_cl = cc.contains("clang-cl");
        let is_msvc = simple_common::platform::cc_detect::is_msvc_target(&cc);
        let mut cmd = std::process::Command::new(&cc);
        if !is_msvc {
            cmd.arg("-fPIC");
        }

        // macOS: Use ld_classic (Apple's older linker) which is more tolerant
        #[cfg(target_os = "macos")]
        cmd.arg("-Wl,-ld_classic");

        // Linux/FreeBSD: disable PIE for simpler static linking.
        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        cmd.arg("-no-pie");

        if is_clang_cl {
            cmd.arg(&main_o);
            if let Some(ref init) = init_o {
                cmd.arg(init);
            }
            cmd.arg(format!("/Fe:{}", self.output.display()));
        } else {
            cmd.arg("-o").arg(&self.output).arg(&main_o);
            if let Some(ref init) = init_o {
                cmd.arg(init);
            }
        }

        // For large builds, archive objects into a static library first to avoid
        // linker crashes when passing thousands of individual .o files.
        if object_paths.len() > 100 {
            let archive_path = temp_dir.join("libspl_objects.a");
            let ar_tool = find_archive_tool();
            let is_msvc_lib = ar_tool == "lib";

            // Batch ar calls to avoid Windows 32K command-line limit (~2000 objects = ~120K chars).
            // First batch creates the archive (rcs), subsequent batches append (rs).
            const BATCH_SIZE: usize = 200;
            let mut ar_ok = true;
            for (i, chunk) in object_paths.chunks(BATCH_SIZE).enumerate() {
                let status = if is_msvc_lib {
                    // MSVC lib.exe: lib /OUT:archive.lib [existing.lib] obj1.o obj2.o ...
                    // lib.exe has no append mode — always recreate with /OUT: and include
                    // the existing archive as input on subsequent batches.
                    let mut lib_cmd = std::process::Command::new(&ar_tool);
                    lib_cmd.arg(format!("/OUT:{}", archive_path.display()));
                    if i > 0 {
                        lib_cmd.arg(&archive_path);
                    }
                    lib_cmd
                        .args(chunk)
                        .status()
                        .map_err(|e| format!("lib batch {i}: {e}"))?
                } else {
                    let flag = if i == 0 { "rcs" } else { "rs" };
                    std::process::Command::new(&ar_tool)
                        .arg(flag)
                        .arg(&archive_path)
                        .args(chunk)
                        .status()
                        .map_err(|e| format!("ar batch {i}: {e}"))?
                };
                if !status.success() {
                    ar_ok = false;
                    break;
                }
            }
            if !ar_ok {
                // Fallback: try libtool on macOS (also batched)
                #[cfg(target_os = "macos")]
                {
                    let mut sub_archives = Vec::new();
                    for (i, chunk) in object_paths.chunks(BATCH_SIZE).enumerate() {
                        let sub = temp_dir.join(format!("_batch_{}.a", i));
                        let s = std::process::Command::new("libtool")
                            .arg("-static")
                            .arg("-o")
                            .arg(&sub)
                            .args(chunk)
                            .status()
                            .map_err(|e| format!("libtool batch {i}: {e}"))?;
                        if !s.success() {
                            return Err(format!("libtool failed on batch {i}"));
                        }
                        sub_archives.push(sub);
                    }
                    let s = std::process::Command::new("libtool")
                        .arg("-static")
                        .arg("-o")
                        .arg(&archive_path)
                        .args(&sub_archives)
                        .status()
                        .map_err(|e| format!("libtool merge: {e}"))?;
                    if !s.success() {
                        return Err("libtool merge failed".to_string());
                    }
                }
                #[cfg(not(target_os = "macos"))]
                return Err("ar failed to create archive".to_string());
            }
            // Link the archive. Use -force_load/--whole-archive to include all symbols,
            // not just referenced ones (needed for runtime dispatch tables).
            // On macOS, also pass -no_deduplicate for faster linking with large archives.
            #[cfg(target_os = "macos")]
            {
                cmd.arg("-Wl,-force_load").arg(&archive_path);
                cmd.arg("-Wl,-no_deduplicate");
            }
            #[cfg(any(target_os = "linux", target_os = "freebsd"))]
            {
                cmd.arg("-Wl,--whole-archive")
                    .arg(&archive_path)
                    .arg("-Wl,--no-whole-archive");
            }
            #[cfg(target_os = "windows")]
            {
                if is_clang_cl {
                    // clang-cl: archive + MSVC linker flags via /link at end
                    cmd.arg(&archive_path);
                } else if is_msvc {
                    // clang targeting MSVC: use -Wl, prefix for lld-link
                    cmd.arg(format!("-Wl,/WHOLEARCHIVE:{}", archive_path.display()));
                } else {
                    // MinGW/GNU linker
                    cmd.arg("-Wl,--whole-archive")
                        .arg(&archive_path)
                        .arg("-Wl,--no-whole-archive");
                }
            }
        } else {
            for obj in object_paths {
                cmd.arg(obj);
            }
        }

        // Add runtime/compiler library. Prefer combined native_all library
        // (includes Cranelift FFI for self-hosting) over runtime-only.
        if let Some(native_all) = find_native_all_library() {
            cmd.arg(&native_all);
        } else if let Some(runtime) = find_runtime_library() {
            cmd.arg(&runtime);
        }

        // Libraries — via PlatformLinkConfig (single source of truth per OS)
        let link_config = simple_common::platform::link_config::PlatformLinkConfig::for_host();
        for path in &link_config.library_search_paths {
            cmd.arg(format!("-L{}", path));
        }
        if is_clang_cl {
            // clang-cl: pass .lib names directly (MSVC linker convention)
            for lib in &link_config.libraries {
                cmd.arg(format!("{}.lib", lib));
            }
        } else {
            // clang/g++: use -l flag (works for both GNU and MSVC targets)
            for lib in &link_config.libraries {
                cmd.arg(format!("-l{}", lib));
            }
        }
        // macOS-specific: c++ linking when native_all is present
        // (native_all/Cargo.toml hard-codes features=["llvm"])
        if cfg!(target_os = "macos") && find_native_all_library().is_some() {
            if let Some(llvm_lib) = simple_common::platform::cc_detect::find_homebrew_llvm_lib() {
                cmd.arg(format!("-L{}", llvm_lib));
                cmd.arg(format!("-Wl,-rpath,{}", llvm_lib));
            }
            cmd.arg("-lc++");
        }

        // Generate stub object for unresolved symbols + apply linker flags.
        // Strategy is per-OS via PlatformLinkConfig (Weak, WeakDefinition, StrongWithAllowMultiple).
        #[cfg(not(target_os = "windows"))]
        {
            let stubs_o = generate_stub_object(temp_dir, object_paths, &main_o)?;
            cmd.arg(&stubs_o);
        }
        for flag in &link_config.unresolved_symbol_flags {
            cmd.arg(flag);
        }
        #[cfg(target_os = "windows")]
        if is_clang_cl {
            // /link passes remaining args to MSVC linker
            cmd.arg("/link").arg("/WHOLEARCHIVE").arg("/FORCE:MULTIPLE,UNRESOLVED");
        } else if is_msvc {
            cmd.arg("-Wl,/FORCE:UNRESOLVED");
        }

        if self.config.strip {
            #[cfg(target_os = "macos")]
            cmd.arg("-Wl,-S");
            #[cfg(any(target_os = "linux", target_os = "freebsd"))]
            cmd.arg("-Wl,-s");
            #[cfg(target_os = "windows")]
            if is_clang_cl {
                cmd.arg("/link").arg("/DEBUG:NONE");
            } else if is_msvc {
                cmd.arg("-Wl,/DEBUG:NONE");
            } else {
                cmd.arg("-Wl,-s");
            }
        }

        if self.config.verbose {
            eprintln!("Link command: {:?}", cmd);
        }

        let output_result = cmd.output().map_err(|e| format!("link ({cc}): {e}"))?;

        if output_result.status.success() {
            // Report binary size
            if let Ok(meta) = std::fs::metadata(&self.output) {
                eprintln!("Linked: {} ({} KB) via {cc}", self.output.display(), meta.len() / 1024);
            }
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output_result.stderr);
            Err(format!("link failed: {}", stderr))
        }
    }
}

/// Generate a stub object file that provides weak definitions for all unresolved symbols.
///
/// Scans the given object files / archive for undefined symbols that have no definition,
/// then generates a small C file with weak stub functions returning 0 for each.
/// This prevents dyld from crashing at load time on macOS.
#[cfg(any(target_os = "macos", target_os = "freebsd", target_os = "linux"))]
fn generate_stub_object(
    temp_dir: &std::path::Path,
    object_paths: &[PathBuf],
    main_o: &std::path::Path,
) -> Result<PathBuf, String> {
    use std::collections::{HashSet, BTreeSet};

    // Collect all defined and undefined symbols from the objects.
    let mut defined = HashSet::new();
    let mut undefined = BTreeSet::new();

    // Check if an archive exists (for large builds)
    let archive_path = temp_dir.join("libspl_objects.a");
    let scan_paths: Vec<&std::path::Path> = if archive_path.exists() {
        vec![archive_path.as_path(), main_o]
    } else {
        let mut v: Vec<&std::path::Path> = object_paths.iter().map(|p| p.as_path()).collect();
        v.push(main_o);
        v
    };

    for path in &scan_paths {
        let output = std::process::Command::new("nm")
            .arg("-g") // external (global) symbols only
            .arg("-p") // don't sort (faster)
            .arg(path)
            .output()
            .map_err(|e| format!("nm: {e}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            match parts.as_slice() {
                // "                 U _symbol"
                [sym_type, name] if *sym_type == "U" => {
                    undefined.insert(name.to_string());
                }
                // "0000000000000000 T _symbol"  (or D, S, B, etc.)
                [_addr, sym_type, name] if *sym_type != "U" => {
                    defined.insert(name.to_string());
                }
                _ => {}
            }
        }
    }

    // Also scan the runtime library for defined AND undefined symbols.
    // Undefined symbols in the runtime lib (e.g., MSVC __security_cookie from
    // ring/lzma-sys C code) need stubs when linking with MinGW.
    let runtime_lib = find_native_all_library().or_else(find_runtime_library);
    if let Some(ref rt_path) = runtime_lib {
        let output = std::process::Command::new("nm")
            .arg("-g")
            .arg("-p")
            .arg(rt_path)
            .output()
            .map_err(|e| format!("nm runtime: {e}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            match parts.as_slice() {
                [sym_type, name] if *sym_type == "U" => {
                    undefined.insert(name.to_string());
                }
                [_addr, sym_type, name] if *sym_type != "U" => {
                    defined.insert(name.to_string());
                }
                _ => {}
            }
        }
    }

    // Scan system libraries for symbols (libc, libm, etc.) — via PlatformLinkConfig
    let plat_config = simple_common::platform::link_config::PlatformLinkConfig::for_host();
    for lib_path in &plat_config.system_scan_libs {
        if std::path::Path::new(lib_path).exists() {
            let mut nm_cmd = std::process::Command::new("nm");
            for flag in &plat_config.nm_flags {
                nm_cmd.arg(flag);
            }
            nm_cmd.arg(lib_path);
            if let Ok(output) = nm_cmd.output() {
                let stdout = String::from_utf8_lossy(&output.stdout);
                for line in stdout.lines() {
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    if let [_addr, sym_type, name] = parts.as_slice() {
                        if *sym_type != "U" {
                            // Strip glibc version suffix: pipe2@@GLIBC_2.9 → pipe2
                            let base = name.split("@@").next().unwrap_or(name);
                            defined.insert(base.to_string());
                            // Also insert the full versioned name in case someone refs it
                            if base != *name {
                                defined.insert(name.to_string());
                            }
                        }
                    }
                }
            }
        }
    }

    // Symbols that are undefined and not defined anywhere → need stubs
    let needs_stub: Vec<String> = undefined
        .into_iter()
        .filter(|s| !defined.contains(s))
        // Skip system/dyld symbols only
        .filter(|s| !s.starts_with("_dyld_") && *s != "_main" && *s != "main")
        // Skip known C standard library / system builtins
        .filter(|s| !is_system_symbol(s))
        // Skip MSVC C++ mangled symbols (start with ?) and __imp_ import thunks
        // These come from MSVC-compiled objects in the runtime lib and are
        // resolved by the system DLLs at load time, not by our stubs.
        .filter(|s| !s.starts_with('?') && !s.starts_with("__imp_"))
        .collect();

    if needs_stub.is_empty() {
        // Generate a minimal empty object
        let stub_c = temp_dir.join("_stubs.c");
        std::fs::write(&stub_c, "/* no stubs needed */\n").map_err(|e| format!("write stubs: {e}"))?;
        let stub_o = temp_dir.join("_stubs.o");
        let status = std::process::Command::new("clang")
            .arg("-c")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_c)
            .status()
            .map_err(|e| format!("compile stubs: {e}"))?;
        if !status.success() {
            return Err("failed to compile empty stubs".to_string());
        }
        return Ok(stub_o);
    }

    eprintln!(
        "Generating {} stub functions for unresolved symbols...",
        needs_stub.len()
    );

    // Generate pure assembly stubs via PlatformLinkConfig + asm_helpers.
    // Each stub returns tagged nil (3). Strategy is per-OS (Weak/WeakDefinition/Strong).
    let mut asm_code = String::with_capacity(needs_stub.len() * 100);
    asm_code.push_str("/* Auto-generated stubs for bootstrap linking */\n");

    let host_target = simple_common::target::Target::host();
    let ret_nil = simple_common::platform::asm_helpers::asm_ret_nil(&host_target);
    let jmp_prefix = simple_common::platform::asm_helpers::asm_jmp_instruction(&host_target);

    for sym in &needs_stub {
        if !plat_config.is_valid_asm_label(sym) {
            continue;
        }

        // __builtin_* symbols → trampoline to real function (macOS only)
        if cfg!(target_os = "macos") && sym.starts_with("___builtin_") {
            let real_fn = format!("_{}", &sym["___builtin_".len()..]);
            asm_code.push_str(&plat_config.generate_builtin_trampoline_asm(sym, jmp_prefix, &real_fn));
            continue;
        }

        asm_code.push_str(&plat_config.generate_stub_asm(sym, ret_nil));
    }

    let stub_s = temp_dir.join("_stubs.s");
    std::fs::write(&stub_s, &asm_code).map_err(|e| format!("write stubs: {e}"))?;

    let stub_o = temp_dir.join("_stubs.o");
    let output = std::process::Command::new("clang")
        .arg("-c")
        .arg("-o")
        .arg(&stub_o)
        .arg(&stub_s)
        .output()
        .map_err(|e| format!("assemble stubs: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("failed to assemble stub functions: {}", stderr));
    }

    Ok(stub_o)
}

/// Check if a mangled symbol name refers to a C standard library / system function.
/// These must NOT be stubbed as weak — the real definitions come from system dylibs.
#[cfg(any(target_os = "macos", target_os = "freebsd", target_os = "linux"))]
fn is_system_symbol(sym: &str) -> bool {
    // Strip leading underscore (macOS C ABI prepends _; ELF/FreeBSD doesn't).
    // Check both original and stripped form so __errno_location matches
    // whether or not the leading _ is stripped.
    let name = sym.strip_prefix('_').unwrap_or(sym);
    is_known_system_name(sym) || is_known_system_name(name)
}

fn is_known_system_name(name: &str) -> bool {
    matches!(
        name,
        // Memory
        "malloc" | "calloc" | "realloc" | "free" | "posix_memalign" | "aligned_alloc" |
        "memcpy" | "memmove" | "memset" | "memcmp" | "memchr" |
        // String
        "strlen" | "strcmp" | "strncmp" | "strcpy" | "strncpy" | "strcat" | "strdup" |
        "strerror" | "strstr" | "strchr" | "strrchr" | "strtol" | "strtoul" | "strtod" |
        "strtoll" | "strtoull" |
        // I/O
        "printf" | "fprintf" | "sprintf" | "snprintf" | "puts" | "fputs" | "fputc" |
        "fwrite" | "fread" | "fopen" | "fclose" | "fflush" | "fseek" | "ftell" |
        "feof" | "ferror" | "fileno" | "fdopen" | "freopen" | "getline" | "getdelim" |
        "stdin" | "stdout" | "stderr" |
        // Math
        "sqrt" | "sqrtf" | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "atan2" |
        "exp" | "expf" | "log" | "logf" | "log2" | "log10" | "pow" | "powf" |
        "fabs" | "fabsf" | "ceil" | "ceilf" | "floor" | "floorf" | "round" | "roundf" |
        "fmod" | "fmodf" | "fmin" | "fmax" | "copysign" | "nan" | "isnan" | "isinf" |
        "trunc" | "truncf" |
        // Process
        "exit" | "_exit" | "abort" | "atexit" | "getenv" | "setenv" | "unsetenv" | "system" |
        "fork" | "execve" | "execvp" | "waitpid" | "kill" | "getpid" | "getppid" |
        // Signals
        "signal" | "sigaction" | "sigemptyset" | "sigfillset" | "sigaddset" |
        // Threads
        "pthread_create" | "pthread_join" | "pthread_detach" | "pthread_self" |
        "pthread_mutex_init" | "pthread_mutex_lock" | "pthread_mutex_unlock" |
        "pthread_mutex_destroy" | "pthread_rwlock_init" | "pthread_rwlock_destroy" |
        "pthread_rwlock_rdlock" | "pthread_rwlock_wrlock" | "pthread_rwlock_unlock" |
        "pthread_cond_init" | "pthread_cond_wait" | "pthread_cond_signal" |
        "pthread_cond_broadcast" | "pthread_cond_destroy" |
        // Dynamic linking
        "dlopen" | "dlclose" | "dlsym" | "dlerror" |
        // File system
        "open" | "close" | "read" | "write" | "lseek" | "stat" | "fstat" | "lstat" |
        "mkdir" | "rmdir" | "unlink" | "rename" | "getcwd" | "chdir" | "access" |
        "realpath" | "readlink" | "symlink" | "opendir" | "readdir" | "closedir" |
        // Network
        "socket" | "bind" | "listen" | "accept" | "connect" | "send" | "recv" |
        "sendto" | "recvfrom" | "setsockopt" | "getsockopt" | "getaddrinfo" |
        "freeaddrinfo" | "inet_ntop" | "inet_pton" | "htons" | "ntohs" | "htonl" |
        // Time
        "time" | "clock" | "clock_gettime" | "gettimeofday" | "nanosleep" | "usleep" | "sleep" |
        // Misc
        "qsort" | "bsearch" | "abs" | "labs" | "rand" | "srand" | "isdigit" | "isalpha" |
        "isspace" | "tolower" | "toupper" | "mmap" | "munmap" | "mprotect" | "sysconf" |
        "pipe" | "dup" | "dup2" | "fcntl" | "ioctl" | "select" | "poll" |
        // glibc internals used by Rust std (stubbing these causes segfaults)
        "gnu_get_libc_version" | "confstr" | "getauxval" | "dl_iterate_phdr" |
        "__libc_start_main" | "__cxa_atexit" | "__cxa_finalize" | "__cxa_thread_atexit_impl" |
        "__errno_location" | "__stack_chk_fail" | "__stack_chk_guard" |
        // POSIX spawn (used by Rust Command)
        "posix_spawn" | "posix_spawnattr_init" | "posix_spawnattr_setflags" |
        "posix_spawnattr_setsigdefault" | "posix_spawnattr_setsigmask" |
        "posix_spawnattr_setpgroup" | "posix_spawnattr_destroy" |
        "posix_spawn_file_actions_init" | "posix_spawn_file_actions_adddup2" |
        "posix_spawn_file_actions_addopen" | "posix_spawn_file_actions_addclose" |
        "posix_spawn_file_actions_destroy" | "posix_spawnp" |
        // Additional libc functions used by Rust std
        "setlocale" | "nl_langinfo" | "getpwuid_r" | "getuid" | "geteuid" |
        "prctl" | "sched_getaffinity" | "getrandom" | "syscall" |
        "epoll_create1" | "epoll_ctl" | "epoll_wait" | "eventfd" |
        "futex" | "madvise" | "mremap" | "mincore"
    )
}

/// Compile a single .spl file to object code.
/// Find the matching `>` for a string starting with `<...>`, handling nested `<>`.
/// Returns the index of the closing `>` relative to the input string.
fn find_balanced_gt(s: &str) -> Option<usize> {
    if !s.starts_with('<') {
        return None;
    }
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        if c == '<' {
            depth += 1;
        } else if c == '>' {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
    }
    None
}

/// Try alternate name forms to resolve a call target through use_map/import_map.
/// MIR generates `Type__method` but import_map uses `Type.method` (and vice versa).
fn resolve_name_variants(
    name: &str,
    use_map: &std::collections::HashMap<String, String>,
    import_map: &std::collections::HashMap<String, String>,
) -> Option<String> {
    // Try Type__method → Type.method
    if let Some(pos) = name.find("__") {
        let type_part = &name[..pos];
        let method_part = &name[pos + 2..];
        let dotted = format!("{}.{}", type_part, method_part);
        if let Some(resolved) = use_map.get(&dotted).or_else(|| import_map.get(&dotted)) {
            return Some(resolved.clone());
        }
        // Also try all-lowercase joined: "OptimizationConfig__speed" → "optimizationconfig_speed"
        // (desugar creates Type__method but actual fn may be typename_method in lowercase)
        let lower_joined = format!("{}_{}", type_part.to_lowercase(), method_part);
        if let Some(resolved) = use_map.get(&lower_joined).or_else(|| import_map.get(&lower_joined)) {
            return Some(resolved.clone());
        }
        // Try lowercase no-separator: "OptimizationConfig__speed" → "optimizationconfigspeed"
        let lower_no_sep = format!("{}{}", type_part.to_lowercase(), method_part.to_lowercase());
        if let Some(resolved) = import_map.get(&lower_no_sep) {
            return Some(resolved.clone());
        }
    }
    // Try Type.method → Type__method
    if let Some(pos) = name.find('.') {
        let underscored = format!("{}__{}", &name[..pos], &name[pos + 1..]);
        if let Some(resolved) = use_map.get(&underscored).or_else(|| import_map.get(&underscored)) {
            return Some(resolved.clone());
        }
        // Also try replacing ALL dots with `__` for module-qualified names
        // e.g., "types.locale_en_us" → "types__locale_en_us"
        let all_under = name.replace('.', "__");
        if all_under != underscored {
            if let Some(resolved) = use_map.get(&all_under).or_else(|| import_map.get(&all_under)) {
                return Some(resolved.clone());
            }
        }
        // Try the part after the last dot as a raw function name in import_map
        // e.g., "types.locale_en_us" → look up "locale_en_us"
        let func_part = &name[pos + 1..];
        if !func_part.is_empty() {
            if let Some(resolved) = use_map.get(func_part).or_else(|| import_map.get(func_part)) {
                return Some(resolved.clone());
            }
        }
    }
    // Try enum variant constructor pattern: `typename_Variant` → `TypeName.Variant`
    // Heuristic: split at last `_` before an uppercase letter.
    // E.g., `castnumericresult_Int` → try `CastNumericResult.Int` in import_map
    for (i, _) in name.match_indices('_').rev() {
        let variant = &name[i + 1..];
        if variant.is_empty() {
            continue;
        }
        // Variant part must start with uppercase (enum variant convention)
        if !variant.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            continue;
        }
        let prefix_raw = &name[..i];
        if prefix_raw.is_empty() {
            continue;
        }
        // Try to find import_map keys matching `*.{variant}` where the key prefix
        // matches the raw prefix case-insensitively
        for (key, resolved) in import_map.iter().chain(use_map.iter()) {
            if let Some(dot_pos) = key.rfind('.') {
                let key_variant = &key[dot_pos + 1..];
                let key_type = &key[..dot_pos];
                if key_variant == variant
                    && key_type.to_lowercase().replace("_", "") == prefix_raw.to_lowercase().replace("_", "")
                {
                    return Some(resolved.clone());
                }
            }
        }
    }
    None
}

fn suffix_of(name: &str) -> Option<&str> {
    if let Some((_, suffix)) = name.rsplit_once("__") {
        Some(suffix)
    } else if let Some((_, suffix)) = name.rsplit_once('.') {
        Some(suffix)
    } else {
        None
    }
}

/// Build a suffix index from all mangled names for fuzzy method resolution.
///
/// Maps method suffix (e.g., "push") → list of fully-qualified mangled names.
/// Also indexes sub-suffixes: for "Type.method" suffixes, indexes "method" separately.
fn build_suffix_index(
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
) -> std::collections::HashMap<String, Vec<String>> {
    let mut index: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();
    for mangled_list in all_mangled.values() {
        for mangled in mangled_list {
            if let Some(suffix) = suffix_of(mangled) {
                index.entry(suffix.to_string()).or_default().push(mangled.clone());
                // Also index the sub-suffix after '.' within the suffix,
                // but ONLY when the sub-suffix starts with uppercase (enum variant convention).
                // E.g., "CastNumericResult.Int" → also index "Int" → mangled.
                // Skip lowercase sub-suffixes like "new", "get" which are too ambiguous.
                if let Some(dot_pos) = suffix.rfind('.') {
                    let sub_suffix = &suffix[dot_pos + 1..];
                    if !sub_suffix.is_empty() && sub_suffix.starts_with(|c: char| c.is_ascii_uppercase()) {
                        index.entry(sub_suffix.to_string()).or_default().push(mangled.clone());
                    }
                }
            }
        }
    }
    index
}

/// Resolve an unresolved call name by suffix matching against the suffix index.
///
/// Splits `name` at underscores from right to left, trying each suffix
/// (e.g., "tokens_push" → try "push"). Returns the best matching fully-qualified name.
/// Only resolves when there is a single candidate or a confident prefix-based match.
fn resolve_by_suffix(name: &str, suffix_index: &std::collections::HashMap<String, Vec<String>>) -> Option<String> {
    // First: try the whole name as a suffix (e.g., "push" directly)
    if let Some(candidates) = suffix_index.get(name) {
        if candidates.len() == 1 {
            return Some(candidates[0].clone());
        }
    }
    // Then: split at underscores right-to-left
    // "tokens_push" → try "push", "engine_unify" → try "unify"
    for (i, _) in name.match_indices('_').rev() {
        let prefix = &name[..i];
        let method = &name[i + 1..];
        if method.is_empty() || prefix.is_empty() {
            continue;
        }

        if let Some(candidates) = suffix_index.get(method) {
            if candidates.len() == 1 {
                return Some(candidates[0].clone());
            }
            // Disambiguate: only resolve when prefix matches exactly one candidate
            let prefix_lower = prefix.to_lowercase();
            let matching: Vec<_> = candidates
                .iter()
                .filter(|c| c.to_lowercase().contains(&prefix_lower))
                .collect();
            if matching.len() == 1 {
                return Some(matching[0].clone());
            }
            // If multiple match prefix, pick shortest as tiebreaker
            if !matching.is_empty() {
                if let Some(best) = matching.iter().min_by_key(|c| c.len()) {
                    return Some((*best).clone());
                }
            }
        }
    }
    None
}

/// Apply name mangling to a MIR module for the LLVM backend.
///
/// The Cranelift backend does this at codegen time via `module_prefix`, `import_map`, etc.
/// The LLVM backend operates on MIR names directly, so we mangle MIR before passing it.
fn mangle_mir(
    mir: &mut crate::mir::MirModule,
    prefix: &str,
    is_entry: bool,
    import_map: &std::collections::HashMap<String, String>,
    ambiguous_names: &std::collections::HashSet<String>,
    use_map: &std::collections::HashMap<String, String>,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
) -> usize {
    use crate::mir::MirInst;

    let mut unresolved_count: usize = 0;

    // Extern fn declarations from this module (e.g., `extern fn stdin_read_char`)
    // must never be mangled — they resolve to C/runtime symbols at link time.
    let extern_fns = mir.extern_fn_names.clone();

    // Names that should never be mangled (runtime functions, builtins).
    let is_runtime_or_builtin = |name: &str| -> bool {
        extern_fns.contains(name)
            || name.starts_with("rt_")
            || name.starts_with("__simple_")
            || name.starts_with("spl_")
            || name.starts_with("__get_global_")
            || name.starts_with("__set_global_")
            || name.starts_with("bit_")
            || name.starts_with("bitwise_")
            || name.starts_with("ffi_")
            || name.starts_with("rc_box_")
            || name.starts_with("arc_box_")
            // UPPER_CASE.method calls are global variable method calls — pass through unmangled
            || (name.contains('.') && {
                let prefix = name.split('.').next().unwrap_or("");
                !prefix.is_empty() && prefix.chars().all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
            })
            // Variable method call pattern: xxx_builtin_method where the suffix is a known
            // collection method. These are calls like `varname.contains(x)` lowered as
            // `varname_contains(varname, x)` in MIR.
            // Variable method call patterns: only exclude SPECIFIC known non-function patterns
            // Avoid broad suffixes like _get/_map that might match real functions
            || name.ends_with("_contains_key")
            || matches!(
                name,
                "print" | "println" | "eprint" | "eprintln"
                    | "print_raw" | "eprint_raw" | "dprint"
                    | "Ok" | "Err" | "Some" | "None"
                    | "len" | "push" | "pop" | "get" | "clear"
                    | "contains" | "starts_with" | "ends_with"
                    | "concat" | "char_at" | "at" | "join" | "trim"
                    | "split" | "replace" | "to_upper" | "upper"
                    | "to_lower" | "lower" | "to_int" | "to_i64" | "parse_int"
                    | "to_string" | "str" | "slice" | "substring"
                    | "keys" | "values" | "filter" | "sort" | "reverse"
                    | "first" | "last" | "find" | "any" | "all"
                    | "map" | "each" | "reduce" | "fold"
                    | "asm" | "unsafe" | "assert" | "Dict"
                    | "traverse" | "func" | "line_trim"
                    | "malloc" | "free" | "calloc" | "realloc"
                    | "memset" | "memcpy" | "memmove" | "madvise"
                    | "mmap" | "mmap_file" | "munmap"
                    | "readln" | "input" | "input_line" | "input_chars"
                    | "env_var" | "env_args" | "env_clone" | "temp_dir"
                    | "file_mtime" | "file_size_for_mmap"
                    | "fs_read_text" | "fs_write_text" | "fs_has_file" | "fs_has_file_or_dir"
                    | "dir_list_recursive"
                    | "__traits" | "Error" | "VReg" | "Generic"
                    | "trim_end" | "trim_start" | "string_from_byte" | "string_from_char_code"
                    | "from_char_code"
                    | "i64_max" | "text_index_of"
                    | "current_rss_kb_main"
                    | "array_length" | "array_new"
                    | "mmap_read_string" | "mmap_read_bytes"
                    | "interpret_ast" | "execute_compiled"
                    | "handler" | "highlighter" | "completer" | "validator"
                    | "AtomicI64" | "CircuitBreakerConfig" | "RateLimitConfig"
                    | "ResourceLimits" | "TimeoutConfig"
                    | "run_benchmarks" | "run_arch_check"
                    | "validate_databases" | "test_user_service"
                    | "register_builtin_blocks"
                    | "sql_keywords"
                    | "path_pop"
                    | "new_text_lines" | "old_text_lines"
                    | "new_to_clone" | "parent_clone" | "cycle_path_clone"
                    | "upx_ensure_available" | "upx_get_path"
                    | "self_extract_create" | "self_extract_is_compressed"
                    | "JsonBlockDef" | "MathBlockDef" | "ShellBlockDef" | "SqlBlockDef"
                    | "RegexBlockDef" | "MarkdownBlockDef" | "NogradBlockDef" | "LossBlockDef"
                    | "make_cuda_port" | "make_vulkan_port"
                    | "lexer_create_internal"
                    | "mlr_lower_module" | "hir_expr_type" | "hir_pool_get"
                    | "json_to_const"
                    | "linkercompilationcontext_from_objects"
                    | "search_recursive" | "find_decreases" | "find_scope_ancestor"
                    | "calls_itself" | "hover_fn"
                    | "daemon_send_request" | "parse_shell_commands"
                    | "count_leading_chars" | "count_trailing_chars"
                    | "line_trim_start" | "trimmed_is_empty" | "transcriber_is_empty"
                    | "trait__is_none" | "type__size_bytes"
                    | "next_lexeme_value_chars"
                    | "matching_sort_by" | "mp_segments"
            )
    };

    // Build set of locally-defined function names (functions with bodies in this module).
    let local_fn_names: std::collections::HashSet<String> = mir
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| f.name.clone())
        .collect();

    // Build a set of all known fully-qualified imported names (values from import_map/use_map)
    // including both `.` and `_dot_` forms, so we can recognize function definitions that
    // are already cross-module qualified and skip re-mangling them.
    let imported_qualified: std::collections::HashSet<String> = {
        let mut set = std::collections::HashSet::new();
        for v in import_map.values().chain(use_map.values()) {
            set.insert(v.clone());
            // Also add _dot_ form if it contains '.'
            if v.contains('.') {
                set.insert(v.replace('.', "_dot_"));
            }
            // Also add '.' form if it contains '_dot_'
            if v.contains("_dot_") {
                set.insert(v.replace("_dot_", "."));
            }
        }
        set
    };

    // Build a mapping from raw name → mangled name for local functions.
    let mut local_mangled: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for func in &mir.functions {
        let has_body = !func.blocks.is_empty();
        if !has_body {
            // Extern declarations: never mangle
            continue;
        }
        if is_runtime_or_builtin(&func.name) {
            continue;
        }
        // Skip if the function name is already a fully-qualified imported name
        // (e.g., "mod__Type.method" or "mod__Type_dot_method" from cross-module references)
        if imported_qualified.contains(&func.name) {
            continue;
        }
        let mangled = if func.name == "main" {
            if is_entry {
                "spl_main".to_string()
            } else {
                format!("{}__{}", prefix, func.name)
            }
        } else {
            format!("{}__{}", prefix, func.name)
        };
        local_mangled.insert(func.name.clone(), mangled);
    }

    // Build local suffix index from this module's known names (low ambiguity).
    // The global suffix_index from all_mangled is used as a fallback for names
    // not found in the local index.
    let mut local_suffix_index: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();
    for resolved in local_mangled
        .values()
        .chain(use_map.values())
        .chain(import_map.values())
    {
        if let Some(suffix) = suffix_of(resolved) {
            local_suffix_index
                .entry(suffix.to_string())
                .or_default()
                .push(resolved.clone());
            // Also index sub-suffix after '.'
            if let Some(dot_pos) = suffix.rfind('.') {
                let sub_suffix = &suffix[dot_pos + 1..];
                if !sub_suffix.is_empty() {
                    local_suffix_index
                        .entry(sub_suffix.to_string())
                        .or_default()
                        .push(resolved.clone());
                }
            }
        }
    }

    // Build a mapping from raw name → mangled name for local globals.
    let mut local_global_mangled: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for (name, _ty, _is_mut) in &mir.globals {
        if mir.local_globals.contains(name) && !is_runtime_or_builtin(name) {
            local_global_mangled.insert(name.clone(), format!("{}__{}", prefix, name));
        }
    }

    // Phase 1: Rename function definitions
    for func in &mut mir.functions {
        if let Some(mangled) = local_mangled.get(&func.name) {
            func.name = mangled.clone();
        }
    }

    // Phase 2: Rename globals in mir.globals, global_init_values, local_globals
    let mut new_globals = Vec::new();
    for (name, ty, is_mut) in &mir.globals {
        if let Some(mangled) = local_global_mangled.get(name) {
            new_globals.push((mangled.clone(), *ty, *is_mut));
        } else {
            new_globals.push((name.clone(), *ty, *is_mut));
        }
    }
    mir.globals = new_globals;

    let old_init = std::mem::take(&mut mir.global_init_values);
    for (name, val) in old_init {
        if let Some(mangled) = local_global_mangled.get(&name) {
            mir.global_init_values.insert(mangled.clone(), val);
        } else {
            mir.global_init_values.insert(name, val);
        }
    }

    let old_init_strings = std::mem::take(&mut mir.global_init_strings);
    for (name, val) in old_init_strings {
        if let Some(mangled) = local_global_mangled.get(&name) {
            mir.global_init_strings.insert(mangled.clone(), val);
        } else {
            mir.global_init_strings.insert(name, val);
        }
    }

    let old_local = std::mem::take(&mut mir.local_globals);
    for name in old_local {
        if let Some(mangled) = local_global_mangled.get(&name) {
            mir.local_globals.insert(mangled.clone());
        } else {
            mir.local_globals.insert(name);
        }
    }

    // Build a set of all known mangled names (values from import_map/use_map + local_mangled)
    // so we can recognize already-qualified call targets and skip re-mangling them.
    // Include both `.` and `_dot_` forms for cross-module method calls.
    let known_mangled: std::collections::HashSet<String> = {
        let mut set: std::collections::HashSet<String> = import_map
            .values()
            .chain(use_map.values())
            .chain(local_mangled.values())
            .cloned()
            .collect();
        let extras: Vec<String> = set
            .iter()
            .filter_map(|v| {
                if v.contains('.') {
                    Some(v.replace('.', "_dot_"))
                } else if v.contains("_dot_") {
                    Some(v.replace("_dot_", "."))
                } else {
                    None
                }
            })
            .collect();
        set.extend(extras);
        set
    };

    // Phase 3: Rename call targets and global references in instructions.
    // Resolution order: local definition first (prevents imported name shadowing
    // a module's own function), then use_map, then import_map, then raw fallback.
    for func in &mut mir.functions {
        for block in &mut func.blocks {
            for inst in &mut block.instructions {
                match inst {
                    MirInst::Call { target, .. } => {
                        let name = target.name().to_string();
                        if is_runtime_or_builtin(&name) {
                            continue;
                        }
                        // If the call target is already a known fully-qualified mangled name,
                        // skip it — don't re-mangle.
                        if known_mangled.contains(name.as_str()) {
                            continue;
                        }
                        // Also try _dot_ → . conversion for cross-module method calls
                        // e.g., "mod__Type_dot_method" → "mod__Type.method"
                        if name.contains("_dot_") {
                            let converted = name.replace("_dot_", ".");
                            if known_mangled.contains(converted.as_str()) {
                                *target = target.with_name(converted);
                                continue;
                            }
                        }
                        if let Some(mangled) = local_mangled.get(&name) {
                            *target = target.with_name(mangled.clone());
                        } else if let Some(resolved) = use_map.get(&name) {
                            *target = target.with_name(resolved.clone());
                        } else if let Some(resolved) = import_map.get(&name) {
                            *target = target.with_name(resolved.clone());
                        } else if let Some(resolved) = resolve_name_variants(&name, use_map, import_map) {
                            *target = target.with_name(resolved);
                        } else if name.contains('.') {
                            // Dotted call: "Type.method" or "module.function"
                            let method = name.rsplit('.').next().unwrap_or(&name);
                            let type_part = name.split('.').next().unwrap_or("");
                            // First try looking up the full dotted name as a suffix key
                            // (handles "Type.method" keys in the suffix index)
                            let candidates = local_suffix_index
                                .get(&name)
                                .or_else(|| suffix_index.get(&name))
                                .or_else(|| local_suffix_index.get(method))
                                .or_else(|| suffix_index.get(method));
                            if let Some(candidates) = candidates {
                                let best = candidates
                                    .iter()
                                    .find(|c| c.to_lowercase().contains(&type_part.to_lowercase()))
                                    .or_else(|| {
                                        if candidates.len() == 1 {
                                            candidates.first()
                                        } else {
                                            None
                                        }
                                    });
                                if let Some(b) = best {
                                    *target = target.with_name(b.clone());
                                } else {
                                    // Try resolve_by_suffix as last resort for dotted names
                                    if let Some(resolved) = resolve_by_suffix(&name, &local_suffix_index)
                                        .or_else(|| resolve_by_suffix(&name, suffix_index))
                                    {
                                        *target = target.with_name(resolved);
                                    } else {
                                        unresolved_count += 1;
                                        eprintln!(
                                            "warning: unresolved call `{}` in function `{}` (module: {})",
                                            name, func.name, prefix
                                        );
                                    }
                                }
                            } else if let Some(resolved) = resolve_by_suffix(&name, &local_suffix_index)
                                .or_else(|| resolve_by_suffix(&name, suffix_index))
                            {
                                *target = target.with_name(resolved);
                            } else {
                                unresolved_count += 1;
                                eprintln!(
                                    "warning: unresolved call `{}` in function `{}` (module: {})",
                                    name, func.name, prefix
                                );
                            }
                        } else if let Some(resolved) = resolve_by_suffix(&name, &local_suffix_index)
                            .or_else(|| resolve_by_suffix(&name, suffix_index))
                        {
                            *target = target.with_name(resolved);
                        } else {
                            unresolved_count += 1;
                            eprintln!(
                                "warning: unresolved call `{}` in function `{}` (module: {})",
                                name, func.name, prefix
                            );
                        }
                    }
                    MirInst::InterpCall { func_name, .. } => {
                        if is_runtime_or_builtin(func_name) || known_mangled.contains(func_name.as_str()) {
                            continue;
                        }
                        if let Some(mangled) = local_mangled.get(func_name.as_str()) {
                            *func_name = mangled.clone();
                        } else if let Some(resolved) = use_map.get(func_name.as_str()) {
                            *func_name = resolved.clone();
                        } else if let Some(resolved) = import_map.get(func_name.as_str()) {
                            *func_name = resolved.clone();
                        } else if let Some(resolved) = resolve_name_variants(func_name, use_map, import_map) {
                            *func_name = resolved;
                        } else if let Some(resolved) = resolve_by_suffix(func_name, &local_suffix_index)
                            .or_else(|| resolve_by_suffix(func_name, suffix_index))
                        {
                            *func_name = resolved;
                        }
                    }
                    MirInst::GlobalLoad { global_name, .. } | MirInst::GlobalStore { global_name, .. } => {
                        if is_runtime_or_builtin(global_name) || known_mangled.contains(global_name.as_str()) {
                            continue;
                        }
                        if let Some(mangled) = local_global_mangled.get(global_name.as_str()) {
                            *global_name = mangled.clone();
                        } else if let Some(resolved) = use_map.get(global_name.as_str()) {
                            *global_name = resolved.clone();
                        } else if let Some(resolved) = import_map.get(global_name.as_str()) {
                            *global_name = resolved.clone();
                        } else if let Some(resolved) = resolve_name_variants(global_name, use_map, import_map) {
                            *global_name = resolved;
                        } else if let Some(resolved) = resolve_by_suffix(global_name, &local_suffix_index)
                            .or_else(|| resolve_by_suffix(global_name, suffix_index))
                        {
                            *global_name = resolved;
                        }
                    }
                    MirInst::MethodCallStatic { func_name, .. } => {
                        if is_runtime_or_builtin(func_name) || known_mangled.contains(func_name.as_str()) {
                            continue;
                        }
                        // Try _dot_ → . conversion for cross-module method calls
                        if func_name.contains("_dot_") {
                            let converted = func_name.replace("_dot_", ".");
                            if known_mangled.contains(converted.as_str()) {
                                *func_name = converted;
                                continue;
                            }
                        }
                        if let Some(mangled) = local_mangled.get(func_name.as_str()) {
                            *func_name = mangled.clone();
                        } else if let Some(resolved) = use_map
                            .get(func_name.as_str())
                            .or_else(|| import_map.get(func_name.as_str()))
                        {
                            *func_name = resolved.clone();
                        } else if let Some(resolved) = resolve_name_variants(func_name, use_map, import_map) {
                            *func_name = resolved;
                        } else {
                            // Extract method part: "Type.method" → try "method" in suffix indexes
                            let method = func_name.rsplit('.').next().unwrap_or(func_name);
                            let type_part = func_name.split('.').next().unwrap_or("");
                            let type_part_lower = type_part.to_lowercase();
                            let candidates = local_suffix_index.get(method).or_else(|| suffix_index.get(method));
                            if let Some(candidates) = candidates {
                                let best = candidates
                                    .iter()
                                    .find(|c| c.to_lowercase().contains(&type_part_lower))
                                    .or_else(|| {
                                        if candidates.len() == 1 {
                                            candidates.first()
                                        } else {
                                            None
                                        }
                                    });
                                if let Some(b) = best {
                                    *func_name = b.clone();
                                }
                            } else if let Some(resolved) = resolve_by_suffix(func_name, &local_suffix_index)
                                .or_else(|| resolve_by_suffix(func_name, suffix_index))
                            {
                                *func_name = resolved;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    unresolved_count
}

fn compile_file_to_object(
    source: &str,
    file_path: &Path,
    project_root: &Path,
    source_root: &Path,
    no_mangle: bool,
    is_entry: bool,
    imports: &ModuleImports,
) -> Result<Vec<u8>, String> {
    // Bootstrap hack: normalize optional types that older lenient type resolver misses
    let is_bootstrap = std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1");
    let mut source = if is_bootstrap {
        // Protect ?? (null coalesce) before stripping ? from types
        let mut s = source.replace("??", "\x00COALESCE\x00");

        // Handle `.?` (optional chaining / nil-check) before general ? stripping.
        // `.?` followed by non-identifier chars is a nil-check: `val.?` → `val != nil`
        // `.?` followed by identifier is optional chain: `val.?method()` → `val.method()`
        for pat in [".?:", ".?\n", ".?\r\n", ".? ", ".?\t", ".?)", ".?,", ".?]", ".?;"] {
            s = s.replace(pat, &format!(" != nil{}", &pat[2..]));
        }
        // `.?` followed by `=` is nil-check before comparison: `val.? == false`
        s = s.replace(".? =", " != nil =");
        // `.?` at end of file
        if s.ends_with(".?") {
            let len = s.len();
            s.replace_range(len - 2.., " != nil");
        }

        // Strip `?` suffix from nullable types (Type? → Type)
        // Only strip when ? is followed by non-identifier chars (whitespace, punctuation, EOL)
        for pat in ["? ", "?\n", "?\r\n", "?\t", "?,", "?)", "?]", "?>", "?:", "?=", "?;"] {
            while s.contains(pat) {
                s = s.replace(pat, &pat[1..]);
            }
        }
        if s.ends_with('?') {
            s.pop();
        }

        // Restore ?? (null coalesce) operator
        s = s.replace("\x00COALESCE\x00", "??");

        // Replace /* complex expr */ placeholders with 0 (used in main.spl and others
        // as stub expressions that the full compiler interprets but the Rust parser can't)
        s = s.replace("/* complex expr */", "0");
        // Layer connect operator ~> not yet in parser — rewrite to pipe |> for bootstrap
        s = s.replace(" ~> ", " |> ");

        // Function-type parameters not yet supported in Rust parser.
        // Replace `fn(...)` type annotations with `any`.
        // Must handle: fn(text) -> i64, fn([text]) -> Result<T,E>, fn() -> (), fn(m): body
        // Strategy: find `: fn(`, match balanced parens, skip optional `-> RetType`
        // IMPORTANT: Skip strings and comments to avoid mangling docstrings
        {
            let mut result = String::new();
            let bytes = s.as_bytes();
            let mut i = 0;
            let mut in_triple_quote = false;
            let mut in_single_quote = false;
            let mut in_comment = false;
            while i < bytes.len() {
                // Track string/comment state
                if !in_single_quote
                    && !in_comment
                    && i + 2 < bytes.len()
                    && bytes[i] == b'"'
                    && bytes[i + 1] == b'"'
                    && bytes[i + 2] == b'"'
                {
                    in_triple_quote = !in_triple_quote;
                    result.push('"');
                    result.push('"');
                    result.push('"');
                    i += 3;
                    continue;
                }
                if in_triple_quote {
                    result.push(bytes[i] as char);
                    i += 1;
                    continue;
                }
                if !in_comment && !in_single_quote && bytes[i] == b'"' {
                    in_single_quote = true;
                    result.push('"');
                    i += 1;
                    continue;
                }
                if in_single_quote {
                    if bytes[i] == b'\\' && i + 1 < bytes.len() {
                        result.push(bytes[i] as char);
                        result.push(bytes[i + 1] as char);
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        in_single_quote = false;
                    }
                    result.push(bytes[i] as char);
                    i += 1;
                    continue;
                }
                if bytes[i] == b'#' {
                    in_comment = true;
                }
                if in_comment {
                    if bytes[i] == b'\n' {
                        in_comment = false;
                    }
                    result.push(bytes[i] as char);
                    i += 1;
                    continue;
                }
                // Look for `: fn(` pattern (field/param fn-type annotation)
                let is_fn_type = i + 5 < bytes.len()
                    && (bytes[i] == b':' || bytes[i] == b'=')
                    && bytes[i + 1] == b' '
                    && bytes[i + 2] == b'f'
                    && bytes[i + 3] == b'n'
                    && bytes[i + 4] == b'(';
                if !is_fn_type {
                    result.push(bytes[i] as char);
                    i += 1;
                    continue;
                }
                // Keep the `: ` or `= ` prefix
                result.push(bytes[i] as char);
                result.push(' ');
                let fn_start = i + 2; // position of 'f' in 'fn('
                                      // Find matching ')' with balanced parens
                let mut depth = 0i32;
                let mut j = fn_start + 2; // skip 'fn'
                                          // j now points at '('
                depth += 1;
                j += 1;
                while j < bytes.len() && depth > 0 {
                    if bytes[j] == b'(' || bytes[j] == b'[' {
                        depth += 1;
                    } else if bytes[j] == b')' || bytes[j] == b']' {
                        depth -= 1;
                    }
                    j += 1;
                }
                // j is now past the matching ')'
                // Check for optional ` -> RetType`
                if j + 4 <= bytes.len() && &s[j..j + 4] == " -> " {
                    j += 4;
                    // Skip return type: handle balanced <>, (), []
                    let mut type_depth = 0i32;
                    while j < bytes.len() {
                        let c = bytes[j];
                        if c == b'<' || c == b'(' || c == b'[' {
                            type_depth += 1;
                        } else if c == b'>' || c == b')' || c == b']' {
                            if type_depth > 0 {
                                type_depth -= 1;
                            } else {
                                break;
                            }
                        } else if type_depth == 0
                            && (c == b',' || c == b':' || c == b'\n' || c == b'\r' || c == b'#' || c == b' ')
                        {
                            break;
                        }
                        j += 1;
                    }
                }
                // Check what follows: if it's `:` (lambda body), emit `fn()` to keep lambda syntax
                // Otherwise emit `any` for type annotation
                if j < bytes.len() && bytes[j] == b':' {
                    // Lambda: fn(params): body — keep as fn(): body (strip param types)
                    result.push_str("fn()");
                } else {
                    result.push_str("any");
                }
                i = j;
            }
            s = result;
        }
        // Bare `fn` as field type (e.g., `_validator: fn`)
        s = s.replace(": fn\n", ": any\n");
        s = s.replace(": fn\r\n", ": any\r\n");

        // `cli Name:` blocks are not supported — comment out the entire block
        // (the declaration line AND all indented body lines)
        {
            let mut result = String::new();
            let mut in_cli_block = false;
            let mut cli_indent: Option<usize> = None;
            for line in s.lines() {
                let trimmed = line.trim_start();
                if trimmed.starts_with("cli ") && trimmed.contains(':') && !trimmed.starts_with('#') {
                    in_cli_block = true;
                    cli_indent = Some(line.len() - trimmed.len());
                    result.push_str("# ");
                    result.push_str(line);
                    result.push('\n');
                    continue;
                }
                if in_cli_block {
                    let line_indent = line.len() - line.trim_start().len();
                    if trimmed.is_empty() || line_indent > cli_indent.unwrap_or(0) {
                        result.push_str("# ");
                        result.push_str(line);
                        result.push('\n');
                        continue;
                    } else {
                        in_cli_block = false;
                        cli_indent = None;
                    }
                }
                result.push_str(line);
                result.push('\n');
            }
            // Remove trailing newline added by iteration if original didn't have one
            if !s.ends_with('\n') && result.ends_with('\n') {
                result.pop();
            }
            s = result;
        }

        // Generic impl blocks: `impl<T, E> Type<T, E>:` → `impl Type:`
        // Only process lines starting with `impl<` (safe — only at start of line)
        {
            let mut result = String::new();
            for line in s.lines() {
                let trimmed = line.trim_start();
                if trimmed.starts_with("impl<") {
                    let indent = &line[..line.len() - trimmed.len()];
                    // Strip `<...>` after impl
                    let rest = &trimmed[4..]; // skip "impl"
                    let after_generic = if let Some(gt) = find_balanced_gt(rest) {
                        &rest[gt + 1..]
                    } else {
                        rest
                    };
                    // Strip `<...>` from the type name too
                    let after_generic = after_generic.trim_start();
                    let clean_type = if let Some(lt_pos) = after_generic.find('<') {
                        if let Some(rest_after) = after_generic.get(lt_pos..) {
                            if let Some(gt) = find_balanced_gt(rest_after) {
                                format!("{}{}", &after_generic[..lt_pos], &rest_after[gt + 1..])
                            } else {
                                after_generic.to_string()
                            }
                        } else {
                            after_generic.to_string()
                        }
                    } else {
                        after_generic.to_string()
                    };
                    // Also strip `where` clauses
                    let clean_type = if let Some(w) = clean_type.find(" where ") {
                        format!("{}:", &clean_type[..w])
                    } else {
                        clean_type
                    };
                    result.push_str(indent);
                    result.push_str("impl ");
                    result.push_str(&clean_type);
                    result.push('\n');
                } else {
                    result.push_str(line);
                    result.push('\n');
                }
            }
            if !s.ends_with('\n') && result.ends_with('\n') {
                result.pop();
            }
            s = result;
        }

        s
    } else {
        // Non-bootstrap: just normalize text? → text for basic compat
        source.replace("text?", "text")
    };

    // Parse
    let mut parser = simple_parser::Parser::new(&source);
    let ast = parser
        .parse()
        .map_err(|e| format!("{}: parse: {e}", file_path.display()))?;

    // Build per-module use_map from AST `use` statements.
    // Maps local imported name → mangled symbol name.
    let use_map = build_use_map_from_ast(&ast, &imports.all_mangled, &imports.re_exports);

    // Mono
    let ast = monomorphize_module(&ast);

    // HIR
    let hir_source_root = project_root.join("src");
    let resolver = ModuleResolver::new(project_root.to_path_buf(), hir_source_root);
    let mut lowerer = Lowerer::with_module_resolver(resolver, file_path.to_path_buf());
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer
        .lower_module(&ast)
        .map_err(|e| format!("{}: hir: {e}", file_path.display()))?;

    // MIR
    let mir = crate::mir::lower_to_mir(&hir).map_err(|e| format!("{}: mir: {e}", file_path.display()))?;

    // Codegen — select backend via SIMPLE_BACKEND env var
    let use_llvm = std::env::var("SIMPLE_BACKEND").as_deref() == Ok("llvm");

    if use_llvm {
        #[cfg(feature = "llvm")]
        {
            use crate::codegen::backend_trait::NativeBackend;
            use crate::codegen::llvm::LlvmBackend;

            let mut mir = mir;

            // Apply name mangling to MIR (matching Cranelift backend behavior).
            // Without this, same-named functions from different modules collide.
            if !no_mangle {
                let prefix = module_prefix_from_path(file_path, source_root);
                let global_suffix_index = build_suffix_index(imports.all_mangled.as_ref());
                let unresolved = mangle_mir(
                    &mut mir,
                    &prefix,
                    is_entry,
                    imports.import_map.as_ref(),
                    imports.ambiguous_names.as_ref(),
                    &use_map,
                    &global_suffix_index,
                );
                if unresolved > 0 && std::env::var("SIMPLE_BOOTSTRAP").as_deref() != Ok("1") {
                    return Err(format!(
                        "{}: {} unresolved call(s) in module `{}` — fix imports or add to runtime",
                        file_path.display(),
                        unresolved,
                        module_prefix_from_path(file_path, source_root)
                    ));
                }
            } else {
                // Even with no_mangle, entry module main → spl_main
                if is_entry {
                    for func in &mut mir.functions {
                        if func.name == "main" {
                            func.name = "spl_main".to_string();
                        }
                    }
                }
            }

            let mut llvm = LlvmBackend::new(simple_common::target::Target::host())
                .map_err(|e| format!("{}: llvm init: {e}", file_path.display()))?;
            llvm.set_import_map(imports.import_map.clone());
            llvm.set_use_map(use_map.clone());
            let obj = llvm
                .compile(&mir)
                .map_err(|e| format!("{}: llvm codegen: {e}", file_path.display()))?;

            // Dump LLVM IR for entry module if debug enabled
            if is_entry && std::env::var("SIMPLE_DEBUG_LLVM").is_ok() {
                if let Ok(ir) = llvm.get_ir() {
                    let ir_path = file_path.with_extension("ll");
                    let _ = std::fs::write(&ir_path, &ir);
                    eprintln!("[llvm] IR dumped to {}", ir_path.display());
                }
            }

            return Ok(obj);
        }
        #[cfg(not(feature = "llvm"))]
        return Err(format!(
            "{}: LLVM backend requested but 'llvm' feature not enabled",
            file_path.display()
        ));
    }

    // Cranelift backend (default)
    let mut codegen = Codegen::new().map_err(|e| format!("{}: codegen init: {e}", file_path.display()))?;
    codegen.set_entry_module(is_entry);
    codegen.set_import_map(imports.import_map.clone());
    codegen.set_ambiguous_names(imports.ambiguous_names.clone());
    codegen.set_use_map(use_map);
    if !no_mangle {
        let prefix = module_prefix_from_path(file_path, source_root);
        codegen.set_module_prefix(prefix);
    }
    let obj = codegen
        .compile_module(&mir)
        .map_err(|e| format!("{}: codegen: {e}", file_path.display()))?;

    Ok(obj)
}

/// Compile a file with panic catching and timeout.
#[allow(clippy::too_many_arguments)]
fn compile_file_safe(
    source: String,
    file_path: PathBuf,
    project_root: PathBuf,
    source_root: PathBuf,
    timeout_secs: u64,
    stack_size: usize,
    no_mangle: bool,
    is_entry: bool,
    imports: ModuleImports,
) -> Result<Vec<u8>, String> {
    use std::sync::mpsc;

    let (tx, rx) = mpsc::channel();
    let handle = std::thread::Builder::new()
        .name(format!(
            "compile-{}",
            file_path.file_name().unwrap_or_default().to_string_lossy()
        ))
        .stack_size(stack_size)
        .spawn(move || {
            let result = if std::env::var("SIMPLE_NO_CATCH").is_ok() {
                // Helpful for debugging: let panics crash to get full backtraces.
                compile_file_to_object(
                    &source,
                    &file_path,
                    &project_root,
                    &source_root,
                    no_mangle,
                    is_entry,
                    &imports,
                )
            } else {
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    compile_file_to_object(
                        &source,
                        &file_path,
                        &project_root,
                        &source_root,
                        no_mangle,
                        is_entry,
                        &imports,
                    )
                })) {
                    Ok(r) => r,
                    Err(e) => {
                        let msg = if let Some(s) = e.downcast_ref::<String>() {
                            format!("panic: {s}")
                        } else if let Some(s) = e.downcast_ref::<&str>() {
                            format!("panic: {s}")
                        } else {
                            "panic: unknown".to_string()
                        };
                        Err(msg)
                    }
                }
            };
            let _ = tx.send(());
            result
        })
        .map_err(|e| format!("spawn: {e}"))?;

    match rx.recv_timeout(Duration::from_secs(timeout_secs)) {
        Ok(()) => handle.join().unwrap_or_else(|_| Err("thread join error".to_string())),
        Err(_) => Err(format!("timeout ({}s)", timeout_secs)),
    }
}

/// Check if a file path matches the canonical entry file path.
fn is_entry_file(file_path: &Path, canonical_entry: &Option<PathBuf>) -> bool {
    match canonical_entry {
        Some(entry) => match std::fs::canonicalize(file_path) {
            Ok(p) => {
                let is_entry = p == *entry;
                if is_entry {
                    return true;
                }
                if std::env::var("SIMPLE_DEBUG_ENTRY").is_ok() {
                    eprintln!("[entry-debug] no match: {} vs {}", p.display(), entry.display());
                }
                false
            }
            Err(e) => {
                if std::env::var("SIMPLE_DEBUG_ENTRY").is_ok() {
                    eprintln!("[entry-debug] canonicalize failed for {}: {}", file_path.display(), e);
                }
                false
            }
        },
        None => false,
    }
}

fn same_file_path(a: &Path, b: &Path) -> bool {
    let canon_a = std::fs::canonicalize(a).unwrap_or_else(|_| a.to_path_buf());
    let canon_b = std::fs::canonicalize(b).unwrap_or_else(|_| b.to_path_buf());
    canon_a == canon_b
}

/// Compute a content hash for a source string (same algorithm as SourceInfo).
fn content_hash(content: &str) -> u64 {
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
fn object_cache_key(content: &str, is_entry: bool, backend: &str, no_mangle: bool) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    content.hash(&mut hasher);
    is_entry.hash(&mut hasher);
    backend.hash(&mut hasher);
    no_mangle.hash(&mut hasher);
    hasher.finish()
}

/// Import map build result.
struct ImportMapResult {
    /// raw name → mangled name (unique entries get direct mapping, ambiguous pick first)
    map: std::collections::HashMap<String, String>,
    /// Set of raw names with multiple definitions
    ambiguous: std::collections::HashSet<String>,
    /// raw name → all mangled names (for per-module `use` statement resolution)
    all_mangled: std::collections::HashMap<String, Vec<String>>,
    /// module_prefix → (func_name → actual_mangled_name) for re-exported functions.
    /// When a module imports a function via `use`, it becomes available at that module's path.
    re_exports: std::collections::HashMap<String, std::collections::HashMap<String, String>>,
}

/// Sanitize a mangled symbol name for the host platform.
///
/// On macOS, Mach-O does not support dots in symbol names — Apple ld crashes.
/// This replaces dots with `_dot_` to produce valid symbols, matching what
/// `CommonBackend::sanitize_symbol` does during codegen.
fn sanitize_mangled(name: String) -> String {
    if cfg!(target_os = "macos") && name.contains('.') {
        name.replace('.', "_dot_")
    } else {
        name
    }
}

/// Build an import map for cross-module function resolution.
///
/// Parses each source file to discover top-level function definitions,
/// computes their mangled names, and returns a map from raw name to mangled name
/// for functions that have exactly one definition across all modules.
fn build_import_map(file_sources: &[(PathBuf, String)], source_root: &Path) -> ImportMapResult {
    use std::collections::{HashMap, HashSet};

    // raw_name → list of mangled names (one per defining module)
    let mut raw_to_mangled: HashMap<String, Vec<String>> = HashMap::new();

    for (path, source) in file_sources {
        if path.to_string_lossy().contains("check.spl") {
            continue;
        }
        let prefix = module_prefix_from_path(path, source_root);
        // Try to parse the file; skip files that fail to parse
        let mut parser = simple_parser::Parser::new(source);
        if let Ok(ast) = parser.parse() {
            for item in &ast.items {
                match item {
                    simple_parser::ast::Node::Function(f) => {
                        // Only include functions with bodies (not extern declarations)
                        if !f.body.statements.is_empty() {
                            let mangled = format!("{}__{}", prefix, f.name);
                            raw_to_mangled.entry(f.name.clone()).or_default().push(mangled);
                        }
                    }
                    simple_parser::ast::Node::Class(c) => {
                        // Also index class methods (needed for cross-module static calls like Logger.from_env)
                        for m in &c.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", c.name, m.name);
                                // include both raw method name and fully qualified with class for convenience
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, c.name, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    simple_parser::ast::Node::Extern(e) => {
                        // extern fn foo(...) -> ... :
                        // - Runtime FFIs (rt_*) should keep their raw name (unmangled C symbol).
                        // - Other externs still get a module prefix.
                        let mangled = if e.name.starts_with("rt_") {
                            e.name.clone()
                        } else {
                            format!("{}__{}", prefix, e.name)
                        };
                        raw_to_mangled.entry(e.name.clone()).or_default().push(mangled);
                    }
                    simple_parser::ast::Node::ExternClass(ec) => {
                        for m in &ec.methods {
                            let raw = format!("{}.{}", ec.name, m.name);
                            let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, ec.name, m.name));
                            raw_to_mangled.entry(raw.clone()).or_default().push(mangled.clone());
                            raw_to_mangled.entry(m.name.clone()).or_default().push(mangled);
                        }
                    }
                    // Module-level variables (val/const/static) need to be in the
                    // import map so cross-module references resolve correctly.
                    simple_parser::ast::Node::Let(l) => {
                        if let Some(name) = extract_let_name(&l.pattern) {
                            let mangled = format!("{}__{}", prefix, name);
                            raw_to_mangled.entry(name).or_default().push(mangled);
                        }
                    }
                    simple_parser::ast::Node::Const(c) => {
                        let mangled = format!("{}__{}", prefix, c.name);
                        raw_to_mangled.entry(c.name.clone()).or_default().push(mangled);
                    }
                    simple_parser::ast::Node::Static(s) => {
                        let mangled = format!("{}__{}", prefix, s.name);
                        raw_to_mangled.entry(s.name.clone()).or_default().push(mangled);
                    }
                    // Struct methods (needed for cross-module calls like Span.empty)
                    simple_parser::ast::Node::Struct(s) => {
                        for m in &s.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", s.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, s.name, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    // Enum methods and variant constructors
                    simple_parser::ast::Node::Enum(e) => {
                        for m in &e.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", e.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, e.name, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                        // Enum variant constructors (e.g., Option.Some, Result.Ok)
                        for v in &e.variants {
                            let raw = format!("{}.{}", e.name, v.name);
                            let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, e.name, v.name));
                            raw_to_mangled.entry(raw).or_default().push(mangled);
                        }
                    }
                    // Trait default methods
                    simple_parser::ast::Node::Trait(t) => {
                        for m in &t.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", t.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, t.name, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    // Impl block methods (impl Type: or impl Trait for Type:)
                    simple_parser::ast::Node::Impl(imp) => {
                        let type_name = match &imp.target_type {
                            simple_parser::ast::Type::Simple(n) => Some(n.as_str()),
                            simple_parser::ast::Type::Generic { name, .. } => Some(name.as_str()),
                            _ => None,
                        };
                        if let Some(type_name) = type_name {
                            for m in &imp.methods {
                                if !m.body.statements.is_empty() {
                                    let raw = format!("{}.{}", type_name, m.name);
                                    let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, type_name, m.name));
                                    raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                    raw_to_mangled.entry(raw).or_default().push(mangled);
                                }
                            }
                        }
                    }
                    // Extend block methods (extend Type:)
                    simple_parser::ast::Node::Extend(ext) => {
                        for m in &ext.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", ext.target_type, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, ext.target_type, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    // Build the final map.
    // For unique definitions: direct mapping.
    // For ambiguous definitions (multiple modules define same name): pick the first
    // one so cross-module calls resolve to SOME definition rather than crashing.
    let mut map = HashMap::new();
    let mut ambiguous = HashSet::new();
    for (raw, mangled_list) in &raw_to_mangled {
        if mangled_list.len() == 1 {
            map.insert(raw.clone(), mangled_list[0].clone());
        } else {
            ambiguous.insert(raw.clone());
            // Pick the first mangled name as a fallback resolution
            map.insert(raw.clone(), mangled_list[0].clone());
        }
    }
    // Second pass: build re-export index.
    // For each module's `use` statements, resolve the imported functions and record
    // that they are re-exported at this module's path. This allows downstream consumers
    // (e.g., `use app.io.mod.{process_run}`) to find the actual definition even when
    // the re-exporting module doesn't define the function itself.
    let mut re_exports: HashMap<String, HashMap<String, String>> = HashMap::new();
    for (path, source) in file_sources {
        let prefix = module_prefix_from_path(path, source_root);
        let mut parser = simple_parser::Parser::new(source);
        if let Ok(ast) = parser.parse() {
            let mut use_items: Vec<(Vec<String>, &simple_parser::ast::ImportTarget)> = Vec::new();
            for item in &ast.items {
                match item {
                    simple_parser::ast::Node::UseStmt(u) => {
                        use_items.push((u.path.segments.clone(), &u.target));
                    }
                    simple_parser::ast::Node::MultiUse(mu) => {
                        for (path, target) in &mu.imports {
                            use_items.push((path.segments.clone(), target));
                        }
                    }
                    _ => {}
                }
            }
            for (segments, target) in use_items {
                let norm_segments: Vec<&str> = segments
                    .iter()
                    .map(|s| if s == "std" { "lib" } else { s.as_str() })
                    .collect();
                let names = collect_imported_names_flat(target);
                for name in names {
                    if let Some(candidates) = raw_to_mangled.get(&name) {
                        // Resolve this import using path matching
                        let resolved = if candidates.len() == 1 {
                            candidates[0].clone()
                        } else {
                            candidates
                                .iter()
                                .find(|c| mangled_matches_use_path(c, &norm_segments))
                                .cloned()
                                .unwrap_or_else(|| candidates[0].clone())
                        };
                        re_exports.entry(prefix.clone()).or_default().insert(name, resolved);
                    }
                }
            }
        }
    }

    // Hardcode critical logging symbols to avoid bootstrap misses
    let logger_debug = sanitize_mangled("compiler__common__config__Logger.debug".to_string());
    map.entry("Logger.debug".to_string())
        .or_insert_with(|| logger_debug.clone());
    map.entry("debug".to_string()).or_insert_with(|| logger_debug.clone());

    let logger_trace = sanitize_mangled("compiler__common__config__Logger.trace".to_string());
    map.entry("Logger.trace".to_string())
        .or_insert_with(|| logger_trace.clone());
    map.entry("trace".to_string()).or_insert_with(|| logger_trace.clone());

    // Bootstrap logger (defined in driver_types) to keep logging non-fatal
    let boot_debug = sanitize_mangled("compiler__driver__driver_types__BootLogger.debug".to_string());
    map.entry("BootLogger.debug".to_string())
        .or_insert_with(|| boot_debug.clone());

    let boot_trace = sanitize_mangled("compiler__driver__driver_types__BootLogger.trace".to_string());
    map.entry("BootLogger.trace".to_string())
        .or_insert_with(|| boot_trace.clone());

    // Critical compiler driver symbols used during self-host bootstrap.
    // Keep explicit aliases so method calls resolve even if parser indexing
    // misses the source file in a partial/compatibility parse.
    let driver_compile = sanitize_mangled("compiler__driver__driver__CompilerDriver.compile".to_string());
    map.entry("CompilerDriver.compile".to_string())
        .or_insert_with(|| driver_compile.clone());

    let compile_result_get_errors =
        sanitize_mangled("compiler__driver__driver_types__CompileResult.get_errors".to_string());
    map.entry("CompileResult.get_errors".to_string())
        .or_insert_with(|| compile_result_get_errors.clone());
    map.entry("get_errors".to_string())
        .or_insert_with(|| compile_result_get_errors.clone());

    ImportMapResult {
        map,
        ambiguous,
        all_mangled: raw_to_mangled,
        re_exports,
    }
}

/// Build a per-module use map from AST `use` statements.
///
/// For each `use path.to.module.{func1, func2}` statement, finds the correct
/// mangled symbol name for each imported function by matching the use path
/// segments against the available mangled names.
fn build_use_map_from_ast(
    ast: &simple_parser::ast::Module,
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
) -> std::collections::HashMap<String, String> {
    let mut use_map = std::collections::HashMap::new();

    for item in &ast.items {
        match item {
            simple_parser::ast::Node::UseStmt(use_stmt) => {
                collect_use_imports(
                    &use_stmt.path.segments,
                    &use_stmt.target,
                    all_mangled,
                    re_exports,
                    &mut use_map,
                );
            }
            simple_parser::ast::Node::ExportUseStmt(export_use) => {
                // export use also imports names into the current module's scope
                collect_use_imports(
                    &export_use.path.segments,
                    &export_use.target,
                    all_mangled,
                    re_exports,
                    &mut use_map,
                );
            }
            simple_parser::ast::Node::MultiUse(multi_use) => {
                for (path, target) in &multi_use.imports {
                    collect_use_imports(&path.segments, target, all_mangled, re_exports, &mut use_map);
                }
            }
            _ => {}
        }
    }

    use_map
}

/// Collect imported names from a single `use` statement and resolve to mangled names.
fn collect_use_imports(
    path_segments: &[String],
    target: &simple_parser::ast::ImportTarget,
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
    use_map: &mut std::collections::HashMap<String, String>,
) {
    // Normalize path: std → lib
    let segments: Vec<&str> = path_segments
        .iter()
        .map(|s| if s == "std" { "lib" } else { s.as_str() })
        .collect();

    match target {
        simple_parser::ast::ImportTarget::Single(name) => {
            if let Some(mangled) = resolve_import_name(name, &segments, all_mangled, re_exports) {
                use_map.insert(name.clone(), mangled);
            }
        }
        simple_parser::ast::ImportTarget::Aliased { name, alias } => {
            if let Some(mangled) = resolve_import_name(name, &segments, all_mangled, re_exports) {
                use_map.insert(alias.clone(), mangled);
            }
        }
        simple_parser::ast::ImportTarget::Group(items) => {
            for item in items {
                collect_use_imports(path_segments, item, all_mangled, re_exports, use_map);
            }
        }
        simple_parser::ast::ImportTarget::Glob => {
            // For glob imports, we can't resolve individual names at this point.
            // The global import map will handle unique names.
        }
    }
}

/// Find the mangled name for an imported function by matching use path segments
/// against all available mangled names for that function.
///
/// Resolution order:
/// 1. If only one definition exists, use it directly.
/// 2. Try matching use path segments against actual definition mangled names.
/// 3. Try re-export lookup: check if a module at the use path re-exports this function.
/// 4. Fallback: return the first candidate.
fn resolve_import_name(
    func_name: &str,
    use_segments: &[&str],
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
) -> Option<String> {
    let candidates = all_mangled.get(func_name)?;
    if candidates.len() == 1 {
        return Some(candidates[0].clone());
    }

    // Find the candidate whose mangled name contains the use path segments
    // as a subsequence.
    for candidate in candidates {
        if mangled_matches_use_path(candidate, use_segments) {
            return Some(candidate.clone());
        }
    }

    // Try re-export resolution: construct the expected module prefix from use segments
    // and check if that module re-exports this function.
    // Example: use path ["app", "io", "mod"] → prefix "app__io__mod"
    let expected_prefix = use_segments.join("__");
    if let Some(module_re_exports) = re_exports.get(&expected_prefix) {
        if let Some(actual_mangled) = module_re_exports.get(func_name) {
            return Some(actual_mangled.clone());
        }
    }

    // Fallback: return the first candidate
    Some(candidates[0].clone())
}

/// Collect all imported function names from an ImportTarget (flattened).
fn collect_imported_names_flat(target: &simple_parser::ast::ImportTarget) -> Vec<String> {
    let mut names = Vec::new();
    match target {
        simple_parser::ast::ImportTarget::Single(name) => names.push(name.clone()),
        simple_parser::ast::ImportTarget::Aliased { name, .. } => names.push(name.clone()),
        simple_parser::ast::ImportTarget::Group(items) => {
            for item in items {
                names.extend(collect_imported_names_flat(item));
            }
        }
        simple_parser::ast::ImportTarget::Glob => {}
    }
    names
}

/// Check if a mangled name matches a use path by checking if the use path
/// segments appear as a subsequence in the mangled name parts.
///
/// Example: mangled "src__app__io__cli_ops__cli_get_args" with use path
/// ["app", "io", "cli_ops"] → matches because "app", "io", "cli_ops" appear
/// in order as parts of the mangled name (split by "__").
fn mangled_matches_use_path(mangled: &str, use_segments: &[&str]) -> bool {
    let parts: Vec<&str> = mangled.split("__").collect();
    let mut seg_idx = 0;
    for part in &parts {
        if seg_idx < use_segments.len() && *part == use_segments[seg_idx] {
            seg_idx += 1;
        }
    }
    seg_idx == use_segments.len()
}

/// Extract variable name from a Let statement's pattern.
/// Handles simple identifiers and Pattern::Typed wrappers.
fn extract_let_name(pattern: &simple_parser::Pattern) -> Option<String> {
    match pattern {
        simple_parser::Pattern::Identifier(n) => Some(n.clone()),
        simple_parser::Pattern::MutIdentifier(n) => Some(n.clone()),
        simple_parser::Pattern::Typed { pattern: inner, .. } => extract_let_name(inner),
        _ => None,
    }
}

/// Recursively collect .spl files from a directory.
/// Skips broken symlinks and non-regular files.
fn collect_spl_files_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_spl_files_recursive(&path, out);
        } else if path.extension().is_some_and(|e| e == "spl") {
            // Skip known problematic files for bootstrap
            if let Some(p) = path.to_str() {
                if p.contains("check.spl") {
                    continue;
                }
            }
            // Skip broken symlinks: is_file() returns false for broken symlinks
            if path.is_file() {
                out.push(path);
            }
        }
    }
}

/// Find the combined native_all library (runtime + compiler with Cranelift FFI).
fn find_native_all_library() -> Option<PathBuf> {
    // Check env var override first
    if let Ok(path) = std::env::var("SIMPLE_NATIVE_ALL_PATH") {
        let p = PathBuf::from(&path);
        if p.exists() {
            return Some(p);
        }
    }

    let mut candidates: Vec<&str> = vec![
        "src/compiler_rust/target/bootstrap/libsimple_native_all.a",
        "src/compiler_rust/target/release/libsimple_native_all.a",
        "src/compiler_rust/target/debug/libsimple_native_all.a",
    ];

    // Windows MSVC produces .lib instead of lib*.a
    #[cfg(target_os = "windows")]
    {
        candidates.extend_from_slice(&[
            "src/compiler_rust/target/bootstrap/simple_native_all.lib",
            "src/compiler_rust/target/release/simple_native_all.lib",
            "src/compiler_rust/target/debug/simple_native_all.lib",
        ]);
    }

    for candidate in &candidates {
        let path = PathBuf::from(candidate);
        if path.exists() {
            return Some(path);
        }
    }

    // Try relative to current exe
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let path = dir.join("libsimple_native_all.a");
            if path.exists() {
                return Some(path);
            }
            #[cfg(target_os = "windows")]
            {
                let path = dir.join("simple_native_all.lib");
                if path.exists() {
                    return Some(path);
                }
            }
        }
    }

    None
}

/// Find the Simple runtime library.
fn find_runtime_library() -> Option<PathBuf> {
    // Check common locations
    let mut candidates: Vec<&str> = vec![
        // Bootstrap profile (smallest optimized build, used for seed compiler)
        "src/compiler_rust/target/bootstrap/libsimple_runtime.a",
        "src/compiler_rust/target/bootstrap/deps/libsimple_runtime.a",
        // Release layout (optimized)
        "src/compiler_rust/target/release/libsimple_runtime.a",
        "src/compiler_rust/target/release/deps/libsimple_runtime.a",
        // Debug layout (fallback, may be very large)
        "src/compiler_rust/target/debug/libsimple_runtime.a",
        "src/compiler_rust/target/debug/deps/libsimple_runtime.a",
    ];

    // Windows MSVC produces .lib instead of lib*.a
    #[cfg(target_os = "windows")]
    {
        candidates.extend_from_slice(&[
            "src/compiler_rust/target/bootstrap/simple_runtime.lib",
            "src/compiler_rust/target/bootstrap/deps/simple_runtime.lib",
            "src/compiler_rust/target/release/simple_runtime.lib",
            "src/compiler_rust/target/release/deps/simple_runtime.lib",
            "src/compiler_rust/target/debug/simple_runtime.lib",
            "src/compiler_rust/target/debug/deps/simple_runtime.lib",
        ]);
    }

    // System-installed (Unix only)
    #[cfg(not(target_os = "windows"))]
    candidates.push("/usr/local/lib/libsimple_runtime.a");

    for candidate in &candidates {
        let path = PathBuf::from(candidate);
        if path.exists() {
            return Some(path);
        }
    }

    // Try relative to current exe
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let path = dir.join("libsimple_runtime.a");
            if path.exists() {
                return Some(path);
            }
            #[cfg(target_os = "windows")]
            {
                let path = dir.join("simple_runtime.lib");
                if path.exists() {
                    return Some(path);
                }
            }
        }
    }

    None
}

/// Find a C compiler — delegates to `simple_common::platform::cc_detect`.
fn find_c_compiler() -> String {
    simple_common::platform::cc_detect::find_c_compiler()
}

/// Find an archive tool — delegates to `simple_common::platform::cc_detect`.
fn find_archive_tool() -> String {
    simple_common::platform::cc_detect::find_archive_tool()
}

fn find_cxx_compiler() -> String {
    simple_common::platform::cc_detect::find_cxx_compiler()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_prefix_from_path() {
        let source_root = PathBuf::from("/project/src");

        assert_eq!(
            module_prefix_from_path(
                &PathBuf::from("/project/src/compiler/10.frontend/core/lexer.spl"),
                &source_root
            ),
            "compiler__frontend__core__lexer"
        );

        assert_eq!(
            module_prefix_from_path(&PathBuf::from("/project/src/app/cli/main.spl"), &source_root),
            "app__cli__main"
        );

        assert_eq!(
            module_prefix_from_path(&PathBuf::from("/project/src/lib/common/text.spl"), &source_root),
            "lib__common__text"
        );
    }

    #[test]
    fn test_collect_spl_files() {
        let temp = tempfile::tempdir().unwrap();
        let dir = temp.path();
        std::fs::write(dir.join("a.spl"), "# test").unwrap();
        std::fs::write(dir.join("b.txt"), "not spl").unwrap();
        std::fs::create_dir(dir.join("sub")).unwrap();
        std::fs::write(dir.join("sub/c.spl"), "# test").unwrap();

        let mut files = Vec::new();
        collect_spl_files_recursive(dir, &mut files);
        assert_eq!(files.len(), 2);
    }

    #[test]
    fn test_content_hash_consistency() {
        let h1 = content_hash("fn main(): return 42");
        let h2 = content_hash("fn main(): return 42");
        assert_eq!(h1, h2);

        let h3 = content_hash("fn main(): return 0");
        assert_ne!(h1, h3);
    }

    #[test]
    fn test_content_hash_matches_source_info() {
        // Ensure our content_hash matches SourceInfo::update_from_content
        let content = "fn main(): return 42";
        let hash = content_hash(content);

        let mut info = SourceInfo::new(PathBuf::from("test.spl"));
        info.update_from_content(content);

        assert_eq!(hash, info.content_hash);
    }

    #[test]
    fn test_incremental_cache_dir_default() {
        let builder = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple"));
        assert_eq!(builder.cache_dir(), PathBuf::from("/project/.simple/native_cache"));
    }

    #[test]
    fn test_source_dir_preserves_logical_path() {
        let builder = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple"))
            .source_dir(PathBuf::from("src/app/mcp_t32"));
        assert_eq!(builder.source_dirs, vec![PathBuf::from("/project/src/app/mcp_t32")]);
    }

    #[test]
    fn test_incremental_cache_dir_custom() {
        let mut config = NativeBuildConfig::default();
        config.cache_dir = Some(PathBuf::from("/tmp/my_cache"));

        let builder =
            NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple")).config(config);

        assert_eq!(builder.cache_dir(), PathBuf::from("/tmp/my_cache"));
    }

    #[test]
    fn test_default_config_mangle() {
        let config = NativeBuildConfig::default();
        assert!(
            !config.no_mangle,
            "no_mangle should default to false (mangling enabled)"
        );
        assert!(config.incremental, "incremental should default to true");
        assert!(!config.clean, "clean should default to false");
    }

    #[test]
    fn test_discover_files_includes_explicit_entry_outside_source_dirs() {
        let temp = tempfile::tempdir().unwrap();
        let project_root = temp.path().join("project");
        let src_dir = project_root.join("src");
        let tools_dir = project_root.join("examples/tool");
        std::fs::create_dir_all(&src_dir).unwrap();
        std::fs::create_dir_all(&tools_dir).unwrap();

        let lib_file = src_dir.join("lib.spl");
        let entry_file = tools_dir.join("main.spl");
        std::fs::write(&lib_file, "fn helper(): pass").unwrap();
        std::fs::write(&entry_file, "fn main(): pass").unwrap();

        let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
            .source_dir(src_dir)
            .entry_file(entry_file.clone());

        let files = builder.discover_files();
        assert!(files.iter().any(|path| same_file_path(path, &lib_file)));
        assert!(files.iter().any(|path| same_file_path(path, &entry_file)));
        assert_eq!(files.len(), 2);
    }
}
