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
    /// Canonicalizes the path so it's absolute and consistent with source_root.
    pub fn source_dir(mut self, dir: PathBuf) -> Self {
        let canonical = std::fs::canonicalize(&dir).unwrap_or(dir);
        self.source_dirs.push(canonical);
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
            std::fs::create_dir_all(&objects_dir)
                .map_err(|e| format!("create cache dir: {e}"))?;
        }

        // 3. Create temp directory for .o files
        let mut temp_dir = Some(tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?);
        let temp_dir_path = temp_dir.as_ref().unwrap().path().to_path_buf();

        // 4. Read all source files and determine dirty set
        let compile_start = Instant::now();
        let mut file_sources: Vec<(PathBuf, String)> = Vec::new();
        for path in &files {
            let source = std::fs::read_to_string(path)
                .map_err(|e| (path.clone(), format!("read: {e}")))
                .map_err(|(p, m)| format!("{}: {}", p.display(), m))?;
            file_sources.push((path.clone(), source));
        }

        // Determine which files need recompilation via content hash
        let mut to_compile: Vec<(usize, PathBuf, String)> = Vec::new();
        let mut cached_objects: Vec<(usize, PathBuf)> = Vec::new();

        if use_incremental {
            for (i, (path, source)) in file_sources.iter().enumerate() {
                let hash = content_hash(source);
                let cached_o = objects_dir.join(format!("{:016x}.o", hash));
                if cached_o.exists() {
                    // Cache hit: copy to temp dir
                    let obj_path = temp_dir_path.join(format!("mod_{}.o", i));
                    if std::fs::copy(&cached_o, &obj_path).is_ok() {
                        cached_objects.push((i, obj_path));
                        continue;
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
            eprintln!(
                "Incremental: {} cached, {} to compile",
                cached_count,
                to_compile.len()
            );
        }

        // Canonicalize the entry file path for comparison during compilation
        let canonical_entry: Option<PathBuf> = self.entry_file.as_ref().and_then(|p| {
            std::fs::canonicalize(p).ok()
        });
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
        let (import_map, ambiguous_names, all_mangled, re_exports) = if !self.config.no_mangle {
            let result = build_import_map(&file_sources, &self.source_root);
            if self.config.verbose {
                eprintln!("Import map: {} unique, {} ambiguous function entries, {} modules with re-exports",
                    result.map.len(), result.ambiguous.len(), result.re_exports.len());
            }
            (std::sync::Arc::new(result.map), std::sync::Arc::new(result.ambiguous),
             std::sync::Arc::new(result.all_mangled), std::sync::Arc::new(result.re_exports))
        } else {
            (std::sync::Arc::new(std::collections::HashMap::new()),
             std::sync::Arc::new(std::collections::HashSet::new()),
             std::sync::Arc::new(std::collections::HashMap::new()),
             std::sync::Arc::new(std::collections::HashMap::new()))
        };

        // 5. Compile dirty files
        let results = if self.config.parallel {
            self.compile_entries_parallel(&to_compile, &temp_dir_path, &canonical_entry, &import_map, &ambiguous_names, &all_mangled, &re_exports)
        } else {
            self.compile_entries_sequential(&to_compile, &temp_dir_path, &canonical_entry, &import_map, &ambiguous_names, &all_mangled, &re_exports)
        };
        let compile_time = compile_start.elapsed();

        // Collect results
        let mut object_paths: Vec<PathBuf> = cached_objects
            .into_iter()
            .map(|(_, p)| p)
            .collect();
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
            eprintln!("");  // spacer
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
            return Err(format!(
                "All {} files failed to compile",
                files.len()
            ));
        }

        // 6. Cache freshly compiled objects
        if use_incremental {
            for (idx, obj_path) in &freshly_compiled {
                if let Some((_, source)) = file_sources.get(*idx) {
                    let hash = content_hash(source);
                    let cached_o = objects_dir.join(format!("{:016x}.o", hash));
                    let _ = std::fs::copy(obj_path, cached_o);
                }
            }
        }

        // 7. Link
        let link_start = Instant::now();
        self.link_objects(&object_paths)?;
        let link_time = link_start.elapsed();

        // Optionally keep the temporary object directory for debugging.
        if std::env::var("SIMPLE_KEEP_NATIVE_OBJS").is_ok() {
            if let Some(dir) = temp_dir.take() {
                let path = dir.into_path();
                eprintln!("Keeping native object files in {}", path.display());
            }
        }

        let binary_size = std::fs::metadata(&self.output)
            .map(|m| m.len())
            .unwrap_or(0);

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
        files.sort();
        files
    }

    /// Compile entries (index, path, source) in parallel using rayon.
    fn compile_entries_parallel(
        &self,
        entries: &[(usize, PathBuf, String)],
        temp_dir: &Path,
        canonical_entry: &Option<PathBuf>,
        import_map: &std::sync::Arc<std::collections::HashMap<String, String>>,
        ambiguous_names: &std::sync::Arc<std::collections::HashSet<String>>,
        all_mangled: &std::sync::Arc<std::collections::HashMap<String, Vec<String>>>,
        re_exports: &std::sync::Arc<std::collections::HashMap<String, std::collections::HashMap<String, String>>>,
    ) -> Vec<Result<(usize, PathBuf), (PathBuf, String)>> {
        // Configure rayon thread pool if needed
        if let Some(n) = self.config.num_threads {
            let _ = rayon::ThreadPoolBuilder::new()
                .num_threads(n)
                .build_global();
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
        let import_map = import_map.clone();
        let ambiguous_names = ambiguous_names.clone();
        let all_mangled = all_mangled.clone();
        let re_exports = re_exports.clone();

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
                    import_map.clone(),
                    ambiguous_names.clone(),
                    all_mangled.clone(),
                    re_exports.clone(),
                ) {
                    Ok(obj_code) => {
                        let obj_path = temp_dir.join(format!("mod_{}.o", idx));
                        std::fs::write(&obj_path, &obj_code)
                            .map_err(|e| (path.clone(), format!("write .o: {e}")))?;
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
        import_map: &std::sync::Arc<std::collections::HashMap<String, String>>,
        ambiguous_names: &std::sync::Arc<std::collections::HashSet<String>>,
        all_mangled: &std::sync::Arc<std::collections::HashMap<String, Vec<String>>>,
        re_exports: &std::sync::Arc<std::collections::HashMap<String, std::collections::HashMap<String, String>>>,
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
                    import_map.clone(),
                    ambiguous_names.clone(),
                    all_mangled.clone(),
                    re_exports.clone(),
                ) {
                    Ok(obj_code) => {
                        let obj_path = temp_dir.join(format!("mod_{}.o", idx));
                        std::fs::write(&obj_path, &obj_code)
                            .map_err(|e| (path.clone(), format!("write .o: {e}")))?;
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

    /// Compile the C main stub to an object file.
    fn compile_main_stub(&self, temp_dir: &Path) -> Result<PathBuf, String> {
        let main_c = temp_dir.join("_main_stub.c");
        std::fs::write(
            &main_c,
            r#"
extern int __attribute__((weak)) spl_main(void);
extern void __attribute__((weak)) rt_set_args(int argc, char** argv);
extern void __attribute__((weak)) __simple_runtime_init(void);
extern void __attribute__((weak)) __simple_runtime_shutdown(void);
int main(int argc, char** argv) {
    if (__simple_runtime_init) __simple_runtime_init();
    if (rt_set_args) rt_set_args(argc, argv);
    int r = spl_main ? spl_main() : 0;
    if (__simple_runtime_shutdown) __simple_runtime_shutdown();
    return r;
}
"#,
        )
        .map_err(|e| format!("write main stub: {e}"))?;

        let main_o = temp_dir.join("_main_stub.o");
        let cc = find_c_compiler();
        let status = std::process::Command::new(&cc)
            .args(["-c", "-o"])
            .arg(&main_o)
            .arg(&main_c)
            .status()
            .map_err(|e| format!("compile main stub: {e}"))?;
        if !status.success() {
            return Err("Failed to compile main stub".to_string());
        }
        Ok(main_o)
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
        let temp_dir = object_paths[0]
            .parent()
            .ok_or("no parent for object path")?;

        // Compile the C main stub (defines main() which calls spl_main())
        let main_o = self.compile_main_stub(temp_dir)?;

        // Use clang as the linker driver — it handles CRT files (crt1.o, crti.o, crtn.o),
        // libc initialization, and library paths automatically.
        let mut cmd = std::process::Command::new("clang");
        cmd.arg("-fPIC")
            .arg("-no-pie")
            .arg("-o").arg(&self.output)
            .arg(&main_o);

        // Add all SPL object files
        for obj in object_paths {
            cmd.arg(obj);
        }

        // Add runtime library if found
        if let Some(runtime) = find_runtime_library() {
            cmd.arg(&runtime);
        }

        // Libraries
        for lib in &["pthread", "dl", "m", "unwind"] {
            cmd.arg(format!("-l{}", lib));
        }

        // Allow undefined symbols at link time. Many .spl files declare extern fn rt_*
        // functions that aren't in the runtime library (CUDA, GC, debugger hooks, etc.).
        cmd.arg("-Wl,--unresolved-symbols=ignore-all");

        if self.config.strip {
            cmd.arg("-Wl,-s");
        }

        if self.config.verbose {
            eprintln!("Link command: {:?}", cmd);
        }

        let output_result = cmd.output()
            .map_err(|e| format!("link (clang): {e}"))?;

        if output_result.status.success() {
            // Report binary size
            if let Ok(meta) = std::fs::metadata(&self.output) {
                eprintln!("Linked: {} ({} KB) in clang",
                    self.output.display(), meta.len() / 1024);
            }
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output_result.stderr);
            Err(format!("link failed: {}", stderr))
        }
    }
}

/// Compile a single .spl file to object code.
fn compile_file_to_object(
    source: &str,
    file_path: &Path,
    project_root: &Path,
    source_root: &Path,
    no_mangle: bool,
    is_entry: bool,
    import_map: &std::sync::Arc<std::collections::HashMap<String, String>>,
    ambiguous_names: &std::sync::Arc<std::collections::HashSet<String>>,
    all_mangled: &std::sync::Arc<std::collections::HashMap<String, Vec<String>>>,
    re_exports: &std::sync::Arc<std::collections::HashMap<String, std::collections::HashMap<String, String>>>,
) -> Result<Vec<u8>, String> {
    // Bootstrap hack: normalize optional text types that older lenient type resolver misses
    let mut source = source.replace("text?", "text");
    if std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1") {
        source = source.replace(".?:", " != nil:");
        source = source.replace(".?\n", " != nil\n");
        source = source.replace(".?\r\n", " != nil\r\n");
        for pat in [
            "? ",
            "?\n",
            "?\r\n",
            "?\t",
            "?,",
            "?)",
            "?]",
            "?>",
            "?:",
            "?=",
            "?;",
            "?>",
        ] {
            while source.contains(pat) {
                source = source.replace(pat, &pat[1..]);
            }
        }
        if source.ends_with('?') {
            source.pop();
        }
    }

    // Parse
    let mut parser = simple_parser::Parser::new(&source);
    let ast = parser.parse().map_err(|e| format!("{}: parse: {e}", file_path.display()))?;

    // Build per-module use_map from AST `use` statements.
    // Maps local imported name → mangled symbol name.
    let use_map = build_use_map_from_ast(&ast, all_mangled, re_exports);

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

    // Codegen
    let mut codegen = Codegen::new().map_err(|e| format!("{}: codegen init: {e}", file_path.display()))?;
    codegen.set_entry_module(is_entry);
    codegen.set_import_map(import_map.clone());
    codegen.set_ambiguous_names(ambiguous_names.clone());
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
fn compile_file_safe(
    source: String,
    file_path: PathBuf,
    project_root: PathBuf,
    source_root: PathBuf,
    timeout_secs: u64,
    stack_size: usize,
    no_mangle: bool,
    is_entry: bool,
    import_map: std::sync::Arc<std::collections::HashMap<String, String>>,
    ambiguous_names: std::sync::Arc<std::collections::HashSet<String>>,
    all_mangled: std::sync::Arc<std::collections::HashMap<String, Vec<String>>>,
    re_exports: std::sync::Arc<std::collections::HashMap<String, std::collections::HashMap<String, String>>>,
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
                    &import_map,
                    &ambiguous_names,
                    &all_mangled,
                    &re_exports,
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
                        &import_map,
                        &ambiguous_names,
                        &all_mangled,
                        &re_exports,
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
        Some(entry) => {
            match std::fs::canonicalize(file_path) {
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
            }
        }
        None => false,
    }
}

/// Compute a content hash for a source string (same algorithm as SourceInfo).
fn content_hash(content: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    content.hash(&mut hasher);
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

/// Build an import map for cross-module function resolution.
///
/// Parses each source file to discover top-level function definitions,
/// computes their mangled names, and returns a map from raw name to mangled name
/// for functions that have exactly one definition across all modules.
fn build_import_map(
    file_sources: &[(PathBuf, String)],
    source_root: &Path,
) -> ImportMapResult {
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
                            raw_to_mangled
                                .entry(f.name.clone())
                                .or_default()
                                .push(mangled);
                        }
                    }
                    simple_parser::ast::Node::Class(c) => {
                        // Also index class methods (needed for cross-module static calls like Logger.from_env)
                        for m in &c.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", c.name, m.name);
                                // include both raw method name and fully qualified with class for convenience
                                raw_to_mangled
                                    .entry(m.name.clone())
                                    .or_default()
                                    .push(format!("{}__{}.{}", prefix, c.name, m.name));
                                let mangled = format!("{}__{}.{}", prefix, c.name, m.name);
                                raw_to_mangled
                                    .entry(raw)
                                    .or_default()
                                    .push(mangled);
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
                        raw_to_mangled
                            .entry(e.name.clone())
                            .or_default()
                            .push(mangled);
                    }
                    simple_parser::ast::Node::ExternClass(ec) => {
                        for m in &ec.methods {
                            let raw = format!("{}.{}", ec.name, m.name);
                            raw_to_mangled
                                .entry(raw.clone())
                                .or_default()
                                .push(format!("{}__{}.{}", prefix, ec.name, m.name));
                            raw_to_mangled
                                .entry(m.name.clone())
                                .or_default()
                                .push(format!("{}__{}.{}", prefix, ec.name, m.name));
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
                let norm_segments: Vec<&str> = segments.iter().map(|s| {
                    if s == "std" { "lib" } else { s.as_str() }
                }).collect();
                let names = collect_imported_names_flat(target);
                for name in names {
                    if let Some(candidates) = raw_to_mangled.get(&name) {
                        // Resolve this import using path matching
                        let resolved = if candidates.len() == 1 {
                            candidates[0].clone()
                        } else {
                            candidates.iter()
                                .find(|c| mangled_matches_use_path(c, &norm_segments))
                                .cloned()
                                .unwrap_or_else(|| candidates[0].clone())
                        };
                        re_exports.entry(prefix.clone())
                            .or_default()
                            .insert(name, resolved);
                    }
                }
            }
        }
    }

    // Hardcode critical logging symbols to avoid bootstrap misses
    let logger_debug = "compiler__common__config__Logger.debug".to_string();
    map.entry("Logger.debug".to_string()).or_insert_with(|| logger_debug.clone());
    map.entry("debug".to_string()).or_insert_with(|| logger_debug.clone());

    let logger_trace = "compiler__common__config__Logger.trace".to_string();
    map.entry("Logger.trace".to_string()).or_insert_with(|| logger_trace.clone());
    map.entry("trace".to_string()).or_insert_with(|| logger_trace.clone());

    // Bootstrap logger (defined in driver_types) to keep logging non-fatal
    let boot_debug = "compiler__driver__driver_types__BootLogger.debug".to_string();
    map.entry("BootLogger.debug".to_string()).or_insert_with(|| boot_debug.clone());

    let boot_trace = "compiler__driver__driver_types__BootLogger.trace".to_string();
    map.entry("BootLogger.trace".to_string()).or_insert_with(|| boot_trace.clone());

    ImportMapResult { map, ambiguous, all_mangled: raw_to_mangled, re_exports }
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
                collect_use_imports(&use_stmt.path.segments, &use_stmt.target, all_mangled, re_exports, &mut use_map);
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
    let segments: Vec<&str> = path_segments.iter().map(|s| {
        if s == "std" { "lib" } else { s.as_str() }
    }).collect();

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

/// Recursively collect .spl files from a directory.
/// Skips broken symlinks and non-regular files.
fn collect_spl_files_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_spl_files_recursive(&path, out);
        } else if path.extension().map_or(false, |e| e == "spl") {
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

/// Find the Simple runtime library.
fn find_runtime_library() -> Option<PathBuf> {
    // Check common locations
    let candidates = [
        // Development layout
        "src/compiler_rust/target/debug/libsimple_runtime.a",
        "src/compiler_rust/target/debug/deps/libsimple_runtime.a",
        "src/compiler_rust/target/release/libsimple_runtime.a",
        "src/compiler_rust/target/release/deps/libsimple_runtime.a",
        // Bootstrap profile (used for seed compiler)
        "src/compiler_rust/target/bootstrap/libsimple_runtime.a",
        "src/compiler_rust/target/bootstrap/deps/libsimple_runtime.a",
        // System-installed
        "/usr/local/lib/libsimple_runtime.a",
    ];

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
        }
    }

    None
}

/// Find a C compiler.
fn find_c_compiler() -> String {
    if let Ok(cc) = std::env::var("CC") {
        return cc;
    }
    if std::process::Command::new("clang")
        .arg("--version")
        .output()
        .is_ok()
    {
        return "clang".to_string();
    }
    "gcc".to_string()
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
            module_prefix_from_path(
                &PathBuf::from("/project/src/app/cli/main.spl"),
                &source_root
            ),
            "app__cli__main"
        );

        assert_eq!(
            module_prefix_from_path(
                &PathBuf::from("/project/src/lib/common/text.spl"),
                &source_root
            ),
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
        let builder = NativeProjectBuilder::new(
            PathBuf::from("/project"),
            PathBuf::from("/project/bin/simple"),
        );
        assert_eq!(
            builder.cache_dir(),
            PathBuf::from("/project/.simple/native_cache")
        );
    }

    #[test]
    fn test_incremental_cache_dir_custom() {
        let mut config = NativeBuildConfig::default();
        config.cache_dir = Some(PathBuf::from("/tmp/my_cache"));

        let builder = NativeProjectBuilder::new(
            PathBuf::from("/project"),
            PathBuf::from("/project/bin/simple"),
        )
        .config(config);

        assert_eq!(builder.cache_dir(), PathBuf::from("/tmp/my_cache"));
    }

    #[test]
    fn test_default_config_mangle() {
        let config = NativeBuildConfig::default();
        assert!(!config.no_mangle, "no_mangle should default to false (mangling enabled)");
        assert!(config.incremental, "incremental should default to true");
        assert!(!config.clean, "clean should default to false");
    }
}
