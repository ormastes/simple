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
#[cfg(test)]
mod entry_closure_global_init_tests;

pub use config::*;
pub use compiler::*;
pub use linker::*;
pub use imports::*;
pub use tools::*;

use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use object::{Architecture, BinaryFormat, Object, ObjectKind};
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

fn native_object_staging_dir(cache_base_dir: &Path, cache_dir: &Path) -> Result<tempfile::TempDir, String> {
    let staging_parent = cache_base_dir
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    std::fs::create_dir_all(staging_parent)
        .map_err(|e| format!("create native object staging parent {}: {e}", staging_parent.display()))?;
    std::fs::create_dir_all(cache_dir)
        .map_err(|e| format!("create native object cache {}: {e}", cache_dir.display()))?;
    tempfile::Builder::new()
        .prefix("native-objects-")
        .tempdir_in(staging_parent)
        .map_err(|e| format!("create native object staging in {}: {e}", staging_parent.display()))
}

/// Read a cache entry only when it is a parseable relocatable object.
///
/// The key identifies build inputs; it does not make arbitrary payload bytes
/// trustworthy. Require the expected relocatable format and architecture.
/// Invalid entries are left in place: another builder may have atomically
/// published a valid object after our read, so unlinking here would race it.
fn expected_cached_object_identity() -> (Architecture, BinaryFormat) {
    use simple_common::target::{TargetArch, TargetOS};
    let target = effective_target();
    let architecture = match target.arch {
        TargetArch::X86_64 => Architecture::X86_64,
        TargetArch::Aarch64 => Architecture::Aarch64,
        TargetArch::X86 => Architecture::I386,
        TargetArch::Arm => Architecture::Arm,
        TargetArch::Riscv64 => Architecture::Riscv64,
        TargetArch::Riscv32 => Architecture::Riscv32,
        TargetArch::Wasm32 => Architecture::Wasm32,
        TargetArch::Wasm64 => Architecture::Wasm64,
    };
    let format = match target.os {
        TargetOS::Windows => BinaryFormat::Coff,
        TargetOS::MacOS => BinaryFormat::MachO,
        TargetOS::Any if matches!(target.arch, TargetArch::Wasm32 | TargetArch::Wasm64) => BinaryFormat::Wasm,
        TargetOS::Any | TargetOS::Linux | TargetOS::FreeBSD | TargetOS::SimpleOS | TargetOS::None => BinaryFormat::Elf,
    };
    (architecture, format)
}

fn read_usable_cached_object(path: &Path) -> Option<Vec<u8>> {
    let Ok(bytes) = std::fs::read(path) else {
        return None;
    };
    let (expected_arch, expected_format) = expected_cached_object_identity();
    let usable = object::File::parse(bytes.as_slice())
        .map(|object| {
            object.kind() == ObjectKind::Relocatable
                && object.architecture() == expected_arch
                && object.format() == expected_format
        })
        .unwrap_or(false);
    usable.then_some(bytes)
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
/// 1. `--low-memory` forces a single worker, full stop (highest priority: an
///    explicit memory-safety request must never be silently overridden).
/// 2. Explicit `num_threads` from `NativeBuildConfig` (`--threads`)
/// 3. `SIMPLE_BOOTSTRAP_THREADS` environment variable
/// 4. Backend-aware default: `available_parallelism()` (all cores) for
///    Cranelift, but clamped for LLVM (see `LLVM_DEFAULT_MAX_THREADS` below).
///
/// # Why LLVM gets a lower default
/// Each rayon worker that compiles with `--backend llvm` builds its own
/// independent `inkwell::Context` + `LlvmBackend` (see
/// `compile_file_to_object` in `codegen`-adjacent `compiler.rs`), which spins
/// up a full LLVM optimization pipeline per translation unit. LLVM's
/// per-translation-unit peak memory is routinely GB-scale for large/complex
/// modules, vs. Cranelift's much leaner tens-of-MB footprint for the same
/// input. Before this clamp, `num_threads` defaulted to
/// `available_parallelism()` (all host cores) for BOTH backends equally, so
/// on a 32-core box, 32 concurrent LLVM workers each peaking around 1.5-2 GB
/// multiplied straight into the 50-64 GB earlyoom kills observed on
/// `--backend llvm --mode one-binary` builds -- while the identical source
/// tree under `--backend cranelift --mode dynload` peaked around 1 GB,
/// because Cranelift's per-worker footprint stayed small even at full
/// parallelism. This is not a leak; it is unbounded worker-count x
/// per-worker-peak with no backend-aware ceiling.
const LLVM_DEFAULT_MAX_THREADS: usize = 4;

/// Pure thread-count resolution, factored out of `init_rayon_pool` so the
/// backend-aware clamp can be unit tested without touching the process-global
/// rayon pool (which can only be initialized once per test process).
///
/// `bootstrap_threads_env` is passed in (rather than read from the process
/// environment directly) so tests can exercise the `SIMPLE_BOOTSTRAP_THREADS`
/// branch deterministically.
pub(crate) fn resolve_num_threads(
    config: &NativeBuildConfig,
    available_cores: usize,
    bootstrap_threads_env: Option<usize>,
) -> usize {
    if config.low_memory {
        return 1;
    }
    if let Some(n) = config.num_threads {
        return n;
    }
    if let Some(n) = bootstrap_threads_env.filter(|&n| n > 0) {
        return n;
    }
    if config.backend == "llvm" {
        available_cores.min(LLVM_DEFAULT_MAX_THREADS)
    } else {
        available_cores
    }
}

fn init_rayon_pool(config: &NativeBuildConfig) {
    use std::sync::Once;
    static POOL_INIT: Once = Once::new();

    let available_cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let bootstrap_threads_env = std::env::var("SIMPLE_BOOTSTRAP_THREADS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok());
    let num_threads = resolve_num_threads(config, available_cores, bootstrap_threads_env);

    if config.verbose || std::env::var("SIMPLE_NATIVE_BUILD_TRACE").is_ok() {
        eprintln!(
            "[native-build] parallelism: {num_threads} worker(s) (backend={}, low_memory={})",
            config.backend, config.low_memory
        );
    }

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
/// Enum definitions: enum name → list of (variant name, optional payload types).
type EnumDefs = std::sync::Arc<std::collections::HashMap<String, Vec<(String, Option<Vec<simple_parser::Type>>)>>>;

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
    /// Collision-free `module_prefix__Type` owners that carry a vtable header.
    pub vtable_type_owners: std::sync::Arc<std::collections::HashSet<String>>,
    /// Qualified owner → externally linkable primary vtable symbol.
    pub vtable_symbols: std::sync::Arc<std::collections::HashMap<String, String>>,
    /// Canonical `module_prefix__Type` -> declared field layout.  This is the
    /// authoritative cross-module nominal-layout registry.
    pub struct_defs: std::sync::Arc<std::collections::HashMap<String, Vec<(String, simple_parser::Type)>>>,
    /// Bare type name -> canonical owner, only for names unique in this
    /// compilation closure.  Colliding bare names have no entry.
    pub unique_struct_owners: std::sync::Arc<std::collections::HashMap<String, String>>,
    /// Resolved declaration path -> canonical module-prefix owner.
    pub struct_module_owners: std::sync::Arc<std::collections::HashMap<std::path::PathBuf, String>>,
    /// Duplicate global struct/class definitions grouped by bare type name.
    /// Used only for bounded field-name disambiguation when `struct_defs`
    /// lost information due to same-name collisions across modules.
    pub duplicate_struct_defs: DuplicateStructDefs,
    /// Global enum definitions with payload field types.
    /// Shared across all compilation units. The HIR lowerer consumes this in
    /// `compile_file_to_object` to eagerly seed `module.types.name_to_id` and
    /// `globals` with real enum TypeIds for cross-module enum receivers
    /// (W15-H follow-up to W13-F: 29 stage4 sites where
    /// `expr/access.rs::lower_field_access` was emitting `Global(EnumName)`
    /// with `ty=ANY` because the enum reached the file via re-export but
    /// not via a direct `use` chain that triggered `preregister_imported_type_names`).
    pub enum_defs: EnumDefs,
    /// Mangled enum owner to stable dotted runtime identity.
    pub enum_runtime_names: std::sync::Arc<std::collections::HashMap<String, String>>,
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
    /// Codegen backend: "cranelift" (default) or "llvm".
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
    /// Opt-in safe incremental object reuse (SIMPLE_NATIVE_INCREMENTAL=1).
    ///
    /// When set, every per-module object cache key additionally folds in a
    /// `global_build_fingerprint` (opt-level, entry-closure flag, target triple,
    /// linker-script content, and an order-independent hash of ALL cross-module
    /// codegen inputs — struct/enum layouts, trait impls, import map, exported
    /// signatures). This closes the stale-hit hazard where entry-closure /
    /// global-def population makes one module's object bytes depend on another
    /// module's type layout: a struct change in module A then invalidates the
    /// whole per-module cache instead of silently reusing a stale object for
    /// module B. Default false preserves the legacy content-only key.
    pub incremental_hardening: bool,
    /// M4 (LLVM mem-infra lane): enable AddressSanitizer instrumentation.
    /// `--sanitize` / `--mem-infra=asan` on the CLI. Only takes effect on
    /// `backend == "llvm"` (the capability matrix's own scoping —
    /// `src/lib/common/mem_infra/config.spl`); exported as `SIMPLE_MEM_ASAN=1`
    /// for the LLVM backend (`codegen/llvm/backend_core.rs::llvm_asan_enabled`)
    /// and threaded to the linker (`linker.rs::link_objects`) to link
    /// `libclang_rt.asan`. See
    /// `doc/05_design/compiler/backend/m4_llvm_mem_infra_design.md`.
    pub sanitize: bool,
    /// M4 (LLVM mem-infra lane): enable MemProfiler heap-allocation-profiling
    /// instrumentation. `--memprof` / `--mem-infra=memprof` on the CLI. Only
    /// takes effect on `backend == "llvm"` (the capability matrix's own
    /// scoping — `src/lib/common/mem_infra/config.spl`); exported as
    /// `SIMPLE_MEM_MEMPROF=1` for the LLVM backend
    /// (`codegen/llvm/backend_core.rs::llvm_memprof_enabled`) and threaded to
    /// the linker (`linker.rs::link_objects`) to link the memprof runtime via
    /// `-fmemory-profile`. Unlike `sanitize`, this has no `--sanitize`-style
    /// alias — memprof is a profiler, not a "sanitize" in clang's sense. See
    /// `doc/05_design/compiler/backend/m4_llvm_mem_infra_design.md`.
    pub memprof: bool,
    /// Force conservative (memory-safe) compilation parallelism regardless of
    /// backend or host core count. Overrides the LLVM default-parallelism
    /// clamp below with an even tighter single-worker bound. See
    /// `init_rayon_pool` for why this exists: each parallel worker owns an
    /// independent LLVM `Context` + optimization pipeline, whose peak memory
    /// is far larger than Cranelift's, so unclamped `available_parallelism()`
    /// (the previous default) multiplies that peak by the host core count —
    /// this is what produced the 50-64 GB earlyoom kills on a 32-core box.
    pub low_memory: bool,
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
            // Cranelift owns the qualified native object/vtable ABI. LLVM
            // remains explicit until it implements equivalent layout and
            // external-vtable relocation support.
            backend: "cranelift".to_string(),
            runtime_path: None,
            runtime_bundle: "auto".to_string(),
            entry_closure: false,
            target: None,
            linker_script: None,
            opt_level: NativeOptimizationLevel::default_for_native_executable(),
            emit_archive: false,
            incremental_hardening: false,
            sanitize: false,
            memprof: false,
            low_memory: false,
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

    /// Resolve the configured cache root before target isolation.
    pub(crate) fn cache_base_dir(&self) -> PathBuf {
        self.config
            .cache_dir
            .clone()
            .unwrap_or_else(|| self.project_root.join(".simple/native_cache"))
    }

    /// Resolve the effective cache directory, including a cross-target triple.
    pub(crate) fn cache_dir(&self) -> PathBuf {
        let base = self.cache_base_dir();
        let target = effective_target();
        let targeted = if target.is_host() {
            base
        } else {
            base.join(target.triple_str())
        };
        // Per-lane private cache: entries are reachable only inside their own
        // (compiler identity, lane) scope, so a phase-2 lane's objects can never
        // be named — let alone hit — by a phase-3 lane sharing --cache-dir.
        let scoped = targeted.join(cache_scope_segment());
        write_cache_scope_marker(&scoped);
        scoped
    }

    pub(crate) fn effective_source_root_for(&self, path: &Path) -> PathBuf {
        let canonical_path = safe_canonicalize(path);
        let mut best: Option<PathBuf> = None;
        let mut best_depth = 0usize;
        let mut valid_dirs: Vec<PathBuf> = Vec::new();
        for dir in &self.source_dirs {
            let canonical_dir = safe_canonicalize(dir);
            if !canonical_dir.is_dir() {
                continue;
            }
            valid_dirs.push(canonical_dir.clone());
            if canonical_path.starts_with(&canonical_dir) {
                let depth = canonical_dir.components().count();
                if depth > best_depth {
                    best_depth = depth;
                    best = Some(canonical_dir);
                }
            }
        }
        // Multiple sibling `--source` roots (e.g. `src/app` + `src/compiler`) must not
        // each relativize a file against itself: that discards the very segment
        // (`app` vs `compiler`) that distinguishes them, so `src/app/__init__.spl`
        // and `src/compiler/__init__.spl` both sanitize to the same `__init__`
        // module name. When more than one configured source dir is real, relativize
        // against their common ancestor instead, so that distinguishing segment
        // survives. Single-root configurations are unaffected (valid_dirs.len() <= 1
        // always keeps the prior per-file "deepest match" behavior).
        if best.is_some() && valid_dirs.len() > 1 {
            if let Some(ancestor) = common_ancestor_of_dirs(&valid_dirs) {
                return ancestor;
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
    pub fn build(mut self) -> Result<NativeBuildResult, String> {
        if let Ok(backend) = std::env::var("SIMPLE_BACKEND") {
            if !matches!(backend.as_str(), "llvm" | "cranelift") {
                return Err(format!(
                    "invalid SIMPLE_BACKEND '{}', expected llvm or cranelift",
                    backend
                ));
            }
            self.config.backend = backend;
        }
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

        // Reject normalized-name collisions before clean/cache/staging can mutate state.
        let compile_indices: std::collections::HashSet<usize> = if self.config.entry_closure {
            (0..files.len()).collect()
        } else {
            Self::deduplicate_for_compilation(&files).into_iter().collect()
        };
        let mut module_paths: std::collections::HashMap<String, PathBuf> = std::collections::HashMap::new();
        for (i, (path, _)) in file_sources.iter().enumerate() {
            if !compile_indices.contains(&i) {
                continue;
            }
            let root = self.effective_source_root_for(path);
            let prefix = crate::codegen::common_backend::module_prefix_from_path(path, &root);
            let canonical_path = safe_canonicalize(path);
            if let Some(first) = module_paths.get(&prefix) {
                if first != &canonical_path {
                    return Err(format!(
                        "native module name collision after path sanitization: '{}' and '{}' both map to '{}'; rename one file or directory",
                        first.display(),
                        canonical_path.display(),
                        prefix
                    ));
                }
            } else {
                module_paths.insert(prefix, canonical_path);
            }
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
        let cache_base_dir = self.cache_base_dir();
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

        // 3. Stage .o files beside the cache so system-temp and cache cleanup cannot remove them.
        let mut temp_dir = Some(native_object_staging_dir(&cache_base_dir, &cache_dir)?);
        let temp_dir_path = temp_dir
            .as_ref()
            .map(|dir| dir.path().to_path_buf())
            .ok_or_else(|| "tempdir unexpectedly missing".to_string())?;

        // 4. Read all source files and determine dirty set
        let compile_start = Instant::now();
        // 4b. Discovery phase (hoisted above the dirty-set determination so the
        // opt-in safe-incremental object cache key can fold in every cross-module
        // codegen input): build the import map for cross-module function
        // resolution, and, when the safe-incremental path is active, fingerprint
        // the closure's global type layout / signatures from the same result.
        let incr_hardening = incremental_hardening_requested(self.config.incremental_hardening);
        let mut layout_fp: u64 = 0;
        let result = build_import_map(&file_sources, &self.source_dirs, &self.source_root);
        if let Some(collision) = &result.enum_runtime_collision {
            return Err(collision.clone());
        }
        let imports = if !self.config.no_mangle {
            // Always fingerprinted when the object cache is live: a module's object
            // bytes depend on OTHER modules' declarations, so the cross-module
            // digest is a CORRECTNESS input to the cache key, not an opt-in extra.
            if use_incremental {
                layout_fp = cross_module_layout_fingerprint(&result);
                if std::env::var("SIMPLE_DEBUG_LAYOUT_FP").is_ok() {
                    eprintln!(
                        "[layout-fp] fp={:016x} map={} all_mangled={} struct_defs={} enum_defs={} fn_arities={} fn_return_types={} data_exports={} trait_impls={}",
                        layout_fp,
                        result.map.len(),
                        result.all_mangled.len(),
                        result.struct_defs.len(),
                        result.enum_defs.len(),
                        result.fn_arities.len(),
                        result.fn_return_types.len(),
                        result.data_exports.len(),
                        result.trait_impls.len(),
                    );
                }
            }
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
                vtable_type_owners: std::sync::Arc::new(result.vtable_type_owners),
                vtable_symbols: std::sync::Arc::new(result.vtable_symbols),
                struct_defs: std::sync::Arc::new(result.struct_defs),
                unique_struct_owners: std::sync::Arc::new(result.unique_struct_owners),
                struct_module_owners: std::sync::Arc::new(result.struct_module_owners),
                duplicate_struct_defs: std::sync::Arc::new(result.duplicate_struct_defs),
                enum_defs: std::sync::Arc::new(result.enum_defs),
                enum_runtime_names: std::sync::Arc::new(result.enum_runtime_names),
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
                vtable_type_owners: std::sync::Arc::new(std::collections::HashSet::new()),
                vtable_symbols: std::sync::Arc::new(std::collections::HashMap::new()),
                struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
                unique_struct_owners: std::sync::Arc::new(std::collections::HashMap::new()),
                struct_module_owners: std::sync::Arc::new(std::collections::HashMap::new()),
                duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
                enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
                enum_runtime_names: std::sync::Arc::new(std::collections::HashMap::new()),
                data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
                fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
                fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
                populate_global_struct_defs: false,
                populate_global_enum_defs: false,
            }
        };

        // Global build fingerprint: folded into every per-module object cache key
        // whenever the object cache is live. Any change to opt-level, the
        // entry-closure flag, the target, the linker script, or the closure's
        // cross-module type layout / signatures invalidates the ENTIRE per-module
        // cache. Correctness strictly beats speed: this coarse over-invalidation
        // can only ever cause more rebuilds, never a stale (wrong-binary) reuse.
        //
        // This is deliberately NOT gated on `incr_hardening`. The dependency-blind
        // content-only key reuses a module object after a dependency it was
        // compiled against changed, which produces a WRONG BINARY; an env var must
        // not be able to select that. `incr_hardening` now only controls the
        // per-build `[native-incremental]` receipt.
        let global_fp: Option<GlobalBuildFingerprint> = if use_incremental {
            let ls_hash = self
                .config
                .linker_script
                .as_ref()
                .and_then(|p| std::fs::read(p).ok())
                .map(|bytes| hash_one(&bytes))
                .unwrap_or(0);
            let triple = effective_target().triple_str().to_string();
            Some(GlobalBuildFingerprint {
                producer: std::env::current_exe()
                    .ok()
                    .and_then(|path| std::fs::read(path).ok())
                    .map(|bytes| hash_one(&bytes))
                    .unwrap_or(0),
                opt_level: hash_one(&self.config.opt_level.as_str()),
                entry_closure: hash_one(&self.config.entry_closure),
                target: hash_one(&triple),
                linker_script: ls_hash,
                layout: layout_fp,
                instrumentation: hash_one(&(
                    self.config.backend == "llvm" && self.config.sanitize,
                    self.config.backend == "llvm" && self.config.memprof,
                )),
            })
        } else {
            None
        };
        let global_fp_combined: u64 = global_fp.as_ref().map(GlobalBuildFingerprint::combined).unwrap_or(0);

        let effective_backend = self.config.backend.as_str();

        // Determine which files need recompilation via content hash
        let mut to_compile: Vec<(usize, PathBuf, String, Option<PathBuf>)> = Vec::new();
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
                let cache_eligible = object_cache_eligible(is_entry, source);
                let mut immediate_cache = None;
                if cache_eligible {
                    let per_file_root = self.effective_source_root_for(path);
                    let module_prefix = crate::codegen::common_backend::module_prefix_from_path(path, &per_file_root);
                    let base_hash = object_cache_key(
                        source,
                        is_entry,
                        effective_backend,
                        self.config.no_mangle,
                        &module_prefix,
                        self.config.opt_level,
                    );
                    // Fold in the global build fingerprint so any cross-module
                    // structural change (a dependency this object was compiled
                    // against) misses the cache instead of silently reusing an
                    // object built against the OLD declarations.
                    let hash = hash_one(&(base_hash, global_fp_combined));
                    let cached_o = objects_dir.join(format!("{:016x}.o", hash));
                    if let Some(cached_bytes) = read_usable_cached_object(&cached_o) {
                        // Cache hit: use the bytes already read for validation
                        // instead of issuing a second filesystem read via copy.
                        let obj_path = temp_dir_path.join(format!("mod_{}.o", i));
                        if std::fs::write(&obj_path, cached_bytes).is_ok() {
                            cached_objects.push((i, obj_path));
                            continue;
                        }
                    }
                    // Persist every cache-eligible object as soon as its compile
                    // succeeds. The key already includes the full cross-module
                    // fingerprint, so mangled modules are just as safe to make
                    // durable here as no-mangle modules. Entry objects and
                    // inline-asm sidecars remain excluded above.
                    immediate_cache = Some(cached_o);
                }
                to_compile.push((i, path.clone(), source.clone(), immediate_cache));
            }
        } else {
            for (i, (path, source)) in file_sources.iter().enumerate() {
                // Skip symlink aliases -- only compile each physical file once
                if !compile_indices.contains(&i) {
                    continue;
                }
                to_compile.push((i, path.clone(), source.clone(), None));
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
            for (idx, path, _, _) in to_compile.iter().take(12) {
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

        // (Import map + global build fingerprint are hoisted above the dirty-set
        //  determination -- see section 4b -- so the incremental object cache key
        //  can fold in the closure's cross-module codegen inputs before deciding
        //  which modules are dirty.)

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

        // 6. Cache writes happen atomically per successful module in the compile
        // workers. This intentionally leaves useful keyed objects behind when a
        // sibling module fails or the process is interrupted before link.

        // 6b. Safe-incremental cache summary + manifest (one line per build).
        // Names the changed component when a global input forced a full rebuild,
        // so a wide rebuild is never mistaken for a broken cache.
        if let Some(ref gfp) = global_fp {
            let manifest_path = cache_dir.join("incremental_manifest.txt");
            let reason: Option<&'static str> = std::fs::read_to_string(&manifest_path)
                .ok()
                .and_then(|line| GlobalBuildFingerprint::from_manifest_line(&line))
                .and_then(|prev| gfp.changed_reason(&prev));
            let rebuilt = freshly_compiled.len();
            // The receipt itself stays opt-in (`SIMPLE_NATIVE_INCREMENTAL=1`) so
            // default build output is unchanged; the KEY above is unconditional.
            if incr_hardening {
                match reason {
                    Some(why) => eprintln!(
                        "[native-incremental] {cached_count} reused / {rebuilt} rebuilt (full rebuild: {why})"
                    ),
                    None => eprintln!("[native-incremental] {cached_count} reused / {rebuilt} rebuilt"),
                }
            }
            let _ = std::fs::write(&manifest_path, gfp.to_manifest_line());
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
        let Some(registry_sdn) = security_registry_sdn_from_sources(file_sources, Some(&self.project_root))? else {
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

fn security_registry_sdn_from_sources(
    file_sources: &[(PathBuf, String)],
    project_hint: Option<&Path>,
) -> Result<Option<String>, String> {
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
        // Single-file lenient lowering here has no cross-module type resolution
        // (ModuleResolver::single_file_with_project_hint), unlike the main
        // whole-program lowering pass. A file that matched source_may_declare_security
        // can still reference a cross-module type (e.g. a Result<T, E> return type
        // defined in another file) that this isolated pass cannot resolve, which
        // collapses the field type to ANY and hard-fails lowering with
        // "cannot infer field type while lowering ... struct 'ANY' field '...'"
        // even though the main pass lowers the same file fine. This auxiliary scan
        // only needs require_policy:/enter_sandbox:/lowered_backend: markers, not
        // full type-soundness on unrelated fields, so skip (rather than hard-fail
        // the whole native-build) a file this isolated pass can't lower. See
        // doc/08_tracking/bug/wm_production_fullscreen_evidence_security_registry_any_field_infer_2026-08-09.md
        let module = match crate::hir::lower_with_context_lenient_and_project_hint(&ast, path, project_hint) {
            Ok(module) => module,
            Err(_) => continue,
        };
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

fn object_cache_eligible(is_entry: bool, source: &str) -> bool {
    !is_entry && !source_may_emit_inline_asm_sidecar(source)
}

fn source_may_declare_security(source: &str) -> bool {
    source.lines().any(|line| {
        let trimmed = line.trim_start();
        ["security", "sandbox", "capability"].iter().any(|keyword| {
            let Some(rest) = trimmed.strip_prefix(keyword) else {
                return false;
            };
            if rest.starts_with(':') {
                return true;
            }
            if !rest.chars().next().is_some_and(|ch| ch.is_ascii_whitespace()) {
                return false;
            }
            let rest = rest.trim_start();
            let Some((head, _)) = rest.split_once(':') else {
                return false;
            };
            !head.is_empty()
                && head
                    .chars()
                    .all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' || ch.is_ascii_whitespace())
        })
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

/// Declared private-cache lane for this process (`SIMPLE_CACHE_SCOPE`).
///
/// Concurrent bootstrap lanes (phase-1 seed, phase-2 stage, phase-3 self-host,
/// phase-4 full CLI, census, tool builds) may run DIFFERENT compiler binaries
/// over the SAME source tree while sharing one `--cache-dir`. `compiler_fingerprint`
/// separates different binaries, but two lanes can legitimately share a binary
/// and still must not share entries — and a lane must be able to DECLARE its
/// cache private rather than depend on a fingerprint a mid-run redeploy changes
/// underneath it.
///
/// Unset means `default`, which reproduces the previous single-lane behaviour.
/// See `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`.
pub fn cache_lane() -> String {
    match std::env::var("SIMPLE_CACHE_SCOPE") {
        Ok(name) if !name.trim().is_empty() => name.trim().to_string(),
        _ => "default".to_string(),
    }
}

/// Directory segment that makes a cache entry reachable ONLY within its own
/// (compiler identity, lane) scope. Cross-scope lookups cannot name an
/// out-of-scope entry at all, so the MISS is structural, not a hash comparison.
pub fn cache_scope_segment() -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    cache_lane().hash(&mut hasher);
    compiler_fingerprint().hash(&mut hasher);
    format!("scope-{:016x}", hasher.finish())
}

/// Record the lane that owns a cache directory so a SCRIPT can check ownership
/// without running a compiler (`scripts/check/check-cache-scope-ownership.shs`).
fn write_cache_scope_marker(dir: &Path) {
    let _ = std::fs::create_dir_all(dir);
    let _ = std::fs::write(dir.join(".cache_scope"), format!("lane={}\n", cache_lane()));
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
///
/// NOTE: this is only the per-module BASE key. It intentionally does not know
/// about the module's dependencies; callers MUST fold in
/// `GlobalBuildFingerprint::combined()` (which carries the cross-module layout /
/// signature digest from `cross_module_layout_fingerprint`) before using the
/// result as a cache filename. Using this value alone reuses an object after a
/// dependency changed and ships a wrong binary.
pub(crate) fn object_cache_key(
    content: &str,
    is_entry: bool,
    backend: &str,
    no_mangle: bool,
    module_prefix: &str,
    opt_level: NativeOptimizationLevel,
) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    content.hash(&mut hasher);
    is_entry.hash(&mut hasher);
    backend.hash(&mut hasher);
    no_mangle.hash(&mut hasher);
    module_prefix.hash(&mut hasher);
    opt_level.as_str().hash(&mut hasher);
    std::env::var("SIMPLE_NATIVE_CPU").unwrap_or_default().hash(&mut hasher);
    active_simd_tier_name().hash(&mut hasher);
    compiler_fingerprint().hash(&mut hasher);
    // Belt-and-braces with the scope DIRECTORY partition: even a cache dir
    // hand-pointed at by two lanes yields different keys per lane.
    cache_lane().hash(&mut hasher);
    hasher.finish()
}

/// True when the per-build `[native-incremental] N reused / M rebuilt` receipt
/// is printed.
///
/// Gated by `SIMPLE_NATIVE_INCREMENTAL=1` (default off) OR the equivalent
/// `NativeBuildConfig::incremental_hardening` flag (used by tests to avoid
/// racing the process-global env var).
///
/// This no longer gates cache-key CORRECTNESS: the dependency-aware key
/// (cross-module layout/signature digest + target + opt-level + linker script)
/// is now unconditional, because the legacy content-only key could reuse an
/// object after a dependency changed and produce a wrong binary.
pub(crate) fn incremental_hardening_requested(config_flag: bool) -> bool {
    config_flag || std::env::var("SIMPLE_NATIVE_INCREMENTAL").as_deref() == Ok("1")
}

/// Hash a single hashable value to a `u64`.
fn hash_one<T: std::hash::Hash>(value: &T) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Commutatively fold a per-entry hash into an accumulator so the (unordered)
/// iteration order of `HashMap`/`HashSet` does not affect the final digest.
fn fold_unordered(acc: u64, item: u64) -> u64 {
    // wrapping add of a mixed item -> order-independent (addition is commutative)
    acc.wrapping_add(item.wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(31))
}

/// Fingerprint of EVERY cross-module input the compiler feeds into a module's
/// HIR lowering + codegen when name mangling / global-def population is active.
///
/// Under `--entry-closure` (and any `!no_mangle` build), each module is lowered
/// with the whole closure's `struct_defs`/`enum_defs` injected into its type
/// registry and its cross-module calls resolved through the shared import map.
/// That means a module's object *bytes* depend on OTHER modules' declarations
/// (field offsets, enum tags, mangled call targets). The legacy per-module key
/// hashes only that module's own source, so a struct change in module A leaves
/// module B's source hash unchanged and B silently reuses an object built
/// against A's OLD layout — a stale, wrong binary.
///
/// This digest folds in all such inputs. Any change to it invalidates the whole
/// per-module cache (coarse but strictly conservative: it can only ever cause
/// MORE rebuilds, never a wrong reuse). It is intentionally order-independent so
/// nondeterministic map iteration order does not spuriously bust the cache.
pub(crate) fn cross_module_layout_fingerprint(result: &imports::ImportMapResult) -> u64 {
    let mut fp: u64 = 0;
    for (k, v) in result.map.iter() {
        fp = fold_unordered(fp, hash_one(&(k, v)));
    }
    for k in result.ambiguous.iter() {
        fp = fold_unordered(fp, hash_one(&("amb", k)));
    }
    for (k, v) in result.all_mangled.iter() {
        fp = fold_unordered(fp, hash_one(&(k, v)));
    }
    for (k, inner) in result.re_exports.iter() {
        let mut inner_fp: u64 = 0;
        for (ik, iv) in inner.iter() {
            inner_fp = fold_unordered(inner_fp, hash_one(&(ik, iv)));
        }
        fp = fold_unordered(fp, hash_one(&(k, inner_fp)));
    }
    for (k, v) in result.trait_impls.iter() {
        fp = fold_unordered(fp, hash_one(&(k, v)));
    }
    for owner in result.vtable_type_owners.iter() {
        fp = fold_unordered(fp, hash_one(&("vtable-owner", owner)));
    }
    for (owner, symbol) in result.vtable_symbols.iter() {
        fp = fold_unordered(fp, hash_one(&("vtable-symbol", owner, symbol)));
    }
    for (k, v) in result.struct_defs.iter() {
        fp = fold_unordered(fp, hash_one(&(k, format!("{v:?}"))));
    }
    for (k, v) in result.duplicate_struct_defs.iter() {
        fp = fold_unordered(fp, hash_one(&(k, format!("{v:?}"))));
    }
    for (k, v) in result.enum_defs.iter() {
        fp = fold_unordered(fp, hash_one(&(k, format!("{v:?}"))));
    }
    for (k, v) in result.enum_runtime_names.iter() {
        fp = fold_unordered(fp, hash_one(&(k, v)));
    }
    for k in result.data_exports.iter() {
        fp = fold_unordered(fp, hash_one(&("data", k)));
    }
    for (k, v) in result.fn_arities.iter() {
        fp = fold_unordered(fp, hash_one(&(k, v)));
    }
    for (k, v) in result.fn_return_types.iter() {
        fp = fold_unordered(fp, hash_one(&(k, format!("{v:?}"))));
    }
    fp
}

/// The component hashes of the global build fingerprint. Stored in the
/// per-build manifest so a full-rebuild reason can name WHICH input changed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct GlobalBuildFingerprint {
    pub producer: u64,
    pub opt_level: u64,
    pub entry_closure: u64,
    pub target: u64,
    pub linker_script: u64,
    pub layout: u64,
    pub instrumentation: u64,
}

impl GlobalBuildFingerprint {
    /// Collapse the components into a single digest folded into each object key.
    pub(crate) fn combined(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.producer.hash(&mut hasher);
        self.opt_level.hash(&mut hasher);
        self.entry_closure.hash(&mut hasher);
        self.target.hash(&mut hasher);
        self.linker_script.hash(&mut hasher);
        self.layout.hash(&mut hasher);
        self.instrumentation.hash(&mut hasher);
        hasher.finish()
    }

    /// Human-readable name of the first component that differs from `prev`
    /// (used to explain a full rebuild). Returns None when unchanged.
    pub(crate) fn changed_reason(&self, prev: &GlobalBuildFingerprint) -> Option<&'static str> {
        if self.producer != prev.producer {
            Some("compiler producer changed")
        } else if self.opt_level != prev.opt_level {
            Some("opt-level changed")
        } else if self.entry_closure != prev.entry_closure {
            Some("entry-closure flag changed")
        } else if self.target != prev.target {
            Some("target changed")
        } else if self.linker_script != prev.linker_script {
            Some("linker script changed")
        } else if self.layout != prev.layout {
            Some("cross-module type layout / signatures changed")
        } else if self.instrumentation != prev.instrumentation {
            Some("codegen instrumentation changed")
        } else {
            None
        }
    }

    /// Serialize to the manifest line format used beside cached objects.
    pub(crate) fn to_manifest_line(&self) -> String {
        format!(
            "producer={:016x};opt={:016x};ec={:016x};t={:016x};ls={:016x};layout={:016x};instr={:016x}",
            self.producer,
            self.opt_level,
            self.entry_closure,
            self.target,
            self.linker_script,
            self.layout,
            self.instrumentation
        )
    }

    /// Parse a manifest line produced by `to_manifest_line`.
    pub(crate) fn from_manifest_line(line: &str) -> Option<GlobalBuildFingerprint> {
        let mut fp = GlobalBuildFingerprint {
            producer: 0,
            opt_level: 0,
            entry_closure: 0,
            target: 0,
            linker_script: 0,
            layout: 0,
            instrumentation: 0,
        };
        let mut seen = 0;
        for part in line.trim().split(';') {
            let (key, val) = part.split_once('=')?;
            let n = u64::from_str_radix(val.trim(), 16).ok()?;
            match key.trim() {
                "producer" => fp.producer = n,
                "opt" => fp.opt_level = n,
                "ec" => fp.entry_closure = n,
                "t" => fp.target = n,
                "ls" => fp.linker_script = n,
                "layout" => fp.layout = n,
                "instr" => fp.instrumentation = n,
                _ => continue,
            }
            seen += 1;
        }
        if seen == 7 {
            Some(fp)
        } else {
            None
        }
    }
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
///
/// When more than one configured source dir is a real directory, this mirrors
/// `NativeProjectBuilder::effective_source_root_for`: it relativizes against the
/// *common ancestor* of all the valid source dirs rather than the single deepest
/// match, so sibling `--source` roots (e.g. `src/app` + `src/compiler`) keep the
/// segment that distinguishes them instead of both collapsing to the same
/// sanitized module name. Single-root configurations are unaffected.
pub(crate) fn source_root_for_file(file_path: &Path, source_dirs: &[PathBuf], fallback: &Path) -> PathBuf {
    let canonical_path = safe_canonicalize(file_path);
    let mut best: Option<PathBuf> = None;
    let mut best_depth = 0usize;
    let mut valid_dirs: Vec<PathBuf> = Vec::new();
    for dir in source_dirs {
        let canonical_dir = safe_canonicalize(dir);
        if !canonical_dir.is_dir() {
            continue;
        }
        valid_dirs.push(canonical_dir.clone());
        if canonical_path.starts_with(&canonical_dir) {
            let depth = canonical_dir.components().count();
            if depth > best_depth {
                best_depth = depth;
                best = Some(canonical_dir);
            }
        }
    }
    if best.is_some() && valid_dirs.len() > 1 {
        if let Some(ancestor) = common_ancestor_of_dirs(&valid_dirs) {
            return ancestor;
        }
    }
    best.unwrap_or_else(|| fallback.to_path_buf())
}

/// Longest common path-component ancestor of `dirs`, or `None` if `dirs` is
/// empty or the paths share no component (e.g. different filesystem roots on
/// Windows). Used to relativize a file against the shared root of several
/// sibling `--source` directories instead of the one directory that happens to
/// contain it, which would otherwise discard the segment that makes sibling
/// roots distinguishable (see `effective_source_root_for` / `source_root_for_file`).
fn common_ancestor_of_dirs(dirs: &[PathBuf]) -> Option<PathBuf> {
    let mut iter = dirs.iter();
    let first = iter.next()?;
    let mut common: Vec<std::path::Component> = first.components().collect();
    for dir in iter {
        let comps: Vec<std::path::Component> = dir.components().collect();
        let shared = common.iter().zip(comps.iter()).take_while(|(a, b)| a == b).count();
        common.truncate(shared);
        if common.is_empty() {
            return None;
        }
    }
    if common.is_empty() {
        None
    } else {
        Some(common.into_iter().collect())
    }
}
