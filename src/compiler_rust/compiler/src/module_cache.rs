//! Module caching and loading state management
//!
//! This module provides thread-local caching for loaded modules and tracking
//! of modules currently being loaded (for circular import detection).

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

use tracing::trace;
use crate::interpreter::{
    FUNCTION_MODULE_OWNER, FUNCTION_OVERLOADS, MODULE_ENV_BY_OWNER, MODULE_GLOBALS, MODULE_GLOBAL_BINDINGS_BY_OWNER,
    MODULE_GLOBALS_BY_OWNER, MODULE_GLOBALS_INITIAL_BY_OWNER,
};

use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef};

/// Check if loader tracing/summary is enabled via SIMPLE_LOADER_TRACE env var.
fn loader_stats_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("SIMPLE_LOADER_TRACE")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}

/// Diagnostic: report per-cache entry counts alongside RSS.
/// Gated behind SIMPLE_CACHE_SIZE_REPORT=<N> (report every N module loads).
fn cache_size_report_interval() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| {
        std::env::var("SIMPLE_CACHE_SIZE_REPORT")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(0)
    })
}

fn rss_kb() -> u64 {
    std::fs::read_to_string("/proc/self/statm")
        .ok()
        .and_then(|s| s.split_whitespace().nth(1).and_then(|v| v.parse::<u64>().ok()))
        .map(|pages| pages * 4)
        .unwrap_or(0)
}

/// Print a one-line breakdown of every never-evicted loader cache.
pub fn report_cache_sizes(tag: &str) {
    let exports = MODULE_EXPORTS_CACHE.with(|c| c.borrow().len());
    let (cls_m, cls_e) = MODULE_CLASSES_CACHE
        .with(|c| (c.borrow().len(), c.borrow().values().map(|m| m.len()).sum::<usize>()));
    let (fn_m, fn_e) = MODULE_FUNCTIONS_CACHE
        .with(|c| (c.borrow().len(), c.borrow().values().map(|m| m.len()).sum::<usize>()));
    let (en_m, en_e) = MODULE_ENUMS_CACHE
        .with(|c| (c.borrow().len(), c.borrow().values().map(|m| m.len()).sum::<usize>()));
    let partial = PARTIAL_MODULE_EXPORTS_CACHE.with(|c| c.borrow().len());
    let (env_m, env_e) =
        MODULE_ENV_BY_OWNER.with(|c| (c.borrow().len(), c.borrow().values().map(|e| e.len()).sum::<usize>()));
    let (ovl_k, ovl_e) =
        FUNCTION_OVERLOADS.with(|c| (c.borrow().len(), c.borrow().values().map(|v| v.len()).sum::<usize>()));
    eprintln!(
        "[cache-size] {} rss_mb={} exports={} classes={}m/{}e functions={}m/{}e enums={}m/{}e partial={} env_by_owner={}m/{}e overloads={}k/{}e",
        tag,
        rss_kb() / 1024,
        exports,
        cls_m, cls_e,
        fn_m, fn_e,
        en_m, en_e,
        partial,
        env_m, env_e,
        ovl_k, ovl_e
    );
}

/// Aggregated loader statistics for diagnosing heavy-path imports.
/// Gated behind SIMPLE_LOADER_TRACE=1.
#[derive(Default)]
struct LoaderStats {
    /// Number of times each module path was visited (including cache hits)
    visit_counts: HashMap<PathBuf, u32>,
    /// Cumulative evaluation time per module in microseconds (excludes cache hits)
    eval_time_us: HashMap<PathBuf, u128>,
    /// Maximum recursion depth seen during this session
    max_depth_seen: usize,
    /// Total unique modules loaded (non-cached)
    total_loaded: usize,
    /// Total sibling preload evaluations
    sibling_preloads: usize,
}

// Thread-local cache for normalize_path_key to avoid repeated canonicalize() syscalls
thread_local! {
    static PATH_KEY_CACHE: RefCell<HashMap<PathBuf, PathBuf>> = RefCell::new(HashMap::new());
    /// `filter_functions_from_value` memo: source dict ptr -> (source Arc, filtered Arc).
    static FILTERED_DICT_CACHE: RefCell<HashMap<usize, (Arc<HashMap<String, Value>>, Arc<HashMap<String, Value>>)>> =
        RefCell::new(HashMap::new());
    static LOADER_STATS: RefCell<LoaderStats> = RefCell::new(LoaderStats::default());
}

/// Maximum depth for recursive module loading to prevent infinite loops
pub const MAX_MODULE_DEPTH: usize = 50;

// Thread-local cache for module exports to avoid re-parsing modules
// Key: normalized module path, Value: module exports dict
thread_local! {
    pub static MODULE_EXPORTS_CACHE: RefCell<HashMap<PathBuf, Value>> = RefCell::new(HashMap::new());
    static MODULE_EXPORT_OWNERS: RefCell<HashMap<usize, Arc<str>>> = RefCell::new(HashMap::new());
    // Cache for ClassDef objects (Arc-wrapped for cheap sharing)
    pub static MODULE_CLASSES_CACHE: RefCell<HashMap<PathBuf, HashMap<String, Arc<ClassDef>>>> = RefCell::new(HashMap::new());
    // Cache for FunctionDef objects (Arc-wrapped for cheap sharing with Value::Function)
    pub static MODULE_FUNCTIONS_CACHE: RefCell<HashMap<PathBuf, HashMap<String, Arc<FunctionDef>>>> = RefCell::new(HashMap::new());
    // Cache for EnumDef objects (Arc-wrapped for cheap sharing)
    pub static MODULE_ENUMS_CACHE: RefCell<HashMap<PathBuf, HashMap<String, Arc<EnumDef>>>> = RefCell::new(HashMap::new());
    // Track modules currently being loaded to prevent circular import infinite recursion
    pub static MODULES_LOADING: RefCell<std::collections::HashSet<PathBuf>> = RefCell::new(std::collections::HashSet::new());
    // Track current loading depth to prevent infinite recursion
    pub static MODULE_LOAD_DEPTH: RefCell<usize> = const { RefCell::new(0) };
    // Cache for partial exports (type definitions only) - used for circular import resolution
    // This contains exports after register_definitions but before process_imports_and_assignments
    pub static PARTIAL_MODULE_EXPORTS_CACHE: RefCell<HashMap<PathBuf, Value>> = RefCell::new(HashMap::new());
    // Total modules loaded counter - reset between test files to prevent OOM
    pub static TOTAL_MODULES_LOADED: RefCell<usize> = const { RefCell::new(0) };
}

/// Clear the module exports cache (useful between test runs)
pub fn clear_module_cache() {
    MODULE_EXPORTS_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULE_EXPORT_OWNERS.with(|cache| cache.borrow_mut().clear());
    MODULE_CLASSES_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULE_FUNCTIONS_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULE_ENUMS_CACHE.with(|cache| cache.borrow_mut().clear());
    MODULE_GLOBALS.with(|cache| cache.borrow_mut().clear());
    MODULE_GLOBALS_BY_OWNER.with(|cache| *cache.borrow_mut() = Arc::new(HashMap::new()));
    MODULE_GLOBALS_INITIAL_BY_OWNER.with(|cache| cache.borrow_mut().clear());
    MODULE_ENV_BY_OWNER.with(|cache| cache.borrow_mut().clear());
    MODULE_GLOBAL_BINDINGS_BY_OWNER.with(|cache| cache.borrow_mut().clear());
    FUNCTION_MODULE_OWNER.with(|cache| cache.borrow_mut().clear());
    FUNCTION_OVERLOADS.with(|cache| cache.borrow_mut().clear());
    MODULES_LOADING.with(|loading| loading.borrow_mut().clear());
    MODULE_LOAD_DEPTH.with(|depth| *depth.borrow_mut() = 0);
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| cache.borrow_mut().clear());
    TOTAL_MODULES_LOADED.with(|c| *c.borrow_mut() = 0);
    PATH_KEY_CACHE.with(|cache| cache.borrow_mut().clear());
    FILTERED_DICT_CACHE.with(|cache| cache.borrow_mut().clear());
    // Print loader summary before clearing (if SIMPLE_LOADER_TRACE=1)
    print_loader_summary();
    crate::mem_trace::report("clear_module_cache");
    crate::memory_guard::print_diagnostics();
    crate::memory_guard::reset_stats();
    // Print resolve stats before clearing (if profiling enabled)
    super::interpreter_module::print_resolve_stats();
    // Also clear path resolution cache
    super::interpreter_module::clear_path_resolution_cache();
    super::interpreter_module::reset_resolve_stats();
    // And the compile-pipeline directory-listing cache
    crate::pipeline::module_loader::clear_pipeline_dir_listing_cache();
}

/// Clear module cache selectively — preserve stdlib modules (src/lib/) between tests.
/// Only clears test-file-specific state while keeping parsed stdlib in cache.
/// This avoids re-parsing std.spec, std.io, etc. for every test file.
pub fn clear_module_cache_selective() {
    // Helper: retain only entries whose path contains "src/lib/" (stdlib)
    fn is_stdlib(p: &Path) -> bool {
        let s = p.to_string_lossy();
        s.contains("src/lib/") || s.contains("src\\lib\\")
    }

    MODULE_EXPORTS_CACHE.with(|cache| cache.borrow_mut().retain(|k, _| is_stdlib(k)));
    MODULE_EXPORT_OWNERS.with(|cache| {
        cache
            .borrow_mut()
            .retain(|_, owner| is_stdlib(Path::new(owner.as_ref())));
    });
    MODULE_CLASSES_CACHE.with(|cache| cache.borrow_mut().retain(|k, _| is_stdlib(k)));
    MODULE_FUNCTIONS_CACHE.with(|cache| cache.borrow_mut().retain(|k, _| is_stdlib(k)));
    MODULE_ENUMS_CACHE.with(|cache| cache.borrow_mut().retain(|k, _| is_stdlib(k)));
    MODULE_GLOBALS.with(|cache| cache.borrow_mut().clear());
    FUNCTION_OVERLOADS.with(|cache| cache.borrow_mut().clear());
    MODULE_GLOBALS_INITIAL_BY_OWNER.with(|cache| {
        cache
            .borrow_mut()
            .retain(|owner, _| is_stdlib(Path::new(owner.as_ref())));
    });
    crate::interpreter::reset_owned_globals_from_initial();
    MODULE_ENV_BY_OWNER.with(|cache| {
        cache
            .borrow_mut()
            .retain(|owner, _| is_stdlib(Path::new(owner.as_ref())));
    });
    MODULE_GLOBAL_BINDINGS_BY_OWNER.with(|cache| {
        cache
            .borrow_mut()
            .retain(|owner, _| is_stdlib(Path::new(owner.as_ref())));
    });
    FUNCTION_MODULE_OWNER.with(|cache| {
        cache
            .borrow_mut()
            .retain(|_, owner| is_stdlib(Path::new(owner.as_ref())));
    });
    // Always clear loading/depth state (transient per-file)
    MODULES_LOADING.with(|loading| loading.borrow_mut().clear());
    MODULE_LOAD_DEPTH.with(|depth| *depth.borrow_mut() = 0);
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| cache.borrow_mut().clear());
    // Drop memoised filtered dicts whose source no one else holds any more.
    FILTERED_DICT_CACHE.with(|cache| cache.borrow_mut().retain(|_, (src, _)| Arc::strong_count(src) > 1));
    // Reset module counter but don't clear PATH_KEY_CACHE (path normalization is stable)
    TOTAL_MODULES_LOADED.with(|c| *c.borrow_mut() = 0);
    // Keep path resolution cache (stable across tests)
    super::interpreter_module::reset_resolve_stats();
    crate::memory_guard::reset_stats();
}

/// Increment total modules loaded counter, return new count
pub fn increment_total_modules() -> usize {
    TOTAL_MODULES_LOADED.with(|c| {
        let mut v = c.borrow_mut();
        *v += 1;
        *v
    })
}

/// Undo a failed module-load reservation.
fn decrement_total_modules() {
    TOTAL_MODULES_LOADED.with(|c| {
        let mut v = c.borrow_mut();
        *v = v.checked_sub(1).expect("module-load reservation underflow");
    });
}

/// A module-load budget slot. Dropping an uncommitted reservation rolls it back.
pub struct ModuleLoadReservation {
    committed: bool,
}

impl ModuleLoadReservation {
    pub fn commit(mut self) {
        self.committed = true;
    }
}

impl Drop for ModuleLoadReservation {
    fn drop(&mut self) {
        if !self.committed {
            decrement_total_modules();
        }
    }
}

/// Reserve one module-load budget slot, rejecting without retaining an over-limit attempt.
pub fn reserve_module_load(limit: usize) -> Result<ModuleLoadReservation, usize> {
    let total = increment_total_modules();
    if crate::memory_guard::module_limit_exceeded(total, limit) {
        decrement_total_modules();
        return Err(total);
    }
    Ok(ModuleLoadReservation { committed: false })
}

#[cfg(test)]
pub(crate) fn total_modules_loaded() -> usize {
    TOTAL_MODULES_LOADED.with(|c| *c.borrow())
}

/// Reset total modules loaded counter
pub fn reset_total_modules() {
    TOTAL_MODULES_LOADED.with(|c| *c.borrow_mut() = 0);
}

/// Normalize a path to a consistent key for caching/tracking.
/// Uses canonicalize if the file exists, otherwise normalizes the path string.
/// Results are cached to avoid repeated filesystem syscalls.
pub fn normalize_path_key(path: &Path) -> PathBuf {
    let path_buf = path.to_path_buf();
    if let Some(cached) = PATH_KEY_CACHE.with(|cache| cache.borrow().get(&path_buf).cloned()) {
        return cached;
    }

    let result = normalize_path_key_uncached(path);

    PATH_KEY_CACHE.with(|cache| {
        cache.borrow_mut().insert(path_buf, result.clone());
    });

    result
}

fn normalize_path_key_uncached(path: &Path) -> PathBuf {
    // First try to canonicalize (works if file exists)
    if let Ok(canonical) = path.canonicalize() {
        return canonical;
    }

    // If file doesn't exist yet, normalize the path manually
    // This handles cases like "./foo/../bar" -> "./bar"
    let mut components: Vec<std::path::Component> = Vec::new();
    for component in path.components() {
        match component {
            std::path::Component::ParentDir => {
                // Go up one level if possible
                if !components.is_empty() {
                    if let Some(std::path::Component::Normal(_)) = components.last() {
                        components.pop();
                        continue;
                    }
                }
                components.push(component);
            }
            std::path::Component::CurDir => {
                // Skip "." components
            }
            _ => components.push(component),
        }
    }

    components.iter().collect()
}

/// Check if a module is currently being loaded (circular import detection)
pub fn is_module_loading(path: &Path) -> bool {
    let key = normalize_path_key(path);
    MODULES_LOADING.with(|loading| {
        let result = loading.borrow().contains(&key);
        trace!(path = ?key, is_loading = result, set_size = loading.borrow().len(), "Checking if module is loading");
        result
    })
}

/// Mark a module as currently loading
pub fn mark_module_loading(path: &Path) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Marking module as loading");
    MODULES_LOADING.with(|loading| {
        loading.borrow_mut().insert(key);
    });
}

/// Unmark a module as loading (finished loading)
pub fn unmark_module_loading(path: &Path) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Unmarking module as loading");
    MODULES_LOADING.with(|loading| {
        loading.borrow_mut().remove(&key);
    });
}

/// Increment the module load depth and return the new depth
pub fn increment_load_depth() -> usize {
    MODULE_LOAD_DEPTH.with(|depth| {
        let mut d = depth.borrow_mut();
        *d += 1;
        *d
    })
}

/// Decrement the module load depth
pub fn decrement_load_depth() {
    MODULE_LOAD_DEPTH.with(|depth| {
        let mut d = depth.borrow_mut();
        if *d > 0 {
            *d -= 1;
        }
    });
}

/// Get current module load depth
#[allow(dead_code)] // reason: reachable via SFFI or future entry point; not yet wired
pub fn get_load_depth() -> usize {
    MODULE_LOAD_DEPTH.with(|depth| *depth.borrow())
}

/// Get cached module exports for a path, if available
pub fn get_cached_module_exports(path: &Path) -> Option<Value> {
    let key = normalize_path_key(path);
    MODULE_EXPORTS_CACHE.with(|cache| {
        let result = cache.borrow().get(&key).cloned();
        if result.is_some() {
            trace!(path = ?key, "Module cache hit");
        }
        result
    })
}

/// Cache module exports for a path
pub fn cache_module_exports(path: &Path, exports: Value) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Caching module exports");
    if let Value::Dict(dict) = &exports {
        let owner: Arc<str> = Arc::from(key.to_string_lossy().as_ref());
        MODULE_EXPORT_OWNERS.with(|cache| {
            cache.borrow_mut().insert(Arc::as_ptr(dict) as usize, owner);
        });
    }
    MODULE_EXPORTS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key, exports);
    });
}

pub fn module_exports_owner(exports: &Value) -> Option<Arc<str>> {
    let Value::Dict(dict) = exports else {
        return None;
    };
    MODULE_EXPORT_OWNERS.with(|cache| cache.borrow().get(&(Arc::as_ptr(dict) as usize)).cloned())
}

/// Cache module definitions (classes, functions, enums) for a path.
/// Functions are stored as `Arc<FunctionDef>` for cheap sharing with `Value::Function`.
pub fn cache_module_definitions(
    path: &Path,
    classes: &HashMap<String, Arc<ClassDef>>,
    functions: &HashMap<String, Arc<FunctionDef>>,
    enums: &HashMap<String, Arc<EnumDef>>,
) {
    let key = normalize_path_key(path);
    trace!(path = ?key, classes = classes.len(), functions = functions.len(), enums = enums.len(), "Caching module definitions");
    MODULE_CLASSES_CACHE.with(|cache| {
        cache.borrow_mut().insert(key.clone(), classes.clone());
    });
    MODULE_FUNCTIONS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key.clone(), functions.clone());
    });
    MODULE_ENUMS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key, enums.clone());
    });
    let interval = cache_size_report_interval();
    if interval > 0 {
        let n = MODULE_EXPORTS_CACHE.with(|c| c.borrow().len());
        if n % interval == 0 {
            report_cache_sizes(&format!("modules={}", n));
        }
    }
}

/// Get cached module definitions and merge them into the provided HashMaps.
/// Functions are `Arc<FunctionDef>` -- cloning is a cheap reference-count bump.
/// Returns true if definitions were found and merged, false otherwise.
pub fn merge_cached_module_definitions(
    path: &Path,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    enums: &mut HashMap<String, Arc<EnumDef>>,
) -> bool {
    let key = normalize_path_key(path);
    let mut found = false;

    MODULE_CLASSES_CACHE.with(|cache| {
        if let Some(cached_classes) = cache.borrow().get(&key) {
            for (name, class_def) in cached_classes {
                classes.insert(name.clone(), class_def.clone());
            }
            found = true;
        }
    });

    MODULE_FUNCTIONS_CACHE.with(|cache| {
        if let Some(cached_functions) = cache.borrow().get(&key) {
            for (name, func_def) in cached_functions {
                if name != "main" {
                    // Don't add "main" from imported modules -- Arc clone is cheap
                    functions.insert(name.clone(), func_def.clone());
                    // See the matching guard in evaluation_helpers.rs::process_use_stmt:
                    // this same `func_def` Arc may already be registered in the
                    // process-wide FUNCTION_OVERLOADS map from an earlier pass over
                    // this module. Dedup by pointer identity to cap unbounded
                    // overload-list growth across repeated cache-hit imports (this
                    // alone does not fix the mutation-loss bug — see the longer
                    // note at the matching site for why; the real fix is
                    // `exec_function_with_values_and_writeback` in
                    // interpreter_call/core/function_exec.rs).
                    FUNCTION_OVERLOADS.with(|cell| {
                        let mut overloads = cell.borrow_mut();
                        let entry = overloads.entry(name.clone()).or_default();
                        if !entry.iter().any(|existing| Arc::ptr_eq(existing, func_def)) {
                            entry.push(func_def.clone());
                        }
                    });
                }
            }
        }
    });

    MODULE_ENUMS_CACHE.with(|cache| {
        if let Some(cached_enums) = cache.borrow().get(&key) {
            for (name, enum_def) in cached_enums {
                enums.insert(name.clone(), enum_def.clone());
            }
        }
    });

    if found {
        trace!(path = ?key, "Merged cached module definitions");
    }
    found
}

/// Get partial module exports (type definitions only) for circular import resolution
pub fn get_partial_module_exports(path: &Path) -> Option<Value> {
    let key = normalize_path_key(path);
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| {
        let result = cache.borrow().get(&key).cloned();
        if result.is_some() {
            trace!(path = ?key, "Partial module exports cache hit");
        }
        result
    })
}

/// Cache partial module exports (type definitions only)
/// Called after register_definitions but before process_imports_and_assignments
pub fn cache_partial_module_exports(path: &Path, exports: Value) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Caching partial module exports");
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| {
        cache.borrow_mut().insert(key, exports);
    });
}

/// Clear partial module exports for a path (after full loading completes)
pub fn clear_partial_module_exports(path: &Path) {
    let key = normalize_path_key(path);
    trace!(path = ?key, "Clearing partial module exports");
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| {
        cache.borrow_mut().remove(&key);
    });
}

/// Record a module visit (called at entry of load_and_merge_module).
/// Tracks visit count and max depth.
pub fn record_module_visit(path: &Path, depth: usize) {
    if !loader_stats_enabled() {
        return;
    }
    LOADER_STATS.with(|stats| {
        let mut s = stats.borrow_mut();
        *s.visit_counts.entry(path.to_path_buf()).or_insert(0) += 1;
        if depth > s.max_depth_seen {
            s.max_depth_seen = depth;
        }
    });
}

/// Record eval time for a module (called after successful evaluation, not for cache hits).
pub fn record_module_eval_time(path: &Path, elapsed_us: u128) {
    if !loader_stats_enabled() {
        return;
    }
    LOADER_STATS.with(|stats| {
        let mut s = stats.borrow_mut();
        *s.eval_time_us.entry(path.to_path_buf()).or_insert(0) += elapsed_us;
        s.total_loaded += 1;
    });
}

/// Record a sibling preload evaluation.
pub fn record_sibling_preload() {
    if !loader_stats_enabled() {
        return;
    }
    LOADER_STATS.with(|stats| {
        stats.borrow_mut().sibling_preloads += 1;
    });
}

/// Print aggregated loader summary to stderr, then clear stats.
/// Called from clear_module_cache() when SIMPLE_LOADER_TRACE=1.
pub fn print_loader_summary() {
    if !loader_stats_enabled() {
        return;
    }
    LOADER_STATS.with(|stats| {
        let s = stats.borrow();
        if s.visit_counts.is_empty() {
            return;
        }

        eprintln!("[loader-summary] === Module Loader Summary ===");
        eprintln!("[loader-summary] Total unique modules loaded: {}", s.total_loaded);
        eprintln!(
            "[loader-summary] Total module visits (incl. cache): {}",
            s.visit_counts.values().sum::<u32>()
        );
        eprintln!("[loader-summary] Max recursion depth: {}", s.max_depth_seen);
        eprintln!("[loader-summary] Sibling preload evaluations: {}", s.sibling_preloads);

        // Top 10 most-visited modules
        let mut by_visits: Vec<_> = s.visit_counts.iter().collect();
        by_visits.sort_by(|a, b| b.1.cmp(a.1));
        eprintln!("[loader-summary] Top visited modules:");
        for (path, count) in by_visits.iter().take(10) {
            // Show short path: strip common prefix up to src/
            let display = path.to_string_lossy();
            let short = display.find("src/").map(|i| &display[i..]).unwrap_or(&display);
            eprintln!("[loader-summary]   {:>4}x  {}", count, short);
        }

        // Top 10 slowest modules
        let mut by_time: Vec<_> = s.eval_time_us.iter().collect();
        by_time.sort_by(|a, b| b.1.cmp(a.1));
        eprintln!("[loader-summary] Slowest modules:");
        for (path, time_us) in by_time.iter().take(10) {
            let display = path.to_string_lossy();
            let short = display.find("src/").map(|i| &display[i..]).unwrap_or(&display);
            eprintln!("[loader-summary]   {:>6}us  {}", time_us, short);
        }
        eprintln!("[loader-summary] ===========================");
    });
    // Clear stats after printing
    LOADER_STATS.with(|stats| {
        *stats.borrow_mut() = LoaderStats::default();
    });
}

/// Recursively filter Function values from a Value to prevent exponential memory growth.
/// Instead of removing functions entirely (which breaks transitive imports — BUG-002),
/// we preserve the function but strip its inner `captured_env` to prevent O(N*M)
/// cascading memory growth when modules import each other in chains.
/// This way, module B's exported functions retain references to C's imported functions,
/// so when A calls B's function that calls C's function, the lookup succeeds.
pub fn filter_functions_from_value(value: &Value) -> Value {
    match value {
        Value::Function { name, def, .. } => {
            // Preserve the function but with an empty captured_env to prevent
            // exponential memory growth from nested captured environments.
            // The function definition (Arc<FunctionDef>) is cheap to clone (refcount bump).
            Value::Function {
                name: name.clone(),
                def: def.clone(),
                captured_env: Env::shared_empty(),
            }
        }
        Value::Dict(dict) => {
            // Recursively process dict values (imported modules) — preserve functions inside.
            //
            // Memoised per SOURCE dict: an imported module's export dict is the
            // same `Arc` in every importer's env, and this filter is a pure
            // function of its contents, so rebuilding a fresh ~1000-entry map
            // (new keys, new Function values) once per importing module was
            // O(importers x exports) retained memory encoding nothing. The
            // cache holds a clone of the source `Arc` alongside the result, so
            // a pointer can never be recycled while its entry is live. Cleared
            // with every other loader cache in `clear_module_cache`.
            let key = Arc::as_ptr(dict) as usize;
            if let Some(hit) = FILTERED_DICT_CACHE.with(|c| {
                c.borrow().get(&key).and_then(|(src, out)| Arc::ptr_eq(src, dict).then(|| Arc::clone(out)))
            }) {
                crate::perf_counters::bump(&crate::perf_counters::FILTERED_DICT_HITS, 1);
                return Value::Dict(hit);
            }
            crate::perf_counters::bump(&crate::perf_counters::FILTERED_DICT_BUILDS, 1);
            let filtered: Arc<HashMap<String, Value>> = Arc::new(
                dict.iter()
                    .map(|(k, v)| (k.clone(), filter_functions_from_value(v)))
                    .collect(),
            );
            FILTERED_DICT_CACHE.with(|c| {
                c.borrow_mut().insert(key, (Arc::clone(dict), Arc::clone(&filtered)));
            });
            Value::Dict(filtered)
        }
        // For all other values, clone them as-is
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::{reserve_module_load, reset_total_modules, total_modules_loaded};

    #[test]
    fn module_load_reservation_commits_only_successful_loads() {
        reset_total_modules();
        {
            let _reservation = reserve_module_load(1).unwrap();
            assert_eq!(total_modules_loaded(), 1);
        }
        assert_eq!(total_modules_loaded(), 0);

        reserve_module_load(1).unwrap().commit();
        assert_eq!(total_modules_loaded(), 1);
        assert!(matches!(reserve_module_load(1), Err(2)));
        assert_eq!(total_modules_loaded(), 1);
        reset_total_modules();

        let unlimited = reserve_module_load(0).unwrap();
        assert_eq!(total_modules_loaded(), 1);
        drop(unlimited);
        assert_eq!(total_modules_loaded(), 0);
    }
}
