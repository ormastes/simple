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

use crate::bounded_cache::{limit_from_env, BoundedCache, CacheStats};
use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef};

// ---------------------------------------------------------------------------
// Retention bounds for the loader memos.
//
// The four bounded caches are memos of PURE, recomputable lookups: an evicted
// entry is refilled byte-identically by its owner on the next miss. That is
// what makes them the ones safe to bound.
//
// NOT bounded, deliberately:
//   * the module-DEFINITION caches (`MODULE_EXPORTS_CACHE` and friends) are not
//     memos of a pure function -- a module's exports are the result of RUNNING
//     its top level, so a refill re-executes side effects;
//   * `MODULE_EXPORT_OWNERS` and `FUNCTION_MODULE_OWNER` are side tables keyed
//     by a raw address that they do NOT themselves retain. Their keys are
//     unique only because a *different* cache holds the allocation, and unlike
//     `FILTERED_DICT_CACHE` below they re-check nothing on a hit.
// See `doc/05_design/compiler/interpreter/bounded_seed_interpreter_caches_2026-09-12.md`
// and `doc/08_tracking/bug/pointer_keyed_caches_cannot_be_bounded_2026-09-12.md`.
//
// The defaults are well above the high-water of a full
// `src/app/mcp/main.spl --help` run, so a default-configured process evicts
// nothing and behaves exactly as it did before the bound existed. They are a
// ceiling for a process that walks a much larger import graph.
// ---------------------------------------------------------------------------

/// Retention limit for `PARSED_SOURCE_CACHE`; `SIMPLE_PARSED_SOURCE_CACHE_MAX`
/// overrides, `0` means unbounded.
pub const PARSED_SOURCE_CACHE_MAX_DEFAULT: usize = 4096;
/// Retention limit for `PROBE_SOURCE_CACHE`; `SIMPLE_PROBE_SOURCE_CACHE_MAX`
/// overrides, `0` means unbounded.
pub const PROBE_SOURCE_CACHE_MAX_DEFAULT: usize = 4096;
/// Retention limit for `PATH_KEY_CACHE`; `SIMPLE_PATH_KEY_CACHE_MAX`
/// overrides, `0` means unbounded.
pub const PATH_KEY_CACHE_MAX_DEFAULT: usize = 16384;
/// Retention limit for `FILTERED_DICT_CACHE`; `SIMPLE_FILTERED_DICT_CACHE_MAX`
/// overrides, `0` means unbounded. Lower than the others because each entry is
/// a pair of whole export maps, not a path.
pub const FILTERED_DICT_CACHE_MAX_DEFAULT: usize = 2048;

fn parsed_source_cache_max() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| limit_from_env("SIMPLE_PARSED_SOURCE_CACHE_MAX", PARSED_SOURCE_CACHE_MAX_DEFAULT))
}

fn probe_source_cache_max() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| limit_from_env("SIMPLE_PROBE_SOURCE_CACHE_MAX", PROBE_SOURCE_CACHE_MAX_DEFAULT))
}

fn path_key_cache_max() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| limit_from_env("SIMPLE_PATH_KEY_CACHE_MAX", PATH_KEY_CACHE_MAX_DEFAULT))
}

fn filtered_dict_cache_max() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| limit_from_env("SIMPLE_FILTERED_DICT_CACHE_MAX", FILTERED_DICT_CACHE_MAX_DEFAULT))
}

/// Still borrowed when either map of the memo is referenced outside the cache.
/// Both arms matter and both are the right call: the source dict is a live
/// module export map, and the filtered dict is handed out as `Value::Dict` and
/// can outlive the cache entry in an importer's env. In both cases the
/// allocation survives eviction anyway, so evicting would free nothing and only
/// cost a rebuild.
fn filtered_dict_pinned(value: &(Arc<HashMap<String, Value>>, Arc<HashMap<String, Value>>)) -> bool {
    Arc::strong_count(&value.0) > 1 || Arc::strong_count(&value.1) > 1
}

/// Mirror one cache's per-insert stats delta into the process counters.
fn mirror_stats(
    delta: CacheStats,
    evictions: &std::sync::atomic::AtomicU64,
    pinned_skips: &std::sync::atomic::AtomicU64,
    retained_max: &std::sync::atomic::AtomicU64,
) {
    if delta.evictions > 0 {
        crate::perf_counters::bump(evictions, delta.evictions);
    }
    if delta.pinned_skips > 0 {
        crate::perf_counters::bump(pinned_skips, delta.pinned_skips);
    }
    crate::perf_counters::set_max(retained_max, delta.retained_max as u64);
}

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

/// Still borrowed when the caller's `Option<Arc<String>>` clone is alive.
fn probe_source_pinned(value: &Option<Arc<String>>) -> bool {
    match value {
        Some(source) => Arc::strong_count(source) > 1,
        None => false,
    }
}

thread_local! {
    /// Process-local memo for import-resolution probe source. Retention-bounded:
    /// the value is the WHOLE probe file, so an unbounded one retains every
    /// candidate a resolver ever looked at.
    static PROBE_SOURCE_CACHE: RefCell<BoundedCache<(PathBuf, u64), Option<Arc<String>>>> =
        RefCell::new(BoundedCache::new(probe_source_cache_max(), probe_source_pinned));
}

pub fn probe_source_cached(path: &Path, max_check_bytes: u64) -> Option<Arc<String>> {
    let key = (path.to_path_buf(), max_check_bytes);
    if let Some(hit) = PROBE_SOURCE_CACHE.with(|cache| cache.borrow().get(&key)) {
        crate::perf_counters::bump(&crate::perf_counters::PROBE_SOURCE_HITS, 1);
        return hit;
    }
    crate::perf_counters::bump(&crate::perf_counters::PROBE_SOURCE_READS, 1);
    let value = match std::fs::metadata(path) {
        Ok(metadata) if metadata.len() > max_check_bytes => None,
        _ => crate::read_trace::rts(file!(), line!(), path).ok().map(Arc::new),
    };
    // `value` is alive across the insert, so the entry just filled is pinned and
    // cannot be chosen as its own victim.
    let delta = PROBE_SOURCE_CACHE.with(|cache| cache.borrow_mut().insert(key, value.clone()));
    mirror_stats(
        delta,
        &crate::perf_counters::PROBE_SOURCE_EVICTIONS,
        &crate::perf_counters::PROBE_SOURCE_PINNED_SKIPS,
        &crate::perf_counters::PROBE_SOURCE_RETAINED_MAX,
    );
    value
}

pub fn clear_probe_source_cache() {
    PROBE_SOURCE_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Test-only retention control: cargo tests cannot use the env overrides,
/// which latch in a process-global `OnceLock` shared by every parallel test.
pub fn probe_source_cache_set_limit(limit: usize) {
    PROBE_SOURCE_CACHE.with(|cache| cache.borrow_mut().set_limit(limit));
}

pub fn probe_source_cache_stats() -> CacheStats {
    PROBE_SOURCE_CACHE.with(|cache| cache.borrow().stats())
}

pub fn probe_source_cache_len() -> usize {
    PROBE_SOURCE_CACHE.with(|cache| cache.borrow().len())
}

thread_local! {
    /// Cross-lane source+AST cache: one read and one parse per PHYSICAL file.
    ///
    /// The HIR lowerer and the interpreter each walked the same import graph
    /// with a private cache that the other could not see, so every file both
    /// lanes reach was read and fully re-parsed twice. Measured on
    /// `src/app/mcp/main.spl --help` (`SIMPLE_READ_TRACE=1`, realpaths):
    /// lowerer 117 physical files, interpreter 128, intersection 117 --
    /// 1,265,979 bytes parsed a second time for nothing.
    ///
    /// Keyed by `normalize_path_key`, the same canonical key the exports cache
    /// uses, so alias spellings of one file (`src/std` -> `lib`,
    /// relative vs absolute) share one entry.
    ///
    /// INVALIDATION: none, per process -- which is exactly the policy BOTH
    /// lanes already had (`IMPORTED_MODULE_AST` and `MODULE_EXPORTS_CACHE` are
    /// both plain per-process memos with no stamp), so the unified cache is no
    /// weaker than either. A `src/lib/**` edit is still picked up by the next
    /// run; nothing is baked into the binary.
    /// RETENTION: bounded (`PARSED_SOURCE_CACHE_MAX_DEFAULT`,
    /// `SIMPLE_PARSED_SOURCE_CACHE_MAX`). This is the memory-dominant loader
    /// cache -- every entry holds a whole source string AND its parsed AST --
    /// so it is the one an unbounded process grows on. An entry still borrowed
    /// by either lane is never evicted; see `shared_source_pinned`.
    static PARSED_SOURCE_CACHE: RefCell<BoundedCache<PathBuf, SharedSource>> =
        RefCell::new(BoundedCache::new(parsed_source_cache_max(), shared_source_pinned));
}

/// Still borrowed when ANY payload `Arc` of the entry is shared outside the
/// cache. Both arms matter: the interpreter holds the `source` while it strips
/// `@cfg` globals, the HIR lowerer holds the `ast` while it registers imported
/// symbols, and the error text is handed out on the failure paths. Checking
/// only one of them would let a live entry be freed.
fn shared_source_pinned(value: &SharedSource) -> bool {
    match value {
        SharedSource::Parsed { source, ast } => {
            Arc::strong_count(source) > 1
                || match ast {
                    Ok(parsed) => Arc::strong_count(parsed) > 1,
                    Err(message) => Arc::strong_count(message) > 1,
                }
        }
        SharedSource::ReadError(message) => Arc::strong_count(message) > 1,
    }
}

/// One physical file, read once and parsed once, borrowed by both lanes.
#[derive(Clone)]
pub enum SharedSource {
    /// Read succeeded. `source` is CRLF-normalized.
    Parsed {
        source: Arc<String>,
        /// The parse of exactly those bytes, or the parse error's `Display` text.
        /// Keeping the TEXT (the error is not `Clone`) is what lets every lane
        /// rebuild its own diagnostic byte-identically from a shared entry.
        ast: Result<Arc<simple_parser::ast::Module>, Arc<str>>,
    },
    /// Read failed. Holds the `std::io::Error`'s `Display` text rather than the
    /// error (which is not `Clone`), so each lane rebuilds its own message
    /// byte-identically instead of inventing a new one.
    ReadError(Arc<str>),
}

impl SharedSource {
    /// The parsed AST, or `None` when unreadable or unparseable. This is what
    /// the HIR lowerer consumes; it treats both failures the same way.
    pub fn ast(&self) -> Option<Arc<simple_parser::ast::Module>> {
        match self {
            SharedSource::Parsed { ast, .. } => ast.clone().ok(),
            SharedSource::ReadError(_) => None,
        }
    }
}

/// Look up a file in the cross-lane cache WITHOUT filling it.
///
/// Split from `shared_source` so a caller can attribute a miss to its own lane
/// (the lowerer's `IMPORT_AST_PARSES` counts the parses that lane caused).
pub fn shared_source_lookup(path: &Path) -> Option<SharedSource> {
    let key = normalize_path_key(path);
    PARSED_SOURCE_CACHE.with(|cache| cache.borrow().get(&key))
}

/// Read + parse `path` once per process, shared by every lane. See
/// `PARSED_SOURCE_CACHE`.
pub fn shared_source(path: &Path) -> SharedSource {
    let key = normalize_path_key(path);
    if let Some(hit) = PARSED_SOURCE_CACHE.with(|cache| cache.borrow().get(&key)) {
        crate::perf_counters::bump(&crate::perf_counters::SHARED_SRC_HITS, 1);
        return hit;
    }
    // The borrow is dropped before the read/parse: filling is not re-entrant
    // today, and holding it across arbitrary work is how a RefCell panic gets
    // introduced later.
    crate::perf_counters::bump(&crate::perf_counters::SHARED_SRC_PARSES, 1);
    let entry = match crate::read_trace::rts(file!(), line!(), path) {
        Ok(mut source) => {
            // Normalize CRLF -> LF so indentation-sensitive parsing works on
            // all platforms. Both lanes did this before caching; do it once.
            if source.contains('\r') {
                source = source.replace('\r', "");
            }
            let ast = simple_parser::Parser::new(&source)
                .parse()
                .map(Arc::new)
                .map_err(|e| Arc::from(e.to_string().as_str()));
            SharedSource::Parsed {
                source: Arc::new(source),
                ast,
            }
        }
        Err(e) => SharedSource::ReadError(Arc::from(e.to_string().as_str())),
    };
    // `entry` is alive across the insert, so the entry just filled is pinned
    // and cannot be selected as its own eviction victim.
    let delta = PARSED_SOURCE_CACHE.with(|cache| cache.borrow_mut().insert(key, entry.clone()));
    mirror_stats(
        delta,
        &crate::perf_counters::PARSED_SOURCE_EVICTIONS,
        &crate::perf_counters::PARSED_SOURCE_PINNED_SKIPS,
        &crate::perf_counters::PARSED_SOURCE_RETAINED_MAX,
    );
    entry
}

/// Drop the cross-lane source+AST cache.
pub fn clear_parsed_source_cache() {
    PARSED_SOURCE_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Entry count -- for tests that assert "one parse per physical file" without
/// reading process-global perf counters (cargo runs tests in parallel).
pub fn parsed_source_cache_len() -> usize {
    PARSED_SOURCE_CACHE.with(|cache| cache.borrow().len())
}

/// Test-only retention control; see `probe_source_cache_set_limit`.
pub fn parsed_source_cache_set_limit(limit: usize) {
    PARSED_SOURCE_CACHE.with(|cache| cache.borrow_mut().set_limit(limit));
}

pub fn parsed_source_cache_stats() -> CacheStats {
    PARSED_SOURCE_CACHE.with(|cache| cache.borrow().stats())
}

/// Print a one-line breakdown of every never-evicted loader cache.
pub fn report_cache_sizes(tag: &str) {
    let exports = MODULE_EXPORTS_CACHE.with(|c| c.borrow().len());
    let (cls_m, cls_e) =
        MODULE_CLASSES_CACHE.with(|c| (c.borrow().len(), c.borrow().values().map(|m| m.len()).sum::<usize>()));
    let (fn_m, fn_e) =
        MODULE_FUNCTIONS_CACHE.with(|c| (c.borrow().len(), c.borrow().values().map(|m| m.len()).sum::<usize>()));
    let (en_m, en_e) =
        MODULE_ENUMS_CACHE.with(|c| (c.borrow().len(), c.borrow().values().map(|m| m.len()).sum::<usize>()));
    let partial = PARTIAL_MODULE_EXPORTS_CACHE.with(|c| c.borrow().len());
    let (env_m, env_e) =
        MODULE_ENV_BY_OWNER.with(|c| (c.borrow().len(), c.borrow().values().map(|e| e.len()).sum::<usize>()));
    let (ovl_k, ovl_e) =
        FUNCTION_OVERLOADS.with(|c| (c.borrow().len(), c.borrow().values().map(|v| v.len()).sum::<usize>()));
    let parsed = parsed_source_cache_len();
    let parsed_stats = parsed_source_cache_stats();
    let probe = probe_source_cache_len();
    let probe_stats = probe_source_cache_stats();
    let path_key = path_key_cache_len();
    let path_key_stats = path_key_cache_stats();
    let filtered = FILTERED_DICT_CACHE.with(|c| c.borrow().len());
    let filtered_stats = FILTERED_DICT_CACHE.with(|c| c.borrow().stats());
    eprintln!(
        "[cache-size] {} rss_mb={} exports={} classes={}m/{}e functions={}m/{}e enums={}m/{}e partial={} env_by_owner={}m/{}e overloads={}k/{}e parsed_src={}/{} (ev={} skip={} max={}) probe_src={}/{} (ev={} skip={} max={}) path_key={}/{} (ev={} skip={} max={}) filtered_dict={}/{} (ev={} skip={} max={})",
        tag,
        rss_kb() / 1024,
        exports,
        cls_m, cls_e,
        fn_m, fn_e,
        en_m, en_e,
        partial,
        env_m, env_e,
        ovl_k, ovl_e,
        parsed, parsed_source_cache_max(),
        parsed_stats.evictions, parsed_stats.pinned_skips, parsed_stats.retained_max,
        probe, probe_source_cache_max(),
        probe_stats.evictions, probe_stats.pinned_skips, probe_stats.retained_max,
        path_key, path_key_cache_max(),
        path_key_stats.evictions, path_key_stats.pinned_skips, path_key_stats.retained_max,
        filtered, filtered_dict_cache_max(),
        filtered_stats.evictions, filtered_stats.pinned_skips, filtered_stats.retained_max,
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
    /// RETENTION: bounded (`PATH_KEY_CACHE_MAX_DEFAULT`,
    /// `SIMPLE_PATH_KEY_CACHE_MAX`). A pure memo of `canonicalize`, handed out
    /// by value, so nothing can borrow an entry and the pin predicate is
    /// constant-false.
    static PATH_KEY_CACHE: RefCell<BoundedCache<PathBuf, PathBuf>> =
        RefCell::new(BoundedCache::new(path_key_cache_max(), |_| false));
    /// `filter_functions_from_value` memo: source dict ptr -> (source Arc, filtered Arc).
    ///
    /// RETENTION: bounded (`FILTERED_DICT_CACHE_MAX_DEFAULT`,
    /// `SIMPLE_FILTERED_DICT_CACHE_MAX`). Evicting is safe DESPITE the raw
    /// address key: the lookup below re-checks `Arc::ptr_eq(src, dict)`, so a
    /// recycled address is a miss and a rebuild, never a false hit. An entry
    /// whose source or filtered map is still referenced elsewhere is pinned --
    /// which is also the case where eviction would free nothing, since the
    /// allocation stays alive through the other reference.
    static FILTERED_DICT_CACHE: RefCell<BoundedCache<usize, (Arc<HashMap<String, Value>>, Arc<HashMap<String, Value>>)>> =
        RefCell::new(BoundedCache::new(filtered_dict_cache_max(), filtered_dict_pinned));
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
    clear_probe_source_cache();
    clear_parsed_source_cache();
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
    // And the module-resolver numbered-directory memos
    crate::module_resolver::clear_numbered_dir_cache();
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
    // Source-derived probe/AST memos must not survive a selective boundary:
    // test and IDE callers may edit, delete, or recreate files between runs.
    clear_probe_source_cache();
    clear_parsed_source_cache();
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
    if let Some(cached) = PATH_KEY_CACHE.with(|cache| cache.borrow().get(&path_buf)) {
        return cached;
    }

    let result = normalize_path_key_uncached(path);

    let delta = PATH_KEY_CACHE.with(|cache| cache.borrow_mut().insert(path_buf, result.clone()));
    mirror_stats(
        delta,
        &crate::perf_counters::PATH_KEY_EVICTIONS,
        &crate::perf_counters::PATH_KEY_PINNED_SKIPS,
        &crate::perf_counters::PATH_KEY_RETAINED_MAX,
    );

    result
}

/// Test-only retention control; see `probe_source_cache_set_limit`.
pub fn path_key_cache_set_limit(limit: usize) {
    PATH_KEY_CACHE.with(|cache| cache.borrow_mut().set_limit(limit));
}

pub fn path_key_cache_stats() -> CacheStats {
    PATH_KEY_CACHE.with(|cache| cache.borrow().stats())
}

pub fn path_key_cache_len() -> usize {
    PATH_KEY_CACHE.with(|cache| cache.borrow().len())
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
                c.borrow()
                    .get(&key)
                    .and_then(|(src, out)| Arc::ptr_eq(&src, dict).then(|| Arc::clone(&out)))
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
            let delta = FILTERED_DICT_CACHE
                .with(|c| c.borrow_mut().insert(key, (Arc::clone(dict), Arc::clone(&filtered))));
            mirror_stats(
                delta,
                &crate::perf_counters::FILTERED_DICT_EVICTIONS,
                &crate::perf_counters::FILTERED_DICT_PINNED_SKIPS,
                &crate::perf_counters::FILTERED_DICT_RETAINED_MAX,
            );
            Value::Dict(filtered)
        }
        // For all other values, clone them as-is
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        clear_probe_source_cache, probe_source_cached, reserve_module_load, reset_total_modules, total_modules_loaded,
    };
    use super::{
        clear_parsed_source_cache, normalize_path_key, parsed_source_cache_len, parsed_source_cache_set_limit,
        parsed_source_cache_stats, path_key_cache_len, path_key_cache_set_limit, path_key_cache_stats,
        probe_source_cache_len, probe_source_cache_set_limit, probe_source_cache_stats, shared_source,
        shared_source_lookup, SharedSource,
    };

    /// Each cargo test runs on its own thread, so these thread-local caches are
    /// per-test; a unique directory per test additionally keeps the `PathBuf`
    /// keys from colliding.
    fn scratch_dir(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("l4-bounded-{}-{}", tag, std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create scratch dir");
        dir
    }

    fn write_module(dir: &std::path::Path, i: usize) -> std::path::PathBuf {
        let path = dir.join(format!("m{i}.spl"));
        std::fs::write(&path, format!("pub fn m{i}(): {i}\n")).expect("write module");
        path
    }

    fn body_of(entry: &SharedSource) -> String {
        match entry {
            SharedSource::Parsed { source, .. } => (**source).clone(),
            SharedSource::ReadError(e) => panic!("unexpected read error: {e}"),
        }
    }

    #[test]
    fn parsed_source_cache_evicts_past_its_bound_and_counts_it() {
        clear_parsed_source_cache();
        parsed_source_cache_set_limit(2);
        let dir = scratch_dir("parsed-evict");
        let paths: Vec<_> = (0..8).map(|i| write_module(&dir, i)).collect();

        for path in &paths {
            // The returned entry is dropped before the next fill, so nothing is
            // pinned and the bound can always make progress.
            let _ = shared_source(path);
        }

        assert!(
            parsed_source_cache_len() <= 2,
            "cache held {} entries at limit 2",
            parsed_source_cache_len()
        );
        let stats = parsed_source_cache_stats();
        assert_eq!(stats.evictions, 6, "8 fills at limit 2 must drop 6");
        assert_eq!(stats.pinned_skips, 0, "nothing was borrowed, so nothing blocked a release");
        assert!(stats.retained_max >= 2);

        // Byte-identical after eviction + reload: the entries dropped above are
        // refilled from disk and must match a fresh parse exactly.
        for (i, path) in paths.iter().enumerate() {
            let reloaded = shared_source(path);
            assert_eq!(body_of(&reloaded), format!("pub fn m{i}(): {i}\n"));
            assert!(reloaded.ast().is_some(), "reloaded entry must still parse");
        }

        clear_parsed_source_cache();
        parsed_source_cache_set_limit(super::parsed_source_cache_max());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn parsed_source_cache_never_evicts_a_borrowed_entry() {
        clear_parsed_source_cache();
        let dir = scratch_dir("parsed-pin");
        let held_path = write_module(&dir, 0);
        let second = write_module(&dir, 1);
        let third = write_module(&dir, 2);

        // Hold the first entry the way both lanes hold a `SharedSource` clone.
        let held = shared_source(&held_path);
        parsed_source_cache_set_limit(1);

        let _ = shared_source(&second);
        let _ = shared_source(&third);

        let stats = parsed_source_cache_stats();
        assert!(
            stats.pinned_skips >= 1,
            "a pass that could free nothing must be counted, got {stats:?}"
        );
        assert!(
            shared_source_lookup(&held_path).is_some(),
            "the borrowed entry was evicted while still borrowed"
        );
        assert_eq!(
            body_of(&shared_source_lookup(&held_path).expect("retained")),
            body_of(&held),
            "the retained entry must still be the same bytes, not a dangling refill"
        );

        // Release it: the bound can make progress again.
        let before = parsed_source_cache_stats().evictions;
        drop(held);
        let fourth = write_module(&dir, 3);
        let _ = shared_source(&fourth);
        assert!(
            parsed_source_cache_stats().evictions > before,
            "releasing the borrow must let enforcement evict what it could not before"
        );

        clear_parsed_source_cache();
        parsed_source_cache_set_limit(super::parsed_source_cache_max());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn probe_source_cache_evicts_past_its_bound_and_rereads_identically() {
        clear_probe_source_cache();
        probe_source_cache_set_limit(2);
        let dir = scratch_dir("probe-evict");
        let paths: Vec<_> = (0..6).map(|i| write_module(&dir, i)).collect();

        for path in &paths {
            let _ = probe_source_cached(path, u64::MAX);
        }
        assert!(probe_source_cache_len() <= 2);
        assert_eq!(probe_source_cache_stats().evictions, 4);

        for (i, path) in paths.iter().enumerate() {
            let source = probe_source_cached(path, u64::MAX).expect("reread after eviction");
            assert_eq!(source.as_str(), format!("pub fn m{i}(): {i}\n"));
        }

        clear_probe_source_cache();
        probe_source_cache_set_limit(super::probe_source_cache_max());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn probe_source_cache_never_evicts_a_borrowed_entry() {
        clear_probe_source_cache();
        let dir = scratch_dir("probe-pin");
        let held_path = write_module(&dir, 0);
        let held = probe_source_cached(&held_path, u64::MAX).expect("first read");
        probe_source_cache_set_limit(1);

        for i in 1..4 {
            let _ = probe_source_cached(&write_module(&dir, i), u64::MAX);
        }

        assert!(probe_source_cache_stats().pinned_skips >= 1);
        let still_there = probe_source_cached(&held_path, u64::MAX).expect("retained");
        assert!(
            std::sync::Arc::ptr_eq(&held, &still_there),
            "a borrowed probe source must be the SAME allocation, not a silent re-read"
        );

        clear_probe_source_cache();
        probe_source_cache_set_limit(super::probe_source_cache_max());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn filtered_dict_cache_evicts_past_its_bound_and_rebuilds_identically() {
        use super::{filter_functions_from_value, FILTERED_DICT_CACHE};
        use crate::value::Value;
        use std::collections::HashMap;
        use std::sync::Arc;

        FILTERED_DICT_CACHE.with(|c| {
            c.borrow_mut().clear();
            c.borrow_mut().set_limit(2);
        });

        // Every source dict is dropped at the end of its iteration -- nothing
        // outside the cache holds it -- so the entries are unpinned and the
        // bound can make progress. Only plain data is carried out of the loop;
        // keeping the source `Arc`s would pin every entry and the assertions
        // below would then be measuring nothing.
        let expect_body = |i: usize| (format!("k{i}"), i as i64);
        for i in 0..8usize {
            let mut map = HashMap::new();
            let (k, v) = expect_body(i);
            map.insert(k, Value::Int(v));
            let dict = Arc::new(map);
            let filtered = filter_functions_from_value(&Value::Dict(Arc::clone(&dict)));
            let Value::Dict(out) = &filtered else {
                panic!("filter must return a dict");
            };
            assert_eq!(out.len(), 1);
        }

        let stats = FILTERED_DICT_CACHE.with(|c| c.borrow().stats());
        assert!(
            FILTERED_DICT_CACHE.with(|c| c.borrow().len()) <= 2,
            "cache held {} entries at limit 2",
            FILTERED_DICT_CACHE.with(|c| c.borrow().len())
        );
        assert_eq!(stats.evictions, 6, "8 fills at limit 2 with nothing pinned must drop 6");
        assert_eq!(stats.pinned_skips, 0, "nothing was borrowed, so nothing blocked a release");

        // Rebuild after eviction: the filtered map must be identical to the
        // first build. This is also the case the raw-address key is most
        // exposed to -- the evicted allocations were freed, so a new dict may
        // land on an address a stale entry still names, and the `Arc::ptr_eq`
        // re-check in `filter_functions_from_value` is what makes that a miss
        // and a rebuild instead of a false hit.
        for i in 0..8usize {
            let mut map = HashMap::new();
            let (k, v) = expect_body(i);
            map.insert(k.clone(), Value::Int(v));
            let dict = Arc::new(map);
            let again = filter_functions_from_value(&Value::Dict(dict));
            let Value::Dict(out) = &again else {
                panic!("filter must return a dict");
            };
            assert_eq!(out.len(), 1, "rebuilt map must have the same entries");
            assert!(
                matches!(out.get(&k), Some(Value::Int(x)) if *x == v),
                "rebuilt value for {k} must be {v}, got {:?}",
                out.get(&k)
            );
        }

        FILTERED_DICT_CACHE.with(|c| {
            c.borrow_mut().clear();
            c.borrow_mut().set_limit(super::filtered_dict_cache_max());
        });
    }

    #[test]
    fn path_key_cache_evicts_past_its_bound_and_recomputes_identically() {
        path_key_cache_set_limit(0);
        let dir = scratch_dir("path-key");
        let paths: Vec<_> = (0..8).map(|i| write_module(&dir, i)).collect();
        let expected: Vec<_> = paths.iter().map(|p| normalize_path_key(p)).collect();

        let before = path_key_cache_len();
        path_key_cache_set_limit(2);
        assert!(path_key_cache_len() <= 2, "set_limit must enforce immediately");
        assert!(
            path_key_cache_stats().evictions >= (before.saturating_sub(2)) as u64,
            "shrinking the limit must evict the excess"
        );

        for (path, want) in paths.iter().zip(expected.iter()) {
            assert_eq!(&normalize_path_key(path), want, "recomputed key must be identical");
        }
        assert_eq!(
            path_key_cache_stats().pinned_skips,
            0,
            "path keys are handed out by value and can never be pinned"
        );

        path_key_cache_set_limit(super::path_key_cache_max());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn probe_source_memo_respects_the_size_limit() {
        clear_probe_source_cache();
        let path = std::env::temp_dir().join(format!("probe-source-memo-{}", std::process::id()));
        std::fs::write(&path, "pub fn probe(): 1\n").expect("write probe source");

        assert!(probe_source_cached(&path, 1).is_none());
        let source = probe_source_cached(&path, u64::MAX).expect("larger limit reads source");
        let cached = probe_source_cached(&path, u64::MAX).expect("same limit hits memo");
        assert_eq!(source.as_str(), "pub fn probe(): 1\n");
        assert!(std::sync::Arc::ptr_eq(&source, &cached));

        std::fs::write(&path, "pub fn changed(): 2\n").expect("mutate probe source");
        super::clear_module_cache_selective();
        assert_eq!(
            probe_source_cached(&path, u64::MAX)
                .expect("edited source is visible")
                .as_str(),
            "pub fn changed(): 2\n"
        );

        std::fs::remove_file(&path).expect("delete probe source");
        super::clear_module_cache_selective();
        assert!(probe_source_cached(&path, u64::MAX).is_none());

        std::fs::write(&path, "pub fn recreated(): 3\n").expect("recreate probe source");
        super::clear_module_cache_selective();
        assert_eq!(
            probe_source_cached(&path, u64::MAX)
                .expect("recreated source is visible")
                .as_str(),
            "pub fn recreated(): 3\n"
        );

        let _ = std::fs::remove_file(path);
        clear_probe_source_cache();
    }

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
