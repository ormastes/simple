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
use crate::value::{DictMap, Env, ModuleTable, TableView, Value};
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
/// Retention limit for `PARSED_SOURCE_CACHE` on native-compile worker threads.
/// `SIMPLE_PARSED_SOURCE_CACHE_MAX` overrides when set; the default is modest
/// because one whole-closure compile can walk thousands of modules inside a
/// single worker, and every entry retains a whole source string AND its parsed
/// AST. Entries are pure recomputable memos, so eviction only costs a re-read
/// and re-parse on a later miss in that worker.
pub const PARSED_SOURCE_CACHE_COMPILE_MAX_DEFAULT: usize = 256;
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

/// Limit a native-compile worker should set on its thread-local
/// `PARSED_SOURCE_CACHE`: the env override when present, else the modest
/// compile-phase default. Read on the worker thread itself (the cache is
/// thread-local, so setting it anywhere else has no effect on the worker).
pub fn parsed_source_cache_compile_max() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| {
        limit_from_env("SIMPLE_PARSED_SOURCE_CACHE_MAX", PARSED_SOURCE_CACHE_COMPILE_MAX_DEFAULT)
    })
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
fn filtered_dict_pinned(value: &(Arc<DictMap>, Arc<DictMap>)) -> bool {
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
    /// Cross-lane source+AST cache: one read and parse per physical file and OS.
    ///
    /// The HIR lowerer and the interpreter each walked the same import graph
    /// with a private cache that the other could not see, so every file both
    /// lanes reach was read and fully re-parsed twice. Measured on
    /// `src/app/mcp/main.spl --help` (`SIMPLE_READ_TRACE=1`, realpaths):
    /// lowerer 117 physical files, interpreter 128, intersection 117 --
    /// 1,265,979 bytes parsed a second time for nothing.
    ///
    /// Keyed by OS plus `normalize_path_key`, the canonical key the exports cache
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
    static PARSED_SOURCE_CACHE: RefCell<BoundedCache<(PathBuf, crate::pipeline::cfg_strip::CfgTarget), SharedSource>> =
        RefCell::new(BoundedCache::new(parsed_source_cache_max(), shared_source_pinned));

    /// Source text of entries whose AST was handed to the interpreter BY
    /// OWNERSHIP (`take_shared_ast`). Keeping the exact bytes means a later
    /// `shared_source` for the same file re-parses what the first read saw --
    /// never a fresh disk read -- so the result is identical to a cache hit
    /// (the parser is deterministic), only slower. Source text is ~1/17 of
    /// the AST it produced, which is the whole point of releasing the AST.
    static RELEASED_SOURCE_TEXT: RefCell<HashMap<(PathBuf, crate::pipeline::cfg_strip::CfgTarget), Arc<String>>> = RefCell::new(HashMap::new());
}

/// Hand the interpreter an owned AST for `path`, releasing the cache's copy
/// when nobody else borrows it.
///
/// The interpreter consumes a module's items by value, so it used to
/// deep-clone the shared AST (`(*ast).clone()`), leaving TWO full ASTs per
/// module alive for the rest of the run: the cache's and the interpreter's.
/// Measured on `src/app/browser/main.spl` (513 modules, 10 MB source): the
/// cache side alone was ~300 MB of the 1.4 GB peak.
///
/// The entry is released only when the cache and `ast` (the caller's handle)
/// are the sole owners -- i.e. `shared_source_pinned` would allow evicting it
/// once the caller drops its handle. Otherwise (a HIR lowerer still holds the
/// Arc) this falls back to the old deep clone, so a live borrow is never
/// disturbed. Both paths yield a tree equal to the parse of the cached bytes.
pub fn take_shared_ast(path: &Path, ast: Arc<simple_parser::ast::Module>) -> simple_parser::ast::Module {
    let key = (normalize_path_key(path), crate::pipeline::cfg_strip::cfg_target());
    let released = PARSED_SOURCE_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        let source = match cache.get(&key) {
            Some(SharedSource::Parsed {
                source,
                ast: Ok(cached),
            }) if Arc::ptr_eq(&cached, &ast) => {
                // Owners here: cache entry + `cached` (from get) + `ast`.
                if Arc::strong_count(&ast) != 3 {
                    return false;
                }
                source
            }
            _ => return false,
        };
        cache.remove(&key);
        RELEASED_SOURCE_TEXT.with(|r| r.borrow_mut().insert(key, source));
        true
    });
    if released {
        crate::perf_counters::bump(&crate::perf_counters::INTERP_MODULE_AST_TAKEN, 1);
    }
    Arc::try_unwrap(ast).unwrap_or_else(|shared| (*shared).clone())
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
    shared_source_lookup_for_target(path, crate::pipeline::cfg_strip::cfg_target())
}

/// Look up only the AST selected for this compilation target OS.
pub fn shared_source_lookup_for_target(path: &Path, target: crate::pipeline::cfg_strip::CfgTarget) -> Option<SharedSource> {
    let key = (normalize_path_key(path), target);
    PARSED_SOURCE_CACHE.with(|cache| cache.borrow().get(&key))
}

/// Read + parse `path` once per process, shared by every lane. See
/// `PARSED_SOURCE_CACHE`.
pub fn shared_source(path: &Path) -> SharedSource {
    shared_source_for_target(path, crate::pipeline::cfg_strip::cfg_target())
}

/// Preserve original source bytes while selecting OS branches before parsing.
/// Callers provide the conditional-compilation target names (`cfg_target()`).
pub fn shared_source_for_target(path: &Path, target: crate::pipeline::cfg_strip::CfgTarget) -> SharedSource {
    let key = (normalize_path_key(path), target.clone());
    if let Some(hit) = PARSED_SOURCE_CACHE.with(|cache| cache.borrow().get(&key)) {
        crate::perf_counters::bump(&crate::perf_counters::SHARED_SRC_HITS, 1);
        return hit;
    }
    // The borrow is dropped before the read/parse: filling is not re-entrant
    // today, and holding it across arbitrary work is how a RefCell panic gets
    // introduced later.
    crate::perf_counters::bump(&crate::perf_counters::SHARED_SRC_PARSES, 1);
    // An entry whose AST was released to the interpreter is re-parsed from the
    // SAME bytes it was first read as, so it can never observe a later edit
    // that a still-cached entry would not have observed either.
    if let Some(source) = RELEASED_SOURCE_TEXT.with(|r| r.borrow_mut().remove(&key)) {
        let ast = parse_shared_source(&source, &target);
        let entry = SharedSource::Parsed { source, ast };
        let delta = PARSED_SOURCE_CACHE.with(|cache| cache.borrow_mut().insert(key, entry.clone()));
        mirror_stats(
            delta,
            &crate::perf_counters::PARSED_SOURCE_EVICTIONS,
            &crate::perf_counters::PARSED_SOURCE_PINNED_SKIPS,
            &crate::perf_counters::PARSED_SOURCE_RETAINED_MAX,
        );
        return entry;
    }
    let entry = match crate::read_trace::rts(file!(), line!(), path) {
        Ok(mut source) => {
            // Normalize CRLF -> LF so indentation-sensitive parsing works on
            // all platforms. Both lanes did this before caching; do it once.
            if source.contains('\r') {
                source = source.replace('\r', "");
            }
            let ast = parse_shared_source(&source, &target);
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

fn parse_shared_source(
    source: &str,
    target: &crate::pipeline::cfg_strip::CfgTarget,
) -> Result<Arc<simple_parser::ast::Module>, Arc<str>> {
    let selected = crate::pipeline::cfg_strip::strip_os_when_blocks(source, target)
        .map_err(|error| Arc::<str>::from(error))?;
    simple_parser::Parser::new(&selected)
        .parse()
        .map(Arc::new)
        .map_err(|error| Arc::from(error.to_string()))
}

/// Drop the cross-lane source+AST cache.
pub fn clear_parsed_source_cache() {
    PARSED_SOURCE_CACHE.with(|cache| cache.borrow_mut().clear());
    RELEASED_SOURCE_TEXT.with(|r| r.borrow_mut().clear());
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
        MODULE_ENV_BY_OWNER.with(|c| (c.borrow().len(), c.borrow().values().map(|e| e.retained_len()).sum::<usize>()));
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
    /// `module_owner_key` memo: the last (module path, owner key) pair.
    /// RETENTION: one entry; cleared together with `PATH_KEY_CACHE`.
    static LAST_MODULE_OWNER_KEY: RefCell<Option<(PathBuf, Arc<str>)>> = const { RefCell::new(None) };
    /// `filter_functions_from_value` memo: source dict ptr -> (source Arc, filtered Arc).
    ///
    /// RETENTION: bounded (`FILTERED_DICT_CACHE_MAX_DEFAULT`,
    /// `SIMPLE_FILTERED_DICT_CACHE_MAX`). Evicting is safe DESPITE the raw
    /// address key: the lookup below re-checks `Arc::ptr_eq(src, dict)`, so a
    /// recycled address is a miss and a rebuild, never a false hit. An entry
    /// whose source or filtered map is still referenced elsewhere is pinned --
    /// which is also the case where eviction would free nothing, since the
    /// allocation stays alive through the other reference.
    static FILTERED_DICT_CACHE: RefCell<BoundedCache<usize, (Arc<DictMap>, Arc<DictMap>)>> =
        RefCell::new(BoundedCache::new(filtered_dict_cache_max(), filtered_dict_pinned));
    static LOADER_STATS: RefCell<LoaderStats> = RefCell::new(LoaderStats::default());
}

/// Maximum depth for recursive module loading to prevent infinite loops
pub const MAX_MODULE_DEPTH: usize = 50;

// Thread-local cache for module exports to avoid re-parsing modules
// Key: normalized module path, Value: module exports dict
thread_local! {
    pub static MODULE_EXPORTS_CACHE: RefCell<HashMap<PathBuf, Value>> = RefCell::new(HashMap::new());
    pub(crate) static MODULE_EXPORT_OWNERS: RefCell<HashMap<usize, Arc<str>>> = RefCell::new(HashMap::new());
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
    FLATTEN_OWNER_ENUMS.with(|table| table.borrow_mut().clear());
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
    LAST_MODULE_OWNER_KEY.with(|last| *last.borrow_mut() = None);
    FILTERED_DICT_CACHE.with(|cache| cache.borrow_mut().clear());
    sweep_module_dict_tables();
    clear_probe_source_cache();
    clear_parsed_source_cache();
    crate::pipeline::module_loader::clear_module_source_text_cache();
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
            .retain(|_, owner| is_stdlib(Path::new(&**owner)));
    });
    MODULE_CLASSES_CACHE.with(|cache| cache.borrow_mut().retain(|k, _| is_stdlib(k)));
    MODULE_FUNCTIONS_CACHE.with(|cache| cache.borrow_mut().retain(|k, _| is_stdlib(k)));
    MODULE_ENUMS_CACHE.with(|cache| cache.borrow_mut().retain(|k, _| is_stdlib(k)));
    FLATTEN_OWNER_ENUMS.with(|table| table.borrow_mut().retain_stdlib());
    MODULE_GLOBALS.with(|cache| cache.borrow_mut().clear());
    FUNCTION_OVERLOADS.with(|cache| cache.borrow_mut().clear());
    MODULE_GLOBALS_INITIAL_BY_OWNER.with(|cache| {
        cache
            .borrow_mut()
            .retain(|owner, _| is_stdlib(Path::new(&**owner)));
    });
    crate::interpreter::reset_owned_globals_from_initial();
    MODULE_ENV_BY_OWNER.with(|cache| {
        cache
            .borrow_mut()
            .retain(|owner, _| is_stdlib(Path::new(&**owner)));
    });
    MODULE_GLOBAL_BINDINGS_BY_OWNER.with(|cache| {
        cache
            .borrow_mut()
            .retain(|owner, _| is_stdlib(Path::new(&**owner)));
    });
    FUNCTION_MODULE_OWNER.with(|cache| {
        cache
            .borrow_mut()
            .retain(|_, owner| is_stdlib(Path::new(&**owner)));
    });
    // Always clear loading/depth state (transient per-file)
    MODULES_LOADING.with(|loading| loading.borrow_mut().clear());
    MODULE_LOAD_DEPTH.with(|depth| *depth.borrow_mut() = 0);
    PARTIAL_MODULE_EXPORTS_CACHE.with(|cache| cache.borrow_mut().clear());
    // Drop memoised filtered dicts whose source no one else holds any more.
    FILTERED_DICT_CACHE.with(|cache| cache.borrow_mut().retain(|_, (src, _)| Arc::strong_count(src) > 1));
    sweep_module_dict_tables();
    // Source-derived probe/AST memos must not survive a selective boundary:
    // test and IDE callers may edit, delete, or recreate files between runs.
    clear_probe_source_cache();
    clear_parsed_source_cache();
    crate::pipeline::module_loader::clear_module_source_text_cache();
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

/// Owner key of a module: `normalize_path_key(path)` as text.
///
/// A module's evaluation asks for its own owner once per imported name and
/// once per global, always with the same path. Each ask re-hashed the PathBuf
/// into `PATH_KEY_CACHE` and allocated a fresh `Arc<str>` -- about 13% of
/// module-loading CPU in a `sample` of `simple test <spec>`. The one-entry
/// memo hits only on a byte-identical path and returns exactly the value
/// computed from `normalize_path_key`, so callers see the same key.
pub fn module_owner_key(path: &Path) -> Arc<str> {
    if let Some(owner) = LAST_MODULE_OWNER_KEY.with(|last| {
        last.borrow()
            .as_ref()
            .filter(|(cached, _)| cached.as_os_str() == path.as_os_str())
            .map(|(_, owner)| owner.clone())
    }) {
        return owner;
    }
    let owner: Arc<str> = Arc::from(normalize_path_key(path).to_string_lossy().as_ref());
    LAST_MODULE_OWNER_KEY.with(|last| *last.borrow_mut() = Some((path.to_path_buf(), owner.clone())));
    owner
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

// ---------------------------------------------------------------------------
// Layered module export dicts.
//
// A module's `Value::Dict` holds only the entries the module itself put in
// its export table; whatever it imported whole lives in the `ModuleTable`
// registered here under the dict's address. Every name lookup THROUGH a
// module value goes via `module_dict_get` / `module_dict_for_each_visible`,
// which see exactly the flat table the module used to carry.
// doc/08_tracking/bug/interpreter_use_unpack_reexports_transitive_closure_2026-10-20.md
//
// The registry holds a clone of the dict `Arc` beside the view, so an address
// can never be recycled while its entry is live (the `FILTERED_DICT_CACHE`
// rule). Process-wide, not thread-local: a module value can cross threads.
// ---------------------------------------------------------------------------

type ModuleDictRegistry = HashMap<usize, (Arc<DictMap>, TableView)>;

fn module_dict_tables() -> &'static parking_lot::RwLock<ModuleDictRegistry> {
    static TABLES: OnceLock<parking_lot::RwLock<ModuleDictRegistry>> = OnceLock::new();
    TABLES.get_or_init(|| parking_lot::RwLock::new(HashMap::new()))
}

/// Lock-free negative filter in front of the registry: one bit per hashed
/// dict address, set on registration and never cleared. Every dict field
/// miss, method call and write asks "is this a module dict?"; for a plain
/// dict this answers no with one relaxed load instead of a lock. A set bit
/// only means "check the registry" (false positives are resolved there).
const REGISTRY_FILTER_WORDS: usize = 1024;
static REGISTRY_FILTER: [std::sync::atomic::AtomicU64; REGISTRY_FILTER_WORDS] =
    [const { std::sync::atomic::AtomicU64::new(0) }; REGISTRY_FILTER_WORDS];

fn registry_filter_bit(addr: usize) -> (usize, u64) {
    // Allocation addresses are 16-byte aligned; mix before indexing.
    let h = (addr >> 4).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 32;
    let bit = h % (REGISTRY_FILTER_WORDS * 64);
    (bit / 64, 1u64 << (bit % 64))
}

fn maybe_registered(addr: usize) -> bool {
    let (word, mask) = registry_filter_bit(addr);
    REGISTRY_FILTER[word].load(std::sync::atomic::Ordering::Acquire) & mask != 0
}

fn register_module_dict(dict: &Arc<DictMap>, view: TableView) {
    let (word, mask) = registry_filter_bit(Arc::as_ptr(dict) as usize);
    REGISTRY_FILTER[word].fetch_or(mask, std::sync::atomic::Ordering::Release);
    module_dict_tables()
        .write()
        .insert(Arc::as_ptr(dict) as usize, (Arc::clone(dict), view));
}

/// Drop registry entries no `Value` can reach any more: the dict is held only
/// by the registry and by its own table (`own` / `filtered_own`).
fn sweep_module_dict_tables() {
    module_dict_tables()
        .write()
        .retain(|_, (dict, _)| Arc::strong_count(dict) > 2);
}

/// The registered view of `dict`, if it is a finished module's export dict
/// (or the filtered copy of one).
pub fn module_dict_view(dict: &Arc<DictMap>) -> Option<TableView> {
    if !maybe_registered(Arc::as_ptr(dict) as usize) {
        return None;
    }
    module_dict_tables()
        .read()
        .get(&(Arc::as_ptr(dict) as usize))
        .and_then(|(held, view)| Arc::ptr_eq(held, dict).then(|| view.clone()))
}

/// The registered view of `dict` when it resolves anything beyond `dict`
/// itself; `None` for plain dicts and modules that imported nothing whole.
pub fn layered_view(dict: &Arc<DictMap>) -> Option<TableView> {
    module_dict_view(dict).filter(|view| !view.table.layers().is_empty())
}

/// `dict`'s view for layering into an importer: the registered table, or a
/// leaf table that is exactly `dict` (partial / cycle / empty dicts).
pub fn module_table_for(dict: &Arc<DictMap>) -> TableView {
    match module_dict_view(dict) {
        Some(view) if !view.filtered => view,
        _ => TableView::raw(Arc::new(ModuleTable::leaf(Arc::clone(dict)))),
    }
}

/// `dict[key]` as the module's flat export table would have answered it.
pub fn module_dict_get(dict: &Arc<DictMap>, key: &str) -> Option<Value> {
    if let Some(value) = dict.get(key) {
        return Some(value.clone());
    }
    layered_view(dict).and_then(|view| view.get(key).cloned())
}

pub fn module_dict_contains(dict: &Arc<DictMap>, key: &str) -> bool {
    dict.contains_key(key) || layered_view(dict).is_some_and(|view| view.contains_key(key))
}

/// `Arc::make_mut` for a dict that may be a layered module value: a write
/// first materializes the flat surface, so the written copy still carries
/// every name the module value resolved.
pub fn module_dict_make_mut(dict: &mut Arc<DictMap>) -> &mut DictMap {
    if let Some(flat) = module_dict_flat(dict) {
        *dict = flat;
    }
    Arc::make_mut(dict)
}

/// Every visible (name, value) of `dict`, each name once.
pub fn module_dict_for_each_visible(dict: &Arc<DictMap>, mut f: impl FnMut(&String, &Value)) {
    match layered_view(dict) {
        Some(view) => view.for_each_visible(|name, value| f(name, value)),
        None => {
            for (name, value) in dict.iter() {
                f(name, value);
            }
        }
    }
}

/// The flat map a layered module dict stands for (a fresh copy), or `None`
/// when `dict` is already flat. For collection operations applied to a
/// module value (`len`, `keys`, iteration, ...).
pub fn module_dict_flat(dict: &Arc<DictMap>) -> Option<Arc<DictMap>> {
    let view = layered_view(dict)?;
    let mut flat = DictMap::new();
    view.for_each_visible(|name, value| {
        flat.insert(name.clone(), value.clone());
    });
    Some(Arc::new(flat))
}

/// Number of visible names of `dict`.
pub fn module_dict_len(dict: &Arc<DictMap>) -> usize {
    match layered_view(dict) {
        Some(view) => {
            let mut n = 0;
            view.for_each_visible(|_, _| n += 1);
            n
        }
        None => dict.len(),
    }
}

/// Register a finished module's export table and cache its dict.
pub fn cache_module_export_table(path: &Path, table: Arc<ModuleTable>) {
    // Registered even without layers: importers then share this one table
    // (one id, one set of index entries) instead of minting a leaf per import.
    let dict = Arc::clone(table.own());
    register_module_dict(&dict, TableView::raw(table));
    cache_module_exports(path, Value::Dict(dict));
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
            // A layered module export dict: its filtered view is the table's
            // filtered view, so the filtered dict keeps resolving the layers.
            if let Some(view) = layered_view(dict) {
                if view.filtered {
                    return Value::Dict(Arc::clone(dict));
                }
                let filtered = Arc::clone(view.table.filtered_own(filter_functions_from_value));
                register_module_dict(
                    &filtered,
                    TableView {
                        table: view.table,
                        filtered: true,
                    },
                );
                return Value::Dict(filtered);
            }
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
            let filtered: Arc<DictMap> = Arc::new(
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

    /// The one-entry owner memo must return exactly `normalize_path_key` as
    /// text for every path, including when two modules alternate and when a
    /// distinct spelling of the same file is asked for.
    #[test]
    fn module_owner_key_matches_normalize_path_key_across_alternating_paths() {
        let dir = scratch_dir("owner-key");
        let a = write_module(&dir, 1);
        let b = write_module(&dir, 2);
        let a_dotted = dir.join(".").join("m1.spl");
        let missing = dir.join("absent.spl");
        for path in [&a, &a, &b, &a, &a_dotted, &b, &missing, &missing, &a] {
            let expected = normalize_path_key(path).to_string_lossy().into_owned();
            assert_eq!(&*super::module_owner_key(path), expected.as_str(), "{}", path.display());
        }
        let _ = std::fs::remove_dir_all(&dir);
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
            let mut map = crate::value::DictMap::new();
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
            let mut map = crate::value::DictMap::new();
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

/// Enum registered by the module that is currently executing (the importing /
/// declaring module of the running function), if that module declares `name`.
/// Used to resolve a bare enum name deterministically: the current module's own
/// enum beats the cross-module `GLOBAL_ENUMS` last-registration-wins entry.
/// See bug `seed_enum_variant_bare_name_last_registration_wins_2026_10_19`.
pub fn owner_module_enum(name: &str) -> Option<Arc<EnumDef>> {
    // A first-class enum type/constructor already carries an exact identity;
    // it must not be re-bound by the module in which it is later used.
    if name.starts_with(crate::interpreter::FLATTEN_OWNER_SYMBOL_PREFIX) {
        return crate::interpreter::GLOBAL_ENUMS.with(|t| t.borrow().get(name).cloned());
    }
    let owned = owner_module_def(name, |owner, name| {
        FLATTEN_OWNER_ENUMS
            .with(|t| t.borrow().get(owner).and_then(|m| m.get(name).cloned()))
            .or_else(|| {
                MODULE_ENUMS_CACHE.with(|cache| cache.borrow().get(Path::new(owner)).and_then(|m| m.get(name).cloned()))
            })
    });
    owned
}

/// Existing source-name census fallback, separate from the owner-only API.
pub(crate) fn unique_enum_definition(name: &str) -> Option<Arc<EnumDef>> {
    // Canonical builtins have no source declaration qualification.
    if matches!(name, "Option" | "Result") {
        if let Some(builtin) = crate::interpreter::GLOBAL_ENUMS.with(|t| t.borrow().get(name).cloned()) {
            return Some(builtin);
        }
    }
    // Legacy/global lookup is allowed only for a unique declaration. More
    // than one identity never becomes a first/last-registration winner.
    FLATTEN_OWNER_ENUMS.with(|table| table.borrow().unique_names.get(name).and_then(|entry| entry.clone()))
}

pub(crate) fn enum_source_name(def: &EnumDef) -> &str {
    def.attributes.iter().find_map(|a| a.name.strip_prefix(crate::interpreter::FLATTEN_ENUM_SOURCE_NAME_ATTR_PREFIX))
        .unwrap_or(&def.name)
}

pub(crate) fn enum_display_name(identity: &str) -> String {
    crate::interpreter::GLOBAL_ENUMS.with(|table| {
        table.borrow().get(identity).map(|def| enum_source_name(def).to_owned())
            .unwrap_or_else(|| identity.to_owned())
    })
}

/// Walk from the executing module (or `<entry>` at top level) through explicit
/// `use m.{Name}` bindings to the declaring module, returning its definition.
/// Bounded: facade chains resolve, cycles cannot hang.
fn owner_module_def<T>(name: &str, lookup: impl Fn(&str, &str) -> Option<Arc<T>>) -> Option<Arc<T>> {
    let mut owner = crate::interpreter::CURRENT_EXEC_MODULE
        .with(|cell| cell.borrow().clone())
        .unwrap_or_else(|| Arc::from("<entry>"));
    let mut name = name.to_owned();
    for _ in 0..8 {
        if let Some(own) = lookup(&owner, &name) {
            return Some(own);
        }
        let (next_owner, next_name) = crate::interpreter::owner_bindings(&owner)
            .and_then(|b| b.get(&name).map(std::borrow::Cow::into_owned))?;
        if next_owner == owner && next_name == name {
            return None;
        }
        owner = next_owner;
        name = next_name;
    }
    None
}

thread_local! {
    /// Flattened-lane enum table keyed by declaring module (owner path key);
    /// the flat `enums`/`GLOBAL_ENUMS` maps are last-registration-wins by bare
    /// name. See bug seed_enum_variant_bare_name_last_registration_wins_2026_10_19.
    static FLATTEN_OWNER_ENUMS: RefCell<OwnerEnumTable> = RefCell::new(OwnerEnumTable::default());
}

#[derive(Default)]
struct OwnerEnumTable {
    declarations: HashMap<Arc<str>, HashMap<String, Arc<EnumDef>>>,
    // Derived index of the existing owner census, never an independent ID
    // allocator. None records ambiguity; resolution remains O(1) on hot paths.
    unique_names: HashMap<String, Option<Arc<EnumDef>>>,
}

impl std::ops::Deref for OwnerEnumTable {
    type Target = HashMap<Arc<str>, HashMap<String, Arc<EnumDef>>>;
    fn deref(&self) -> &Self::Target { &self.declarations }
}
impl std::ops::DerefMut for OwnerEnumTable {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.declarations }
}
impl OwnerEnumTable {
    fn index(index: &mut HashMap<String, Option<Arc<EnumDef>>>, def: &Arc<EnumDef>) {
        index.entry(enum_source_name(def).to_owned()).and_modify(|known| {
            if known.as_ref().is_some_and(|prior| prior.name != def.name ||
                prior.attributes.iter().find_map(|a| a.name.strip_prefix(crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX)) !=
                def.attributes.iter().find_map(|a| a.name.strip_prefix(crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX))) {
                *known = None;
            } else if known.is_some() {
                // Re-registration of one declaration must refresh methods,
                // payload fields and variants rather than retain the old Arc.
                *known = Some(Arc::clone(def));
            }
        }).or_insert_with(|| Some(Arc::clone(def)));
    }
    fn clear(&mut self) { self.declarations.clear(); self.unique_names.clear(); }
    fn retain_stdlib(&mut self) {
        self.declarations.retain(|owner, _| owner.contains("src/lib/") || owner.contains("src\\lib\\"));
        self.unique_names.clear();
        for declarations in self.declarations.values() {
            for def in declarations.values() { Self::index(&mut self.unique_names, def); }
        }
    }
}

/// Record a flattened enum under its declaring module, read from the owner
/// attribute the flattening loader puts on the enum declaration itself (so a
/// methodless enum is covered). Untagged enums (entry-declared or a
/// non-flattened run) are not recorded.
pub fn record_flattened_owner_enum(enum_def: &Arc<EnumDef>) {
    let owner = enum_def.attributes.iter().find_map(|a| {
        a.name.strip_prefix(crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX)
            .map(|raw| if raw == "<entry>" { Arc::<str>::from(raw) }
                else { Arc::<str>::from(normalize_path_key(Path::new(raw)).to_string_lossy().as_ref()) })
    });
    if let Some(owner) = owner {
        FLATTEN_OWNER_ENUMS.with(|t| {
            let mut table = t.borrow_mut();
            table.entry(owner).or_default()
                .insert(enum_source_name(enum_def).to_owned(), Arc::clone(enum_def));
            OwnerEnumTable::index(&mut table.unique_names, enum_def);
        });
    }
}

/// Class declared by the module that is currently executing, if that module
/// declares `name`. Mirrors [`owner_module_enum`]: a same-named class from
/// another co-loaded module must not hijack construction or method dispatch
/// inside the declaring module. See bug
/// `interp_class_name_collision_breaks_test_db_persistence_2026-08-10`.
pub fn owner_module_class(name: &str) -> Option<Arc<ClassDef>> {
    owner_module_def(name, |owner, name| {
        FLATTEN_OWNER_CLASSES
            .with(|t| t.borrow().get(owner).and_then(|m| m.get(name).cloned()))
            .or_else(|| {
                MODULE_CLASSES_CACHE.with(|cache| cache.borrow().get(Path::new(owner)).and_then(|m| m.get(name).cloned()))
            })
    })
}

thread_local! {
    /// Flattened-lane class table keyed by declaring module (owner path key).
    /// The flat `classes` map is last-registration-wins by bare name; this one
    /// is not. See bug interp_class_name_collision_breaks_test_db_persistence_2026-08-10.
    static FLATTEN_OWNER_CLASSES: RefCell<HashMap<Arc<str>, HashMap<String, Arc<ClassDef>>>> =
        RefCell::new(HashMap::new());
}

/// Record a flattened class under its declaring module, derived from the
/// owner attribute the flattening loader puts on its methods. Classes with no
/// owner-tagged method (no methods, or a non-flattened run) are not recorded.
pub fn record_flattened_owner_class(class_def: &Arc<ClassDef>) {
    let owner = class_def.methods.iter().find_map(|m| {
        m.attributes.iter().find_map(|a| {
            a.name
                .strip_prefix(crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX)
                .map(|raw| Arc::<str>::from(normalize_path_key(Path::new(raw)).to_string_lossy().as_ref()))
        })
    });
    if let Some(owner) = owner {
        FLATTEN_OWNER_CLASSES.with(|t| {
            t.borrow_mut()
                .entry(owner)
                .or_default()
                .insert(class_def.name.clone(), Arc::clone(class_def));
        });
    }
}

/// Resolve a bare class name: the executing module's own class first, then
/// the caller's flat scope table.
pub fn resolve_class(classes: &HashMap<String, Arc<ClassDef>>, name: &str) -> Option<Arc<ClassDef>> {
    owner_module_class(name).or_else(|| classes.get(name).cloned())
}

/// Snapshot scope classes that a `use m.{a, b}` import must not clobber:
/// a name the incoming module defines, that is already bound in scope to a
/// DIFFERENT class (another module's), and that the braced list does not name.
/// Callers re-insert the snapshot after merging. Non-group imports keep the
/// previous last-registration behaviour.
pub fn unimported_def_collisions<T>(
    explicit: Option<&[String]>,
    incoming: &HashMap<String, Arc<T>>,
    classes: &HashMap<String, Arc<T>>,
) -> Vec<(String, Arc<T>)> {
    let Some(explicit) = explicit else { return Vec::new() };
    incoming
        .iter()
        .filter_map(|(name, def)| {
            let existing = classes.get(name)?;
            if Arc::ptr_eq(existing, def) || explicit.iter().any(|n| n == name) {
                return None;
            }
            Some((name.clone(), Arc::clone(existing)))
        })
        .collect()
}

/// Cached class table of a module, if loaded.
pub fn cached_module_classes(path: &Path) -> Option<HashMap<String, Arc<ClassDef>>> {
    let key = normalize_path_key(path);
    MODULE_CLASSES_CACHE.with(|cache| cache.borrow().get(&key).cloned())
}

#[cfg(test)]
mod class_collision_tests {
    use super::*;
    use simple_parser::ast::Node;

    fn class_def(src: &str) -> Arc<ClassDef> {
        let module = simple_parser::Parser::new(src).parse().expect("parse class fixture");
        module
            .items
            .into_iter()
            .find_map(|n| match n {
                Node::Class(c) => Some(Arc::new(c)),
                _ => None,
            })
            .expect("fixture declares a class")
    }

    #[test]
    fn braced_import_keeps_importers_same_name_class() {
        let a = class_def("class Interner:\n    n: i64\n");
        let b = class_def("class Interner:\n    label: text\n");
        let mut scope = HashMap::new();
        scope.insert("Interner".to_string(), Arc::clone(&a));
        let mut incoming = HashMap::new();
        incoming.insert("Interner".to_string(), Arc::clone(&b));

        let explicit = vec!["tag_b".to_string()];
        let preserved = unimported_def_collisions(Some(&explicit), &incoming, &scope);
        scope.extend(incoming.clone());
        scope.extend(preserved);
        assert!(Arc::ptr_eq(&scope["Interner"], &a), "unimported same-name class clobbered importer's");
    }

    #[test]
    fn explicitly_imported_same_name_class_still_wins() {
        let a = class_def("class Point:\n    x: i64\n");
        let b = class_def("class Point:\n    y: i64\n");
        let scope: HashMap<_, _> = [("Point".to_string(), Arc::clone(&a))].into_iter().collect();
        let incoming: HashMap<_, _> = [("Point".to_string(), Arc::clone(&b))].into_iter().collect();
        let explicit = vec!["Point".to_string()];
        assert!(unimported_def_collisions(Some(&explicit), &incoming, &scope).is_empty());
        // Non-braced imports keep previous behaviour.
        assert!(unimported_def_collisions(None, &incoming, &scope).is_empty());
        // Same Arc re-merged is not a collision.
        let same: HashMap<_, _> = [("Point".to_string(), Arc::clone(&a))].into_iter().collect();
        assert!(unimported_def_collisions(Some(&[]), &same, &scope).is_empty());
    }

    #[test]
    fn owner_module_class_prefers_executing_modules_class() {
        let a = class_def("class Pair:\n    l: i64\n");
        let b = class_def("class Pair:\n    r: i64\n");
        let owner = "/probe/owner_b.spl";
        MODULE_CLASSES_CACHE.with(|c| {
            c.borrow_mut()
                .insert(PathBuf::from(owner), [("Pair".to_string(), Arc::clone(&b))].into_iter().collect())
        });
        let scope: HashMap<_, _> = [("Pair".to_string(), Arc::clone(&a))].into_iter().collect();
        let saved = crate::interpreter::CURRENT_EXEC_MODULE.with(|c| c.replace(Some(Arc::from(owner))));
        assert!(Arc::ptr_eq(&resolve_class(&scope, "Pair").unwrap(), &b));
        crate::interpreter::CURRENT_EXEC_MODULE.with(|c| *c.borrow_mut() = None);
        assert!(Arc::ptr_eq(&resolve_class(&scope, "Pair").unwrap(), &a));
        crate::interpreter::CURRENT_EXEC_MODULE.with(|c| *c.borrow_mut() = saved);
        MODULE_CLASSES_CACHE.with(|c| c.borrow_mut().remove(Path::new(owner)));
    }
}

/// Cached enum table of a module, if loaded.
pub fn cached_module_enums(path: &Path) -> Option<HashMap<String, Arc<EnumDef>>> {
    let key = normalize_path_key(path);
    MODULE_ENUMS_CACHE.with(|cache| cache.borrow().get(&key).cloned())
}

#[cfg(test)]
mod enum_owner_collision_tests {
    //! seed_enum_variant_bare_name_last_registration_wins_2026_10_19: same-named
    //! enums from two co-loaded (flattened) modules must resolve per owner.
    use super::*;
    use simple_parser::ast::{Attribute, Node};

    fn enum_def(src: &str, owner: Option<&str>) -> Arc<EnumDef> {
        let module = simple_parser::Parser::new(src).parse().expect("parse enum fixture");
        let mut e = module
            .items
            .into_iter()
            .find_map(|n| match n {
                Node::Enum(e) => Some(e),
                _ => None,
            })
            .expect("fixture declares an enum");
        if let Some(owner) = owner {
            e.attributes.push(Attribute {
                span: e.span,
                name: format!("{}{owner}", crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX),
                value: None,
                args: None,
                named_args: None,
            });
        }
        Arc::new(e)
    }

    fn variants(e: &EnumDef) -> Vec<&str> {
        e.variants.iter().map(|v| v.name.as_str()).collect()
    }

    fn with_exec_module<R>(owner: Option<&str>, f: impl FnOnce() -> R) -> R {
        let saved = crate::interpreter::CURRENT_EXEC_MODULE.with(|c| c.replace(owner.map(Arc::from)));
        let r = f();
        crate::interpreter::CURRENT_EXEC_MODULE.with(|c| *c.borrow_mut() = saved);
        r
    }

    fn owner_key(raw: &str) -> String {
        normalize_path_key(Path::new(raw)).to_string_lossy().into_owned()
    }

    #[test]
    fn each_declaring_module_resolves_its_own_same_name_enum() {
        let (a_path, b_path) = ("/probe/enum_own_a.spl", "/probe/enum_own_b.spl");
        let a = enum_def("enum Mode:\n    Fast\n    Slow\n", Some(a_path));
        let b = enum_def("enum Mode:\n    Red\n    Blue(i64)\n", Some(b_path));
        record_flattened_owner_enum(&a);
        record_flattened_owner_enum(&b); // last registration: would win by bare name
        let in_a = with_exec_module(Some(&owner_key(a_path)), || owner_module_enum("Mode")).unwrap();
        let in_b = with_exec_module(Some(&owner_key(b_path)), || owner_module_enum("Mode")).unwrap();
        assert_eq!(variants(&in_a), ["Fast", "Slow"]);
        assert_eq!(variants(&in_b), ["Red", "Blue"]);
        // Payload variant keeps its fields through the owner table.
        assert!(in_b.variants[1].fields.as_ref().is_some_and(|f| f.len() == 1));
    }

    #[test]
    fn module_without_own_or_bound_enum_falls_back_to_flat_table() {
        let a = enum_def("enum Lone:\n    One\n", Some("/probe/enum_lone.spl"));
        record_flattened_owner_enum(&a);
        // Another module neither declares nor binds `Lone`: no owner answer,
        // callers fall back to the flat `enums` / GLOBAL_ENUMS tables.
        assert!(with_exec_module(Some(&owner_key("/probe/enum_other.spl")), || owner_module_enum("Lone")).is_none());
        assert!(with_exec_module(None, || owner_module_enum("Lone")).is_none());
    }

    #[test]
    fn untagged_enum_is_not_recorded_under_any_owner() {
        let e = enum_def("enum Untagged:\n    X\n", None);
        record_flattened_owner_enum(&e);
        let found = FLATTEN_OWNER_ENUMS.with(|t| t.borrow().values().any(|m| m.contains_key("Untagged")));
        assert!(!found);
    }

    #[test]
    fn braced_import_keeps_importers_same_name_enum() {
        let a = enum_def("enum Mode:\n    Fast\n    Slow\n", None);
        let b = enum_def("enum Mode:\n    Red\n", None);
        let mut scope: HashMap<_, _> = [("Mode".to_string(), Arc::clone(&a))].into_iter().collect();
        let incoming: HashMap<_, _> = [("Mode".to_string(), Arc::clone(&b))].into_iter().collect();
        let explicit = vec!["mode_b_name".to_string()];
        let preserved = unimported_def_collisions(Some(&explicit), &incoming, &scope);
        scope.extend(incoming.clone());
        scope.extend(preserved);
        assert!(Arc::ptr_eq(&scope["Mode"], &a));
        // Explicitly importing the same name lets it win.
        let named = vec!["Mode".to_string()];
        assert!(unimported_def_collisions(Some(&named), &incoming, &scope).is_empty());
    }
}

#[cfg(test)]
mod owner_identity_lifecycle_tests {
    use super::*;
    use simple_parser::{ast::{Attribute, Node}, Parser};

    fn definition(owner: &str, source: &str) -> Arc<EnumDef> {
        let mut def = Parser::new(source).parse().unwrap().items.into_iter().find_map(|node| match node {
            Node::Enum(def) => Some(def), _ => None,
        }).unwrap();
        let original = def.name.clone();
        def.name = crate::interpreter::flatten_owner_mangled_name(owner, &original);
        def.attributes.extend([
            Attribute { span: def.span, name: format!("{}{owner}", crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX), value: None, args: None, named_args: None },
            Attribute { span: def.span, name: format!("{}{original}", crate::interpreter::FLATTEN_ENUM_SOURCE_NAME_ATTR_PREFIX), value: None, args: None, named_args: None },
        ]);
        Arc::new(def)
    }

    #[test]
    fn same_identity_reregistration_refreshes_unique_lookup_metadata() {
        clear_module_cache();
        let old = definition("/probe/warm_reload.spl", "enum WarmReloadMode:\n    Old\n");
        let fresh = definition("/probe/warm_reload.spl", "enum WarmReloadMode:\n    New(value: i64)\n    fn fresh_method(self) -> i64:\n        7\n");
        record_flattened_owner_enum(&old);
        record_flattened_owner_enum(&fresh);
        let resolved = unique_enum_definition("WarmReloadMode").expect("unique refreshed declaration");
        assert!(Arc::ptr_eq(&resolved, &fresh), "index retained the previous definition Arc");
        assert_eq!(resolved.variants[0].name, "New");
        assert_eq!(resolved.variants[0].fields.as_ref().unwrap().len(), 1);
        assert!(resolved.methods.iter().any(|method| method.name == "fresh_method"));
        clear_module_cache();
        assert!(unique_enum_definition("WarmReloadMode").is_none());
    }

    #[test]
    fn selective_cache_clear_rebuilds_uniqueness_after_user_owner_removal() {
        clear_module_cache();
        let standard = definition("/probe/src/lib/common/warm_mode.spl", "enum RetainedMode:\n    Standard\n");
        let application = definition("/probe/app/warm_mode.spl", "enum RetainedMode:\n    Application\n");
        record_flattened_owner_enum(&standard);
        record_flattened_owner_enum(&application);
        assert!(unique_enum_definition("RetainedMode").is_none(), "two owners must remain ambiguous");
        clear_module_cache_selective();
        let resolved = unique_enum_definition("RetainedMode").expect("stdlib owner retained");
        assert!(Arc::ptr_eq(&resolved, &standard));
        clear_module_cache();
        assert!(unique_enum_definition("RetainedMode").is_none());
    }

    #[test]
    fn actual_stdlib_module_loading_exports_canonical_family_names() {
        clear_module_cache();
        crate::interpreter::clear_interpreter_state();
        let core = Path::new(env!("CARGO_MANIFEST_DIR")).join("../lib/std/src/core");
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();
        for (file, name, expected_id) in [("option.spl", "Option", 1), ("result.spl", "Result", 0)] {
            let path = core.join(file).canonicalize().expect("actual stdlib provider");
            let source = std::fs::read_to_string(&path).expect("actual stdlib source");
            let mut ast = Parser::new(&source).parse().expect("actual stdlib grammar");
            mark_selected_builtin_enum_origins(&mut ast.items, &path, |_| Some(path.clone()));
            let (_, exports, _, _, _) = crate::interpreter::interpreter_module::evaluate_module_exports(
                &ast.items, Some(&path), &mut functions, &mut classes, &mut enums,
            ).expect("actual stdlib module evaluation");
            let Some(Value::EnumType { enum_name }) = exports.get(name) else {
                panic!("stdlib module did not export its enum type {name}");
            };
            assert_eq!(enum_name, name, "actual stdlib family was treated as a user nominal type");
            assert_eq!(crate::codegen::shared::enum_runtime_type_id(enum_name), expected_id);
        }
        clear_module_cache();
        crate::interpreter::clear_interpreter_state();
    }
}


/// This name is not source syntax: Attribute.name is parsed as an identifier,
/// which cannot contain NUL. Parsed AST caches are populated before stamping.
pub(crate) const SELECTED_BUILTIN_ENUM_ORIGIN: &str = "\0simple_selected_builtin_enum_origin=";

pub(crate) fn builtin_enum_shape(def: &EnumDef, source_name: &str) -> bool {
    let (params, expected): (usize, &[(&str, usize)]) = match source_name {
        "Option" => (1, &[("Some", 1), ("None", 0)]),
        "Result" => (2, &[("Ok", 1), ("Err", 1)]),
        _ => return false,
    };
    def.generic_params.len() == params && def.variants.len() == expected.len()
        && expected.iter().all(|(name, arity)| def.variants.iter().any(|variant|
            variant.name == *name && variant.fields.as_ref().map_or(0, Vec::len) == *arity))
}

/// Mark only the physical module's own declarations after actual resolution.
/// `selected` is supplied by the SAME importing loader and importer context.
pub(crate) fn mark_selected_builtin_enum_origins(
    items: &mut [simple_parser::ast::Node], module_path: &Path,
    mut selected: impl FnMut(&str) -> Option<PathBuf>,
) {
    let physical = normalize_path_key(module_path);
    let owner = physical.to_string_lossy();
    for item in items {
        let simple_parser::ast::Node::Enum(def) = item else { continue; };
        let stem = match def.name.as_str() { "Option" => "option", "Result" => "result", _ => continue };
        // An imported/flattened nested declaration belongs to its real owner.
        if def.attributes.iter().filter_map(|a| a.name.strip_prefix(crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX))
            .any(|declared| normalize_path_key(Path::new(declared)) != physical) { continue; }
        // Reclassification is performed on an unshared owned AST, never values.
        def.attributes.retain(|a| !a.name.starts_with(SELECTED_BUILTIN_ENUM_ORIGIN));
        if selected(stem).is_some_and(|path| normalize_path_key(&path) == physical) {
            def.attributes.push(simple_parser::ast::Attribute {
                span: def.span, name: format!("{SELECTED_BUILTIN_ENUM_ORIGIN}{owner}"),
                value: None, args: None, named_args: None,
            });
        }
    }
}

/// Existing module caches are physical-path keyed. Refuse a second provider
/// election that would silently change the meaning of already live values.
pub(crate) fn check_cached_builtin_enum_origins(
    module_path: &Path, importer: &Path,
    mut selected: impl FnMut(&str) -> Option<PathBuf>,
) -> Result<(), crate::error::CompileError> {
    let Some(definitions) = cached_module_enums(module_path) else { return Ok(()); };
    let physical = normalize_path_key(module_path);
    for def in definitions.values() {
        // Module export caches may retain imported/re-exported definitions.
        // Their family election belongs to their declaring physical module,
        // never to the facade/cache-container path.
        let declared_owner = def.attributes.iter().find_map(|a|
            a.name.strip_prefix(SELECTED_BUILTIN_ENUM_ORIGIN)
                .or_else(|| a.name.strip_prefix(crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX)));
        if declared_owner.is_none_or(|owner| normalize_path_key(Path::new(owner)) != physical) { continue; }
        let name = enum_source_name(def);
        let stem = match name { "Option" => "option", "Result" => "result", _ => continue };
        let elected = selected(stem);
        let expected = builtin_enum_shape(def, name)
            && elected.as_ref().is_some_and(|path| normalize_path_key(path) == physical);
        let actual = def.name == name;
        if expected != actual {
            return Err(crate::error::CompileError::Runtime(format!(
                "builtin enum provider conflict for {} imported from {}: selected {:?}; cached family {}; use a fresh isolated module context",
                physical.display(), importer.display(), elected, def.name,
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
mod selected_builtin_provider_tests {
    use super::*;
    use simple_parser::{Parser, ast::Node};

    const OPTION: &str = "enum Option<T>:\n    Some(value: T)\n    None\n";

    fn load_type(import: &str, caller: &Path) -> String {
        let statement = Parser::new(import).parse().unwrap().items.into_iter().find_map(|node| match node {
            Node::UseStmt(statement) => Some(statement), _ => None,
        }).expect("use fixture");
        let value = crate::interpreter::interpreter_module::load_and_merge_module(
            &statement, Some(caller), &mut HashMap::new(), &mut HashMap::new(), &mut HashMap::new(),
        ).expect("actual loader route");
        let Value::EnumType { enum_name } = value else { panic!("import did not return enum type") };
        enum_name
    }

    #[test]
    fn actual_loader_elects_selected_provider_and_rejects_suffix_impostor() {
        clear_module_cache();
        crate::interpreter::clear_interpreter_state();
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        let standard = root.join("src/lib/core/option.spl");
        let application = root.join("app/fake/src/lib/core/option.spl");
        for path in [&standard, &application] {
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, OPTION).unwrap();
        }
        let caller = root.join("src/main.spl");
        std::fs::write(&caller, "# importer\n").unwrap();
        assert_eq!(load_type("use std.core.option.Option\n", &caller), "Option");
        let custom = load_type("use app.fake.src.lib.core.option.Option\n", &caller);
        assert!(custom.starts_with(crate::interpreter::FLATTEN_OWNER_SYMBOL_PREFIX));
        assert!(crate::codegen::shared::enum_runtime_type_id(&custom) > 1);
        clear_module_cache();
        crate::interpreter::clear_interpreter_state();
    }

    #[test]
    fn actual_loader_elects_displaced_family_provider_without_suffix_inference() {
        clear_module_cache();
        crate::interpreter::clear_interpreter_state();
        let temp = tempfile::tempdir().unwrap();
        let provider = temp.path().join("src/lib/common/core/option.spl");
        std::fs::create_dir_all(provider.parent().unwrap()).unwrap();
        std::fs::write(&provider, OPTION).unwrap();
        let caller = temp.path().join("src/main.spl");
        std::fs::write(&caller, "# importer\n").unwrap();
        assert_eq!(load_type("use std.core.option.Option\n", &caller), "Option");
        clear_module_cache();
        crate::interpreter::clear_interpreter_state();
    }

    #[test]
    fn warm_module_provider_conflict_is_rejected_before_registry_merge() {
        clear_module_cache();
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("option.spl");
        std::fs::write(&path, OPTION).unwrap();
        let mut ast = Parser::new(OPTION).parse().unwrap();
        mark_selected_builtin_enum_origins(&mut ast.items, &path, |_| Some(path.clone()));
        let def = ast.items.into_iter().find_map(|node| match node { Node::Enum(def) => Some(Arc::new(def)), _ => None }).unwrap();
        let definitions = HashMap::from([("Option".into(), Arc::clone(&def))]);
        cache_module_definitions(&path, &HashMap::new(), &HashMap::new(), &definitions);
        assert!(check_cached_builtin_enum_origins(&path, Path::new("/provider-a/main.spl"), |_| Some(path.clone())).is_ok());
        let error = check_cached_builtin_enum_origins(&path, Path::new("/provider-b/main.spl"), |_| None).unwrap_err();
        assert!(error.to_string().contains("provider conflict"));
        assert!(Arc::ptr_eq(cached_module_enums(&path).unwrap().get("Option").unwrap(), &def));
        let facade = temp.path().join("facade.spl");
        std::fs::write(&facade, "# facade\n").unwrap();
        cache_module_definitions(&facade, &HashMap::new(), &HashMap::new(), &definitions);
        assert!(check_cached_builtin_enum_origins(&facade, Path::new("/provider-b/main.spl"), |_| None).is_ok(),
            "a facade cache container must not re-elect its imported enum's provider");
        clear_module_cache();
    }

    #[test]
    fn source_attribute_identifier_cannot_spell_trusted_nul_marker() {
        let ast = Parser::new("@simple_selected_builtin_enum_origin\nenum Option<T>:\n    Some(value: T)\n    None\n").parse();
        // Source decorators may be rejected on enums; if accepted, their
        // identifier remains ordinary source spelling and cannot elect origin.
        if let Ok(ast) = ast {
            for node in ast.items {
                if let Node::Enum(def) = node {
                    assert!(def.attributes.iter().all(|a| !a.name.starts_with(SELECTED_BUILTIN_ENUM_ORIGIN)));
                }
            }
        }
        assert!(SELECTED_BUILTIN_ENUM_ORIGIN.starts_with('\0'));
    }
}
