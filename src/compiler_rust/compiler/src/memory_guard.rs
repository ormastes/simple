//! Memory Guard Framework — unified prevention for interpreter memory explosion.
//!
//! Consolidates RSS tracking, module loading budgets, SIMPLE_LIB scope validation,
//! and diagnostics into a single cohesive API. See `doc/04_architecture/memory_rules.md`.
//!
//! # Usage
//! ```rust,no_run
//! use simple_compiler::memory_guard::{MemoryGuard, ModuleLoadGuard};
//! use std::path::Path;
//!
//! // Initialize once at startup
//! MemoryGuard::init();
//!
//! // Per-module load tracking
//! let guard = ModuleLoadGuard::enter(Path::new("path/to/module.spl"));
//! // ... load module ...
//! guard.exit(); // records RSS delta, warns if threshold exceeded
//! ```

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::OnceLock;

// Re-export core watchdog functions
pub use crate::watchdog::{read_rss_bytes, start_watchdog, stop_watchdog};

// ---------------------------------------------------------------------------
// Configuration — all env-var reads cached via OnceLock
// ---------------------------------------------------------------------------

/// RSS limit in bytes (0 = disabled). Read from SIMPLE_MEMORY_LIMIT_MB.
pub fn memory_limit_bytes() -> u64 {
    crate::watchdog::memory_limit_bytes()
}

/// Per-module RSS warning threshold in bytes (0 = disabled).
/// Read from SIMPLE_MODULE_RSS_WARN_MB.
fn module_rss_warn_bytes() -> u64 {
    static WARN: OnceLock<u64> = OnceLock::new();
    *WARN.get_or_init(|| {
        std::env::var("SIMPLE_MODULE_RSS_WARN_MB")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .unwrap_or(0)
            * 1024
            * 1024
    })
}

/// Maximum modules that can be loaded (0 = unlimited).
/// Read from SIMPLE_MODULE_LIMIT.
pub fn module_limit() -> usize {
    static LIMIT: OnceLock<usize> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        std::env::var("SIMPLE_MODULE_LIMIT")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(800) // default from module_cache.rs MAX_TOTAL_MODULES
    })
}

/// Maximum sibling files to preload per __init__.spl.
/// Read from SIMPLE_SIBLING_PRELOAD_LIMIT.
pub fn sibling_preload_limit() -> usize {
    static LIMIT: OnceLock<usize> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        std::env::var("SIMPLE_SIBLING_PRELOAD_LIMIT")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(20)
    })
}

/// Maximum file size (bytes) for sibling name-matching check.
pub fn sibling_max_check_bytes() -> u64 {
    static LIMIT: OnceLock<u64> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        std::env::var("SIMPLE_SIBLING_MAX_CHECK_KB")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .map(|kb| kb * 1024)
            .unwrap_or(50 * 1024) // 50KB default
    })
}

/// Whether diagnostics/stats collection is enabled.
/// Read from SIMPLE_LOADER_TRACE.
pub fn stats_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("SIMPLE_LOADER_TRACE")
            .map(|v| v != "0" && !v.is_empty())
            .unwrap_or(false)
    })
}

// ---------------------------------------------------------------------------
// SIMPLE_LIB Scope Validation
// ---------------------------------------------------------------------------

static LIB_VALIDATED: OnceLock<()> = OnceLock::new();

/// Warn if SIMPLE_LIB contains >500 .spl files (misconfiguration indicator).
/// Runs at most once per process.
pub fn validate_lib_scope() {
    LIB_VALIDATED.get_or_init(|| {
        if let Ok(lib_path) = std::env::var("SIMPLE_LIB") {
            let path = Path::new(&lib_path);
            if path.is_dir() {
                let mut count = 0u32;
                count_spl_files(path, &mut count, 600);
                if count > 500 {
                    eprintln!(
                        "[memory-guard] SIMPLE_LIB={} contains {}+ .spl files — \
                         consider narrowing scope to avoid memory bloat",
                        lib_path, count
                    );
                }
            }
        }
    });
}

fn count_spl_files(dir: &Path, count: &mut u32, max: u32) {
    if *count >= max {
        return;
    }
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        if *count >= max {
            return;
        }
        let path = entry.path();
        if path.is_dir() {
            count_spl_files(&path, count, max);
        } else if path.extension().map_or(false, |e| e == "spl") {
            *count += 1;
        }
    }
}

// ---------------------------------------------------------------------------
// MemoryGuard — one-time initialization
// ---------------------------------------------------------------------------

static INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Central entry point — call once at interpreter startup.
/// Runs SIMPLE_LIB validation and initializes stats collection.
pub struct MemoryGuard;

impl MemoryGuard {
    /// Initialize all memory guards. Idempotent.
    pub fn init() {
        if INITIALIZED.swap(true, Ordering::SeqCst) {
            return; // already initialized
        }
        validate_lib_scope();
    }
}

// ---------------------------------------------------------------------------
// ModuleLoadGuard — RAII per-module RSS tracking
// ---------------------------------------------------------------------------

/// RAII guard that tracks RSS delta during module loading.
/// Created via `ModuleLoadGuard::enter()`, records delta on `exit()` or drop.
pub struct ModuleLoadGuard {
    path: PathBuf,
    rss_before: u64,
    start: std::time::Instant,
    exited: bool,
}

impl ModuleLoadGuard {
    /// Start tracking a module load. Captures current RSS.
    pub fn enter(path: &Path) -> Self {
        Self {
            path: path.to_owned(),
            rss_before: read_rss_bytes(),
            start: std::time::Instant::now(),
            exited: false,
        }
    }

    /// Finish tracking. Returns RSS delta in bytes (positive = growth).
    pub fn exit(mut self) -> i64 {
        self.exited = true;
        self.record_delta()
    }

    fn record_delta(&self) -> i64 {
        let rss_after = read_rss_bytes();
        let delta = rss_after as i64 - self.rss_before as i64;
        let elapsed_us = self.start.elapsed().as_micros();

        // Record to global stats if enabled
        if stats_enabled() {
            GUARD_STATS.with(|stats| {
                let mut s = stats.borrow_mut();
                s.rss_deltas.insert(self.path.clone(), delta);
                s.eval_times.insert(self.path.clone(), elapsed_us);
                s.total_modules += 1;
            });
        }

        // Warn if single module exceeds threshold
        let warn_bytes = module_rss_warn_bytes();
        if warn_bytes > 0 && delta > warn_bytes as i64 {
            eprintln!(
                "[memory-guard] module {} added {}MB RSS (threshold: {}MB)",
                self.path.display(),
                delta / 1024 / 1024,
                warn_bytes / 1024 / 1024,
            );
        }

        delta
    }
}

impl Drop for ModuleLoadGuard {
    fn drop(&mut self) {
        if !self.exited {
            self.record_delta();
        }
    }
}

// ---------------------------------------------------------------------------
// GuardStats — thread-local diagnostics collection
// ---------------------------------------------------------------------------

/// Accumulated stats from all module loads in this thread.
pub struct GuardStats {
    pub rss_deltas: HashMap<PathBuf, i64>,
    pub eval_times: HashMap<PathBuf, u128>,
    pub total_modules: usize,
}

impl GuardStats {
    fn new() -> Self {
        Self {
            rss_deltas: HashMap::new(),
            eval_times: HashMap::new(),
            total_modules: 0,
        }
    }
}

thread_local! {
    static GUARD_STATS: std::cell::RefCell<GuardStats> =
        std::cell::RefCell::new(GuardStats::new());
}

// ---------------------------------------------------------------------------
// Diagnostics reporting
// ---------------------------------------------------------------------------

/// Accumulated peak RSS across the process.
static PEAK_RSS: AtomicU64 = AtomicU64::new(0);

/// Update peak RSS tracker. Call periodically or after heavy operations.
pub fn update_peak_rss() {
    let current = read_rss_bytes();
    PEAK_RSS.fetch_max(current, Ordering::Relaxed);
}

/// Get peak RSS observed so far (bytes).
pub fn peak_rss_bytes() -> u64 {
    PEAK_RSS.load(Ordering::Relaxed)
}

/// Print a summary of memory diagnostics to stderr.
/// Only outputs when `stats_enabled()` returns true.
pub fn print_diagnostics() {
    if !stats_enabled() {
        return;
    }

    let current_rss = read_rss_bytes();
    update_peak_rss();

    eprintln!("\n=== Memory Guard Diagnostics ===");
    eprintln!(
        "Current RSS: {}MB  Peak RSS: {}MB  Limit: {}MB",
        current_rss / 1024 / 1024,
        peak_rss_bytes() / 1024 / 1024,
        memory_limit_bytes() / 1024 / 1024,
    );

    GUARD_STATS.with(|stats| {
        let s = stats.borrow();
        eprintln!("Total modules loaded: {}", s.total_modules);

        // Top RSS consumers
        let mut deltas: Vec<_> = s.rss_deltas.iter().collect();
        deltas.sort_by(|a, b| b.1.abs().cmp(&a.1.abs()));
        if !deltas.is_empty() {
            eprintln!("\nTop RSS consumers:");
            for (path, delta) in deltas.iter().take(10) {
                let time = s.eval_times.get(*path).copied().unwrap_or(0);
                eprintln!("  {:+6}KB  {:>6}us  {}", *delta / 1024, time, path.display());
            }
        }
    });
    eprintln!("================================\n");
}

/// Reset all collected stats (call between test files to prevent accumulation).
pub fn reset_stats() {
    GUARD_STATS.with(|stats| {
        let mut s = stats.borrow_mut();
        s.rss_deltas.clear();
        s.eval_times.clear();
        s.total_modules = 0;
    });
    PEAK_RSS.store(0, Ordering::Relaxed);
}

// ---------------------------------------------------------------------------
// Budget assertions — for use in tests and CI
// ---------------------------------------------------------------------------

/// Assert that current RSS is under the given limit (in MB).
/// Returns `Ok(current_mb)` or `Err(message)`.
pub fn assert_rss_under_mb(limit_mb: u64) -> Result<u64, String> {
    let current = read_rss_bytes();
    let current_mb = current / 1024 / 1024;
    if current_mb > limit_mb {
        Err(format!("RSS {}MB exceeds limit {}MB", current_mb, limit_mb))
    } else {
        Ok(current_mb)
    }
}

/// Assert that a module load did not exceed the given RSS delta (in MB).
pub fn assert_module_delta_under_mb(path: &Path, limit_mb: i64) -> Result<i64, String> {
    let delta_kb = GUARD_STATS.with(|stats| stats.borrow().rss_deltas.get(path).copied().unwrap_or(0));
    let delta_mb = delta_kb / 1024 / 1024;
    if delta_mb > limit_mb {
        Err(format!(
            "Module {} added {}MB RSS (limit: {}MB)",
            path.display(),
            delta_mb,
            limit_mb
        ))
    } else {
        Ok(delta_mb)
    }
}
