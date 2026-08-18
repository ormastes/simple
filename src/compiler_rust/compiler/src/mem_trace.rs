//! Lightweight, always-compiled allocation accounting used to diagnose
//! interpreter memory blowups (native-build worker OOM, 12.5 GB peak RSS while
//! compiling a 3-line file).
//!
//! Design notes / why it looks like this:
//!
//! * ptrace-based attach profiling (perf, gdb, heaptrack) is BLOCKED on the
//!   build hosts (`kernel.yama.ptrace_scope=1`, `perf_event_paranoid=4`), so
//!   the profile has to be produced by the process itself.
//! * The counters are maintained unconditionally (two relaxed atomics per
//!   allocation) so that no env var has to be set before the interesting
//!   allocation happens. Only the *reporting* is gated, behind
//!   `SIMPLE_MEM_TRACE=1`, matching the existing `SIMPLE_LOADER_TRACE` pattern.
//! * Attribution is *self* (exclusive) bytes: a module-load scope subtracts the
//!   bytes retained by the nested module loads it triggered, so a leaf module
//!   that retains 8 MB is visible instead of being hidden inside its root.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

// ---------------------------------------------------------------------------
// Global allocator wrapper
// ---------------------------------------------------------------------------

/// Currently-live heap bytes (allocated minus deallocated).
pub static LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);
/// High-water mark of `LIVE_BYTES`.
pub static PEAK_BYTES: AtomicUsize = AtomicUsize::new(0);
/// Total number of allocation calls since process start.
pub static TOTAL_ALLOCS: AtomicU64 = AtomicU64::new(0);
/// Total bytes ever requested (never decremented).
pub static TOTAL_BYTES: AtomicU64 = AtomicU64::new(0);

/// A `GlobalAlloc` that forwards to an inner allocator while maintaining the
/// counters above. Overhead is a handful of relaxed atomic ops per allocation;
/// it perturbs wall-clock timing slightly but not peak-RSS attribution.
///
/// Generic over the inner allocator on purpose: the driver's default allocator
/// is mimalloc, and wrapping the *real* allocator keeps RSS behaviour faithful
/// (swapping in `System` would change the measurement being explained).
pub struct TrackingAlloc<A = System>(pub A);

impl<A> TrackingAlloc<A> {
    /// Wrap `inner` with allocation accounting.
    pub const fn new(inner: A) -> Self {
        TrackingAlloc(inner)
    }
}

#[inline]
fn on_alloc(size: usize) {
    TOTAL_ALLOCS.fetch_add(1, Ordering::Relaxed);
    TOTAL_BYTES.fetch_add(size as u64, Ordering::Relaxed);
    let live = LIVE_BYTES.fetch_add(size, Ordering::Relaxed) + size;
    PEAK_BYTES.fetch_max(live, Ordering::Relaxed);
}

#[inline]
fn on_dealloc(size: usize) {
    LIVE_BYTES.fetch_sub(size, Ordering::Relaxed);
}

unsafe impl<A: GlobalAlloc> GlobalAlloc for TrackingAlloc<A> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { self.0.alloc(layout) };
        if !p.is_null() {
            on_alloc(layout.size());
        }
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        on_dealloc(layout.size());
        unsafe { self.0.dealloc(ptr, layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { self.0.alloc_zeroed(layout) };
        if !p.is_null() {
            on_alloc(layout.size());
        }
        p
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let p = unsafe { self.0.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            on_dealloc(layout.size());
            on_alloc(new_size);
        }
        p
    }
}

/// Currently-live heap bytes.
pub fn live() -> usize {
    LIVE_BYTES.load(Ordering::Relaxed)
}

/// High-water mark of live heap bytes.
pub fn peak() -> usize {
    PEAK_BYTES.load(Ordering::Relaxed)
}

/// Resident set size in bytes, read from `/proc/self/statm` (Linux only).
pub fn rss_bytes() -> usize {
    #[cfg(target_os = "linux")]
    {
        if let Ok(s) = std::fs::read_to_string("/proc/self/statm") {
            if let Some(pages) = s.split_whitespace().nth(1) {
                if let Ok(p) = pages.parse::<usize>() {
                    return p * 4096;
                }
            }
        }
    }
    0
}

// ---------------------------------------------------------------------------
// Reporting gate
// ---------------------------------------------------------------------------

/// True when `SIMPLE_MEM_TRACE=1` (or `true`).
pub fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("SIMPLE_MEM_TRACE")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}

// ---------------------------------------------------------------------------
// captured_env_with_live_globals accounting (target #2)
// ---------------------------------------------------------------------------

/// Number of `captured_env_with_live_globals` invocations.
pub static CEWLG_CALLS: AtomicU64 = AtomicU64::new(0);
/// Total entries materialised into the fresh `base` map across all invocations.
pub static CEWLG_BASE_ENTRIES: AtomicU64 = AtomicU64::new(0);
/// Sum of net live-byte deltas across invocations (i.e. bytes NOT freed by the
/// time the function returned -- retained, not transient).
pub static CEWLG_NET_BYTES: AtomicU64 = AtomicU64::new(0);
/// Sum of gross live-byte deltas measured at peak inside the invocation.
pub static CEWLG_GROSS_BYTES: AtomicU64 = AtomicU64::new(0);

/// Record one `captured_env_with_live_globals` invocation.
pub fn record_captured_env(base_entries: usize, net_bytes: i64, gross_bytes: i64) {
    if !enabled() {
        return;
    }
    CEWLG_CALLS.fetch_add(1, Ordering::Relaxed);
    CEWLG_BASE_ENTRIES.fetch_add(base_entries as u64, Ordering::Relaxed);
    if net_bytes > 0 {
        CEWLG_NET_BYTES.fetch_add(net_bytes as u64, Ordering::Relaxed);
    }
    if gross_bytes > 0 {
        CEWLG_GROSS_BYTES.fetch_add(gross_bytes as u64, Ordering::Relaxed);
    }
}

fn mb(bytes: usize) -> f64 {
    bytes as f64 / (1024.0 * 1024.0)
}

// ---------------------------------------------------------------------------
// Phase / per-module accounting
// ---------------------------------------------------------------------------

#[derive(Default, Clone, Copy)]
struct ModuleCost {
    /// Bytes still live at scope exit that this module retained itself,
    /// excluding bytes retained by nested module loads.
    self_bytes: i64,
    /// Bytes retained by parsing this module's source into an AST.
    parse_bytes: i64,
    /// Source length in bytes.
    source_bytes: usize,
    /// Top-level AST items after cfg-stripping.
    ast_items: usize,
    /// How many times this module went through a full (non-cached) load.
    loads: u32,
    /// Entries in the module's filtered (visible-name) environment.
    env_entries: usize,
    /// Entries in the module's export map.
    export_entries: usize,
}

#[derive(Default)]
struct PhaseTotals {
    parse: i64,
    eval: i64,
    modules: u64,
    source_bytes: u64,
    ast_items: u64,
    env_entries: u64,
    export_entries: u64,
}

thread_local! {
    /// Stack of (live_bytes_at_enter, bytes_retained_by_children) for nested loads.
    static SCOPE_STACK: RefCell<Vec<(usize, i64)>> = const { RefCell::new(Vec::new()) };
    static MODULE_COSTS: RefCell<HashMap<String, ModuleCost>> = RefCell::new(HashMap::new());
    static PHASES: RefCell<PhaseTotals> = RefCell::new(PhaseTotals::default());
}

/// Push a module-load accounting scope. Paired with [`exit_module`].
pub fn enter_module() {
    if !enabled() {
        return;
    }
    SCOPE_STACK.with(|s| s.borrow_mut().push((live(), 0)));
}

/// Record the bytes retained by parsing `source` into `ast_items` top-level
/// nodes, measured as the live-bytes delta the caller observed across the parse.
pub fn record_parse(module: &str, delta: i64, source_bytes: usize, ast_items: usize) {
    if !enabled() {
        return;
    }
    MODULE_COSTS.with(|m| {
        let mut m = m.borrow_mut();
        let e = m.entry(module.to_string()).or_default();
        e.parse_bytes += delta;
        e.source_bytes = source_bytes;
        e.ast_items = ast_items;
    });
    PHASES.with(|p| {
        let mut p = p.borrow_mut();
        p.parse += delta;
        p.source_bytes += source_bytes as u64;
        p.ast_items += ast_items as u64;
    });
}

/// Record how wide a module's materialised environment and export map are.
/// These are the maps that get copied per module, so their entry counts are
/// what turns a small source file into megabytes of retained interpreter state.
pub fn record_env(module: &str, env_entries: usize, export_entries: usize) {
    if !enabled() {
        return;
    }
    MODULE_COSTS.with(|m| {
        let mut m = m.borrow_mut();
        let e = m.entry(module.to_string()).or_default();
        e.env_entries = env_entries;
        e.export_entries = export_entries;
    });
    PHASES.with(|p| {
        let mut p = p.borrow_mut();
        p.env_entries += env_entries as u64;
        p.export_entries += export_entries as u64;
    });
}

/// Pop the accounting scope opened by [`enter_module`] and attribute the
/// exclusive (self) retained bytes to `module`.
pub fn exit_module(module: &str) {
    if !enabled() {
        return;
    }
    let now = live();
    let (start, children) = match SCOPE_STACK.with(|s| s.borrow_mut().pop()) {
        Some(v) => v,
        None => return,
    };
    let total = now as i64 - start as i64;
    let self_bytes = total - children;
    // Propagate the inclusive delta to the parent scope, if any.
    SCOPE_STACK.with(|s| {
        if let Some(parent) = s.borrow_mut().last_mut() {
            parent.1 += total;
        }
    });
    MODULE_COSTS.with(|m| {
        let mut m = m.borrow_mut();
        let e = m.entry(module.to_string()).or_default();
        e.self_bytes += self_bytes;
        e.loads += 1;
    });
    let n = PHASES.with(|p| {
        let mut p = p.borrow_mut();
        p.eval += self_bytes;
        p.modules += 1;
        p.modules
    });
    // Periodic output so an OOM-aborted run still leaves a usable trace: the
    // abort never reaches a normal shutdown hook, so the report has to be
    // emitted incrementally rather than once at the end.
    if n % 100 == 0 {
        snapshot(&format!("after {n} module loads"));
    }
    if n % 500 == 0 {
        report_inner(&format!("after {n} module loads"));
    }
}

/// RAII wrapper around [`enter_module`] / [`exit_module`] so that every early
/// return out of the loader is still accounted for.
pub struct ModuleScope(Option<String>);

impl ModuleScope {
    /// Open an accounting scope for `module`. A no-op unless tracing is on.
    pub fn enter(module: &std::path::Path) -> Self {
        if !enabled() {
            return ModuleScope(None);
        }
        enter_module();
        ModuleScope(Some(module.display().to_string()))
    }
}

impl Drop for ModuleScope {
    fn drop(&mut self) {
        if let Some(name) = self.0.take() {
            exit_module(&name);
        }
    }
}

/// Print a one-line snapshot of the global counters, tagged with `label`.
pub fn snapshot(label: &str) {
    if !enabled() {
        return;
    }
    eprintln!(
        "[mem] {label} live={:.1}MB peak={:.1}MB rss={:.1}MB allocs={} total_alloc={:.1}MB",
        mb(live()),
        mb(peak()),
        mb(rss_bytes()),
        TOTAL_ALLOCS.load(Ordering::Relaxed),
        TOTAL_BYTES.load(Ordering::Relaxed) as f64 / (1024.0 * 1024.0),
    );
}

/// Print the full per-phase and per-module attribution report.
pub fn report(label: &str) {
    report_inner(label)
}

fn report_inner(label: &str) {
    if !enabled() {
        return;
    }
    snapshot(label);
    let (parse, eval, modules, src, items, envs, exports) = PHASES.with(|p| {
        let p = p.borrow();
        (
            p.parse,
            p.eval,
            p.modules,
            p.source_bytes,
            p.ast_items,
            p.env_entries,
            p.export_entries,
        )
    });
    eprintln!(
        "[mem] phases: module_loads={modules} source={:.1}MB ast_items={items} \
         parse_retained={:.1}MB eval_retained={:.1}MB parse_bytes_per_source_byte={:.1} \
         env_entries={envs} export_entries={exports}",
        src as f64 / (1024.0 * 1024.0),
        parse as f64 / (1024.0 * 1024.0),
        eval as f64 / (1024.0 * 1024.0),
        if src > 0 { parse as f64 / src as f64 } else { 0.0 },
    );

    let c = CEWLG_CALLS.load(Ordering::Relaxed);
    eprintln!(
        "[mem] captured_env_with_live_globals: calls={c} base_entries={} avg_width={:.1} \
         net_retained={:.1}MB gross={:.1}MB",
        CEWLG_BASE_ENTRIES.load(Ordering::Relaxed),
        if c > 0 {
            CEWLG_BASE_ENTRIES.load(Ordering::Relaxed) as f64 / c as f64
        } else {
            0.0
        },
        CEWLG_NET_BYTES.load(Ordering::Relaxed) as f64 / (1024.0 * 1024.0),
        CEWLG_GROSS_BYTES.load(Ordering::Relaxed) as f64 / (1024.0 * 1024.0),
    );
    let mut rows: Vec<(String, ModuleCost)> =
        MODULE_COSTS.with(|m| m.borrow().iter().map(|(k, v)| (k.clone(), *v)).collect());
    rows.sort_by_key(|(_, c)| -(c.self_bytes + c.parse_bytes));
    eprintln!("[mem] top 30 modules by retained bytes (self + parse):");
    for (name, c) in rows.iter().take(30) {
        eprintln!(
            "[mem]   {:>9.2}MB self  {:>9.2}MB parse  src={:>7}B items={:>4} env={:>6} exp={:>6} loads={} {}",
            c.self_bytes as f64 / (1024.0 * 1024.0),
            c.parse_bytes as f64 / (1024.0 * 1024.0),
            c.source_bytes,
            c.ast_items,
            c.env_entries,
            c.export_entries,
            c.loads,
            name,
        );
    }
}
