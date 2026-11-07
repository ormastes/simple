//! Level-gated sampling profiler for the AST interpreter (default OFF).
//!
//! `perf` is unavailable on the dev hosts (`perf_event_paranoid=4`,
//! `ptrace_scope=1`; no elevation for `wpr` on the Windows hosts), so this is
//! the in-process substitute: enable with `SIMPLE_INTERP_SAMPLE=1` and every
//! 10 ms (`SIMPLE_INTERP_SAMPLE_US` to override) a tick records
//!
//!   * the innermost interpreted Simple function (self time),
//!   * every distinct function on the interpreted call stack (inclusive time),
//!   * the innermost `Expr` kind being dispatched by `evaluate_expr`.
//!
//! Tick source per platform:
//!   * Unix: an `ITIMER_PROF` SIGPROF handler — CPU-time sampling of the
//!     interpreter thread.
//!   * Everything else (Windows): a timer THREAD that sleeps the interval and
//!     reads the same atomics — wall-time sampling. A blocked interpreter
//!     thread (I/O, waiting on a child) is then charged to whatever frame it
//!     is blocked in, where SIGPROF would not have ticked at all. The report
//!     names which source produced it (`tick: cpu` / `tick: wall`).
//!
//! The tick is async-signal-safe: it only touches fixed-size static atomics
//! (an open-addressed table keyed by interned name pointer). Aggregation and
//! rendering happen at exit (`atexit`), written to stderr or
//! `SIMPLE_INTERP_SAMPLE_OUT` (pid-suffixed so forked test children don't
//! clobber each other).
//!
//! When disabled the cost on every function entry and every expression
//! dispatch is one relaxed atomic load + branch.

use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::Mutex;

const UNKNOWN: u8 = 0;
const OFF: u8 = 1;
const ON: u8 = 2;
static STATE: AtomicU8 = AtomicU8::new(UNKNOWN);
static ATEXIT_REGISTERED: AtomicBool = AtomicBool::new(false);

/// Max interpreted call depth tracked for inclusive attribution.
const STACK_CAP: usize = 4096;
/// Open-addressed table size (power of two). Interned-name pointer keyed.
const TABLE_CAP: usize = 1 << 15;
/// Expr-kind slots: keyed by the `&'static str` pointer from `dispatch_profile::expr_kind`.
const KIND_CAP: usize = 128;

struct Slot {
    key: AtomicPtr<u8>,
    len: AtomicUsize,
    self_hits: AtomicU64,
    incl_hits: AtomicU64,
}

#[allow(clippy::declare_interior_mutable_const)] // reason: array initialiser for statics
const EMPTY_SLOT: Slot = Slot {
    key: AtomicPtr::new(std::ptr::null_mut()),
    len: AtomicUsize::new(0),
    self_hits: AtomicU64::new(0),
    incl_hits: AtomicU64::new(0),
};

static FRAMES: [Slot; TABLE_CAP] = [EMPTY_SLOT; TABLE_CAP];
static KINDS: [Slot; KIND_CAP] = [EMPTY_SLOT; KIND_CAP];

/// Interpreted call stack: (interned name ptr, len). Written by the
/// interpreter thread, read by the signal handler.
static STACK_PTR: [AtomicPtr<u8>; STACK_CAP] = [const { AtomicPtr::new(std::ptr::null_mut()) }; STACK_CAP];
static STACK_LEN: [AtomicUsize; STACK_CAP] = [const { AtomicUsize::new(0) }; STACK_CAP];
static DEPTH: AtomicUsize = AtomicUsize::new(0);
/// Innermost expr kind currently being dispatched (ptr/len of a &'static str).
static CUR_KIND_PTR: AtomicPtr<u8> = AtomicPtr::new(std::ptr::null_mut());
static CUR_KIND_LEN: AtomicUsize = AtomicUsize::new(0);

static TOTAL_SAMPLES: AtomicU64 = AtomicU64::new(0);
static DROPPED_SAMPLES: AtomicU64 = AtomicU64::new(0);
static IDLE_SAMPLES: AtomicU64 = AtomicU64::new(0);

/// Leaked interned names so the handler never sees a dangling pointer: a
/// `FunctionDef` for a lambda can be transient, its `name` String freed before
/// exit. Only touched when the sampler is ON.
static INTERN: Mutex<Option<HashSet<&'static str>>> = Mutex::new(None);

#[inline(always)]
pub fn enabled() -> bool {
    match STATE.load(Ordering::Relaxed) {
        OFF => false,
        ON => true,
        _ => init(),
    }
}

#[cold]
fn init() -> bool {
    let on = std::env::var("SIMPLE_INTERP_SAMPLE").is_ok_and(|v| !v.is_empty() && v != "0");
    if on && !ATEXIT_REGISTERED.swap(true, Ordering::Relaxed) {
        *INTERN.lock().unwrap() = Some(HashSet::new());
        let us: i64 = std::env::var("SIMPLE_INTERP_SAMPLE_US")
            .ok()
            .and_then(|v| v.parse().ok())
            .filter(|v: &i64| *v >= 100)
            .unwrap_or(10_000);
        #[cfg(unix)]
        unsafe {
            let mut sa: libc::sigaction = std::mem::zeroed();
            sa.sa_sigaction = on_sigprof as usize;
            sa.sa_flags = libc::SA_RESTART | libc::SA_SIGINFO;
            libc::sigemptyset(&mut sa.sa_mask);
            libc::sigaction(libc::SIGPROF, &sa, std::ptr::null_mut());
            let tv = libc::timeval {
                tv_sec: us / 1_000_000,
                tv_usec: (us % 1_000_000) as libc::suseconds_t,
            };
            let it = libc::itimerval {
                it_interval: tv,
                it_value: tv,
            };
            libc::setitimer(libc::ITIMER_PROF, &it, std::ptr::null_mut());
            libc::atexit(dump_at_exit);
        }
        // No SIGPROF/setitimer here (and `libc` is a cfg(unix)-only dependency
        // of this crate). The tick comes from a timer thread instead: the
        // sampled state is all process-global atomics written by the
        // interpreter thread, so a second thread reading them with Acquire
        // ordering sees a consistent (depth, frames) pair exactly as the
        // signal handler does. `atexit` is standard C and the MSVC CRT
        // exports it, declared directly as perf_counters.rs does. Until this
        // port the Windows arm only printed a warning and recorded nothing —
        // the ".claude/rules/commands.md: SIMPLE_INTERP_SAMPLE emits NOTHING"
        // trap; now the report says `tick: wall` so a reader knows what was
        // sampled.
        #[cfg(not(unix))]
        {
            extern "C" {
                fn atexit(cb: extern "C" fn()) -> i32;
            }
            // SAFETY: `dump_at_exit` is `extern "C" fn()` and never unwinds.
            unsafe {
                atexit(dump_at_exit);
            }
            TICK_THREAD_RUNNING.store(true, Ordering::Release);
            let interval = std::time::Duration::from_micros(us as u64);
            std::thread::Builder::new()
                .name("simple-interp-sampler".into())
                .spawn(move || {
                    while TICK_THREAD_RUNNING.load(Ordering::Acquire) {
                        std::thread::sleep(interval);
                        take_sample();
                    }
                })
                .expect("spawn interpreter sampler tick thread");
        }
    }
    STATE.store(if on { ON } else { OFF }, Ordering::Relaxed);
    on
}

/// Set while the non-Unix timer thread should keep ticking; cleared by
/// `dump_at_exit` so no tick lands while the tables are being rendered.
#[cfg(not(unix))]
static TICK_THREAD_RUNNING: AtomicBool = AtomicBool::new(false);

#[cfg(unix)]
const TICK_SOURCE: &str = "cpu";
#[cfg(not(unix))]
const TICK_SOURCE: &str = "wall";

fn intern(name: &str) -> &'static str {
    let mut g = INTERN.lock().unwrap();
    let set = g.get_or_insert_with(HashSet::new);
    if let Some(s) = set.get(name) {
        return s;
    }
    let leaked: &'static str = Box::leak(name.to_string().into_boxed_str());
    set.insert(leaked);
    leaked
}

/// RAII frame: pushes the function name on entry, pops on drop.
pub struct Frame(bool);

impl Frame {
    #[inline(always)]
    pub fn enter(name: &str) -> Frame {
        if !enabled() {
            return Frame(false);
        }
        Self::enter_slow(name)
    }

    #[cold]
    fn enter_slow(name: &str) -> Frame {
        let s = intern(name);
        let d = DEPTH.load(Ordering::Relaxed);
        if d >= STACK_CAP {
            return Frame(false);
        }
        STACK_PTR[d].store(s.as_ptr() as *mut u8, Ordering::Relaxed);
        STACK_LEN[d].store(s.len(), Ordering::Relaxed);
        DEPTH.store(d + 1, Ordering::Release);
        Frame(true)
    }
}

impl Drop for Frame {
    #[inline(always)]
    fn drop(&mut self) {
        if self.0 {
            DEPTH.fetch_sub(1, Ordering::Release);
        }
    }
}

/// RAII expr-kind marker for `evaluate_expr`. Restores the enclosing kind on
/// drop so leaf dispatches don't permanently mask their parents.
pub struct KindGuard(Option<(*mut u8, usize)>);

impl KindGuard {
    #[inline(always)]
    pub fn enter(kind: &'static str) -> KindGuard {
        if !enabled() {
            return KindGuard(None);
        }
        let prev = (
            CUR_KIND_PTR.load(Ordering::Relaxed),
            CUR_KIND_LEN.load(Ordering::Relaxed),
        );
        CUR_KIND_PTR.store(kind.as_ptr() as *mut u8, Ordering::Relaxed);
        CUR_KIND_LEN.store(kind.len(), Ordering::Relaxed);
        KindGuard(Some(prev))
    }
}

impl Drop for KindGuard {
    #[inline(always)]
    fn drop(&mut self) {
        if let Some((p, l)) = self.0 {
            CUR_KIND_PTR.store(p, Ordering::Relaxed);
            CUR_KIND_LEN.store(l, Ordering::Relaxed);
        }
    }
}

#[inline(always)]
fn hash_ptr(p: *mut u8) -> usize {
    let x = p as usize as u64;
    (x.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 20) as usize
}

/// Find-or-insert `key` in `table`; async-signal-safe (atomics only).
fn bump(table: &'static [Slot], key: *mut u8, len: usize, incl: bool) -> bool {
    let mask = table.len() - 1;
    let mut i = hash_ptr(key) & mask;
    for _ in 0..64 {
        let slot = &table[i];
        let cur = slot.key.load(Ordering::Acquire);
        if cur == key
            || (cur.is_null()
                && slot
                    .key
                    .compare_exchange(std::ptr::null_mut(), key, Ordering::AcqRel, Ordering::Acquire)
                    .is_ok())
        {
            slot.len.store(len, Ordering::Relaxed);
            if incl {
                slot.incl_hits.fetch_add(1, Ordering::Relaxed);
            } else {
                slot.self_hits.fetch_add(1, Ordering::Relaxed);
            }
            return true;
        }
        i = (i + 1) & mask;
    }
    false
}

#[cfg(unix)]
extern "C" fn on_sigprof(_sig: libc::c_int, _info: *mut libc::siginfo_t, _ctx: *mut libc::c_void) {
    take_sample();
}

/// One tick: attribute the current interpreted stack and expr kind. Atomics
/// only — callable from a signal handler or from the timer thread.
fn take_sample() {
    TOTAL_SAMPLES.fetch_add(1, Ordering::Relaxed);
    let d = DEPTH.load(Ordering::Acquire).min(STACK_CAP);
    if d == 0 {
        IDLE_SAMPLES.fetch_add(1, Ordering::Relaxed);
    } else {
        let top = STACK_PTR[d - 1].load(Ordering::Relaxed);
        let top_len = STACK_LEN[d - 1].load(Ordering::Relaxed);
        if !top.is_null() && !bump(&FRAMES, top, top_len, false) {
            DROPPED_SAMPLES.fetch_add(1, Ordering::Relaxed);
        }
        // Inclusive: each distinct frame once (recursion must not double count).
        let mut i = d;
        while i > 0 {
            i -= 1;
            let p = STACK_PTR[i].load(Ordering::Relaxed);
            if p.is_null() {
                continue;
            }
            let mut dup = false;
            let mut j = i + 1;
            while j < d {
                if STACK_PTR[j].load(Ordering::Relaxed) == p {
                    dup = true;
                    break;
                }
                j += 1;
            }
            if !dup {
                bump(&FRAMES, p, STACK_LEN[i].load(Ordering::Relaxed), true);
            }
        }
    }
    let k = CUR_KIND_PTR.load(Ordering::Relaxed);
    if !k.is_null() {
        bump(&KINDS, k, CUR_KIND_LEN.load(Ordering::Relaxed), false);
    }
}

fn slot_name(s: &Slot) -> String {
    let p = s.key.load(Ordering::Acquire);
    let l = s.len.load(Ordering::Relaxed);
    if p.is_null() {
        return String::new();
    }
    // SAFETY: keys are interned/leaked `&'static str` (frames) or string
    // literals (kinds); both live for the whole process.
    unsafe { String::from_utf8_lossy(std::slice::from_raw_parts(p as *const u8, l)).into_owned() }
}

/// Render the histograms, most frequent first. Public so specs can assert on it.
pub fn render() -> String {
    let total = TOTAL_SAMPLES.load(Ordering::Relaxed);
    let pct = |v: u64| {
        if total == 0 {
            0.0
        } else {
            v as f64 * 100.0 / total as f64
        }
    };
    let mut out = String::from("interp-sample-profile:\n");
    out.push_str(&format!(
        "  total_samples: {}  idle: {}  dropped: {}  tick: {}\n",
        total,
        IDLE_SAMPLES.load(Ordering::Relaxed),
        DROPPED_SAMPLES.load(Ordering::Relaxed),
        TICK_SOURCE
    ));
    let mut rows: Vec<(String, u64, u64)> = FRAMES
        .iter()
        .filter(|s| !s.key.load(Ordering::Acquire).is_null())
        .map(|s| {
            (
                slot_name(s),
                s.self_hits.load(Ordering::Relaxed),
                s.incl_hits.load(Ordering::Relaxed),
            )
        })
        .collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then(b.2.cmp(&a.2)).then(a.0.cmp(&b.0)));
    // `SIMPLE_INTERP_SAMPLE_ROWS=<n>` widens the table (default 60, which hid
    // every parse-entry row of a lint profile behind the lexer leaves);
    // `all` prints every sampled frame.
    let row_cap = match std::env::var("SIMPLE_INTERP_SAMPLE_ROWS") {
        Ok(v) if v == "all" => usize::MAX,
        Ok(v) => v.parse().unwrap_or(60),
        Err(_) => 60,
    };
    out.push_str("  frames (self / inclusive):\n");
    for (name, s, i) in rows.iter().take(row_cap) {
        out.push_str(&format!(
            "    {:>8} {:>6.2}%  {:>8} {:>6.2}%  {}\n",
            s,
            pct(*s),
            i,
            pct(*i),
            name
        ));
    }
    let mut kinds: Vec<(String, u64)> = KINDS
        .iter()
        .filter(|s| !s.key.load(Ordering::Acquire).is_null())
        .map(|s| (slot_name(s), s.self_hits.load(Ordering::Relaxed)))
        .collect();
    kinds.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    out.push_str("  expr kinds (innermost at sample):\n");
    for (name, s) in kinds.iter() {
        out.push_str(&format!("    {:>8} {:>6.2}%  {}\n", s, pct(*s), name));
    }
    out
}

extern "C" fn dump_at_exit() {
    flush_at_process_exit();
}

static DUMPED: AtomicBool = AtomicBool::new(false);

/// Stop ticking and write the report once. No-op unless the sampler is on.
/// Called from the `atexit` arm AND explicitly by the driver before its
/// terminal `std::process::exit`: on Windows that is `ExitProcess`, which
/// never runs CRT `atexit` handlers, so the report would otherwise be lost
/// exactly on the dominant CLI path (`lint`, `run`, `native-build`).
pub fn flush_at_process_exit() {
    if STATE.load(Ordering::Relaxed) != ON || DUMPED.swap(true, Ordering::Relaxed) {
        return;
    }
    #[cfg(unix)]
    unsafe {
        let zero = libc::timeval { tv_sec: 0, tv_usec: 0 };
        let it = libc::itimerval {
            it_interval: zero,
            it_value: zero,
        };
        libc::setitimer(libc::ITIMER_PROF, &it, std::ptr::null_mut());
    }
    #[cfg(not(unix))]
    TICK_THREAD_RUNNING.store(false, Ordering::Release);
    let text = render();
    match std::env::var("SIMPLE_INTERP_SAMPLE_OUT") {
        Ok(path) if !path.is_empty() => {
            let _ = std::fs::write(format!("{}.{}", path, std::process::id()), text);
        }
        _ => eprintln!("{}", text),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Both tests push onto the process-global sampler stack; serialise them so
    /// one test's frames never sit on top of the other's mid-sample.
    static TEST_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn frame_push_pop_and_table_bump_are_consistent() {
        let _serial = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Drive the table directly (no signal): interned keys aggregate by pointer.
        let a = intern("alpha_fn");
        let b = intern("alpha_fn");
        assert_eq!(a.as_ptr(), b.as_ptr(), "intern must dedupe by content");
        let key = a.as_ptr() as *mut u8;
        assert!(bump(&FRAMES, key, a.len(), false));
        assert!(bump(&FRAMES, key, a.len(), false));
        assert!(bump(&FRAMES, key, a.len(), true));
        let text = render();
        assert!(text.contains("alpha_fn"), "{}", text);
        // Stack discipline: nested frames restore depth.
        STATE.store(ON, Ordering::Relaxed);
        let d0 = DEPTH.load(Ordering::Relaxed);
        {
            let _f = Frame::enter("outer");
            let _g = Frame::enter("inner");
            assert_eq!(DEPTH.load(Ordering::Relaxed), d0 + 2);
        }
        assert_eq!(DEPTH.load(Ordering::Relaxed), d0);
        STATE.store(OFF, Ordering::Relaxed);
    }

    #[test]
    fn take_sample_attributes_self_and_inclusive_on_every_platform() {
        let _serial = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // The tick body is shared by the SIGPROF handler and the non-Unix
        // timer thread; drive it directly so the attribution it records is
        // pinned without depending on either tick source.
        STATE.store(ON, Ordering::Relaxed);
        let before_total = TOTAL_SAMPLES.load(Ordering::Relaxed);
        let before_idle = IDLE_SAMPLES.load(Ordering::Relaxed);
        {
            let _f = Frame::enter("sample_outer_fn");
            let _g = Frame::enter("sample_inner_fn");
            let _k = KindGuard::enter("SampleKind");
            take_sample();
            take_sample();
        }
        STATE.store(OFF, Ordering::Relaxed);
        assert_eq!(TOTAL_SAMPLES.load(Ordering::Relaxed), before_total + 2);
        assert_eq!(IDLE_SAMPLES.load(Ordering::Relaxed), before_idle, "a non-empty stack is never idle");
        let text = render();
        assert!(text.contains("tick: "), "{}", text);
        let row = |name: &str| -> (u64, u64) {
            let line = text
                .lines()
                .find(|l| l.trim_end().ends_with(name))
                .unwrap_or_else(|| panic!("missing row for {name}:\n{text}"));
            let cols: Vec<&str> = line.split_whitespace().collect();
            (cols[0].parse().unwrap(), cols[2].parse().unwrap())
        };
        let (inner_self, inner_incl) = row("sample_inner_fn");
        let (outer_self, outer_incl) = row("sample_outer_fn");
        assert!(inner_self >= 2 && inner_incl >= 2, "innermost gets self + inclusive: {text}");
        assert!(outer_incl >= 2, "caller gets inclusive: {text}");
        assert_eq!(outer_self, 0, "caller never gets self time while a callee is on top: {text}");
        assert!(text.contains("SampleKind"), "{}", text);
    }
}
