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

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

const UNKNOWN: u8 = 0;
const OFF: u8 = 1;
const ON: u8 = 2;
static STATE: AtomicU8 = AtomicU8::new(UNKNOWN);
static ATEXIT_REGISTERED: AtomicBool = AtomicBool::new(false);
static INITIALIZED: OnceLock<bool> = OnceLock::new();

/// Max interpreted call depth tracked for inclusive attribution.
const STACK_CAP: usize = 4096;
/// Open-addressed table size (power of two). Interned-name pointer keyed.
const TABLE_CAP: usize = 1 << 15;
/// Expr-kind slots: keyed by the `&'static str` pointer from `dispatch_profile::expr_kind`.
const KIND_CAP: usize = 128;

/// Immutable metadata published through one atomic pointer. A reader can see
/// an old or new identity, but never a pointer paired with another name's length.
struct SampleName {
    text: &'static str,
}

struct Slot {
    key: AtomicPtr<SampleName>,
    self_hits: AtomicU64,
    incl_hits: AtomicU64,
}

#[allow(clippy::declare_interior_mutable_const)] // reason: array initialiser for statics
const EMPTY_SLOT: Slot = Slot {
    key: AtomicPtr::new(std::ptr::null_mut()),
    self_hits: AtomicU64::new(0),
    incl_hits: AtomicU64::new(0),
};

static FRAMES: [Slot; TABLE_CAP] = [EMPTY_SLOT; TABLE_CAP];
static KINDS: [Slot; KIND_CAP] = [EMPTY_SLOT; KIND_CAP];

/// Interpreted call stack of immutable interned identities. Slots can be reused
/// while a timer samples: one atomic load always retains a valid whole identity.
static STACK_PTR: [AtomicPtr<SampleName>; STACK_CAP] = [const { AtomicPtr::new(std::ptr::null_mut()) }; STACK_CAP];
static DEPTH: AtomicUsize = AtomicUsize::new(0);
/// Innermost expr kind, published as one immutable identity.
static CUR_KIND_PTR: AtomicPtr<SampleName> = AtomicPtr::new(std::ptr::null_mut());

static TOTAL_SAMPLES: AtomicU64 = AtomicU64::new(0);
static DROPPED_SAMPLES: AtomicU64 = AtomicU64::new(0);
static IDLE_SAMPLES: AtomicU64 = AtomicU64::new(0);

/// Leaked interned names so the handler never sees a dangling pointer: a
/// `FunctionDef` for a lambda can be transient, its `name` String freed before
/// exit. Only touched when the sampler is ON.
static INTERN: Mutex<Option<HashMap<&'static str, &'static SampleName>>> = Mutex::new(None);

thread_local! {
    // Kind names are static and few. Avoid the global intern lock on every
    // profiled expression after each thread has resolved a kind once.
    static KIND_NAMES: RefCell<HashMap<&'static str, &'static SampleName>> = RefCell::new(HashMap::new());
}

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
    // Do not expose ON while another caller is still publishing the timer
    // handle: exit must be able to take ownership and join every started timer.
    let on = *INITIALIZED.get_or_init(|| {
        let on = std::env::var("SIMPLE_INTERP_SAMPLE").is_ok_and(|v| !v.is_empty() && v != "0");
        if on && !ATEXIT_REGISTERED.swap(true, Ordering::Relaxed) {
            *INTERN.lock().unwrap() = Some(HashMap::new());
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
            // The timer reads immutable identity pointers, not independently
            // mutable pointer/length fields. It allocates and locks nothing per tick.
            #[cfg(not(unix))]
            {
                extern "C" {
                    fn atexit(cb: extern "C" fn()) -> i32;
                }
                unsafe {
                    atexit(dump_at_exit);
                }
                let interval = std::time::Duration::from_micros(us as u64);
                *TICK_THREAD.lock().unwrap() = Some(TickThread::start(interval, take_sample));
            }
        }
        on
    });
    STATE.store(if on { ON } else { OFF }, Ordering::Release);
    on
}

/// Owned timer lifecycle: wake a parked thread and join before rendering.
#[cfg(not(unix))]
static TICK_THREAD: Mutex<Option<TickThread>> = Mutex::new(None);

#[cfg(any(not(unix), test))]
struct TickThread {
    running: std::sync::Arc<AtomicBool>,
    handle: std::thread::JoinHandle<()>,
}

#[cfg(any(not(unix), test))]
impl TickThread {
    fn start(interval: std::time::Duration, mut sample: impl FnMut() + Send + 'static) -> Self {
        let running = std::sync::Arc::new(AtomicBool::new(true));
        let child_running = running.clone();
        let handle = std::thread::Builder::new()
            .name("simple-interp-sampler".into())
            .spawn(move || {
                while child_running.load(Ordering::Acquire) {
                    std::thread::park_timeout(interval);
                    if !child_running.load(Ordering::Acquire) {
                        break;
                    }
                    sample();
                }
            })
            .expect("spawn interpreter sampler tick thread");
        Self { running, handle }
    }

    fn stop(self) {
        self.running.store(false, Ordering::Release);
        self.handle.thread().unpark();
        // Even a panicked tick thread is terminated after join returns.
        let _ = self.handle.join();
    }
}

#[cfg(unix)]
const TICK_SOURCE: &str = "cpu";
#[cfg(not(unix))]
const TICK_SOURCE: &str = "wall";

fn intern(name: &str) -> &'static SampleName {
    let mut g = INTERN.lock().unwrap();
    let names = g.get_or_insert_with(HashMap::new);
    if let Some(identity) = names.get(name) {
        return identity;
    }
    let text: &'static str = Box::leak(name.to_string().into_boxed_str());
    let identity: &'static SampleName = Box::leak(Box::new(SampleName { text }));
    names.insert(text, identity);
    identity
}

fn intern_kind(kind: &'static str) -> &'static SampleName {
    KIND_NAMES.with(|cache| {
        let mut cache = cache.borrow_mut();
        *cache.entry(kind).or_insert_with(|| intern(kind))
    })
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
        STACK_PTR[d].store(s as *const SampleName as *mut SampleName, Ordering::Release);
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
pub struct KindGuard(Option<*mut SampleName>);

impl KindGuard {
    #[inline(always)]
    pub fn enter(kind: &'static str) -> KindGuard {
        if !enabled() {
            return KindGuard(None);
        }
        let name = intern_kind(kind) as *const SampleName as *mut SampleName;
        let prev = CUR_KIND_PTR.swap(name, Ordering::AcqRel);
        KindGuard(Some(prev))
    }
}

impl Drop for KindGuard {
    #[inline(always)]
    fn drop(&mut self) {
        if let Some(p) = self.0 {
            CUR_KIND_PTR.store(p, Ordering::Release);
        }
    }
}

#[inline(always)]
fn hash_ptr(p: *mut SampleName) -> usize {
    let x = p as usize as u64;
    (x.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 20) as usize
}

/// Find-or-insert `key` in `table`; async-signal-safe (atomics only).
fn bump(table: &'static [Slot], key: *mut SampleName, incl: bool) -> bool {
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
        let top = STACK_PTR[d - 1].load(Ordering::Acquire);
        if !top.is_null() && !bump(&FRAMES, top, false) {
            DROPPED_SAMPLES.fetch_add(1, Ordering::Relaxed);
        }
        // Inclusive: each distinct frame once (recursion must not double count).
        let mut i = d;
        while i > 0 {
            i -= 1;
            let p = STACK_PTR[i].load(Ordering::Acquire);
            if p.is_null() {
                continue;
            }
            let mut dup = false;
            let mut j = i + 1;
            while j < d {
                if STACK_PTR[j].load(Ordering::Acquire) == p {
                    dup = true;
                    break;
                }
                j += 1;
            }
            if !dup {
                bump(&FRAMES, p, true);
            }
        }
    }
    let k = CUR_KIND_PTR.load(Ordering::Acquire);
    if !k.is_null() {
        bump(&KINDS, k, false);
    }
}

fn slot_name(s: &Slot) -> String {
    let p = s.key.load(Ordering::Acquire);
    if p.is_null() {
        return String::new();
    }
    // SAFETY: every key points to an immutable, leaked SampleName, published
    // with release ordering. Text and length come from that same identity.
    unsafe { (*p).text.to_owned() }
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
    if let Some(ticker) = TICK_THREAD.lock().unwrap().take() {
        ticker.stop();
    }
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
        assert!(std::ptr::eq(a, b), "intern must dedupe by content");
        let key = a as *const SampleName as *mut SampleName;
        assert!(bump(&FRAMES, key, false));
        assert!(bump(&FRAMES, key, false));
        assert!(bump(&FRAMES, key, true));
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
        assert_eq!(
            IDLE_SAMPLES.load(Ordering::Relaxed),
            before_idle,
            "a non-empty stack is never idle"
        );
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
        assert!(
            inner_self >= 2 && inner_incl >= 2,
            "innermost gets self + inclusive: {text}"
        );
        assert!(outer_incl >= 2, "caller gets inclusive: {text}");
        assert_eq!(
            outer_self, 0,
            "caller never gets self time while a callee is on top: {text}"
        );
        assert!(text.contains("SampleKind"), "{}", text);
    }

    #[test]
    fn captured_identity_survives_shorter_kind_publication() {
        let _serial = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        STATE.store(ON, Ordering::Relaxed);
        let old = KindGuard::enter("LongKindBeforeConcurrentReplacement");
        // Pause the reader after its single publication load; the writer now
        // replaces the current kind before the reader records its sample.
        let captured = CUR_KIND_PTR.load(Ordering::Acquire);
        let short = KindGuard::enter("Q");
        assert!(bump(&KINDS, captured, false));
        take_sample();
        let captured_slot = Slot {
            key: AtomicPtr::new(captured),
            ..EMPTY_SLOT
        };
        let current_slot = Slot {
            key: AtomicPtr::new(CUR_KIND_PTR.load(Ordering::Acquire)),
            ..EMPTY_SLOT
        };
        assert_eq!(slot_name(&captured_slot), "LongKindBeforeConcurrentReplacement");
        assert_eq!(slot_name(&current_slot), "Q");
        drop(short);
        assert_eq!(CUR_KIND_PTR.load(Ordering::Acquire), captured);
        drop(old);
        STATE.store(OFF, Ordering::Relaxed);
    }

    #[test]
    fn concurrent_frame_reuse_keeps_sample_names_whole() {
        let _serial = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        STATE.store(ON, Ordering::Relaxed);
        // Establish both rows through the production sampling path before
        // racing slot reuse; scheduling must not make this test vacuous.
        for name in ["r", "long_reused_frame_identity"] {
            let _frame = Frame::enter(name);
            take_sample();
        }
        let short_key = intern("r") as *const SampleName as *mut SampleName;
        let long_key = intern("long_reused_frame_identity") as *const SampleName as *mut SampleName;
        let reader = std::thread::spawn(|| {
            for _ in 0..10_000 {
                take_sample();
            }
        });
        for i in 0..10_000 {
            let name = if i % 2 == 0 { "r" } else { "long_reused_frame_identity" };
            let _frame = Frame::enter(name);
            std::thread::yield_now();
        }
        reader.join().unwrap();
        STATE.store(OFF, Ordering::Relaxed);
        let mut checked = 0;
        for slot in &FRAMES {
            let identity = slot.key.load(Ordering::Acquire);
            if identity == short_key {
                assert_eq!(slot_name(slot), "r");
                checked += 1;
            } else if identity == long_key {
                assert_eq!(slot_name(slot), "long_reused_frame_identity");
                checked += 1;
            }
        }
        assert_eq!(checked, 2, "both reused frame identities must be sampled");
    }

    #[test]
    fn stopping_a_parked_tick_thread_wakes_and_joins_before_returning() {
        let calls = std::sync::Arc::new(AtomicUsize::new(0));
        let child_calls = calls.clone();
        let ticker = TickThread::start(std::time::Duration::from_secs(30), move || {
            child_calls.fetch_add(1, Ordering::Relaxed);
        });
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let stopper = std::thread::spawn(move || {
            ticker.stop();
            done_tx.send(()).unwrap();
        });
        done_rx
            .recv_timeout(std::time::Duration::from_secs(2))
            .expect("stop must wake the long interval and join, not wait for it");
        stopper.join().unwrap();
        let stopped_calls = calls.load(Ordering::Relaxed);
        std::thread::yield_now();
        assert_eq!(
            calls.load(Ordering::Relaxed),
            stopped_calls,
            "joined timer cannot sample again"
        );
    }
}
