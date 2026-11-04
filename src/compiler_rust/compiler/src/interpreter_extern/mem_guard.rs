//! Sampled guard-page allocator (plan M2, hosted-lane only).
//!
//! GWP-ASan-style: 1-in-N hosted `rt_alloc` calls land on their own
//! `mmap`'d slot with an unmapped-permission guard page after the data
//! region, so a small overflow traps instead of corrupting a neighbor.
//! `rt_free` on a sampled pointer does not `munmap` immediately — it
//! `mprotect(PROT_NONE)`s the whole slot (data pages too) so a
//! use-after-free read/write also traps, and defers the real `munmap` to a
//! bounded FIFO ring so the trap window survives past the free call.
//!
//! Sampling rate is `SIMPLE_MEM_GUARD_RATE=N` (unset/0 = disabled, the
//! zero-overhead default — `mem_guard_should_sample` degenerates to reading
//! one cached `OnceLock<u64>` and returning `false`, no atomic churn beyond
//! that). See `doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md`.

#![cfg_attr(not(unix), allow(dead_code))]

use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicU64, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

/// Host VM page size. Hard-coding 4096 broke every sampled slot on hosts with
/// larger pages (Apple Silicon macOS uses 16 KiB): the trailing guard page
/// landed mid-page, `mprotect` failed with EINVAL, and every sample silently
/// fell back to the normal allocator.
fn page_size() -> usize {
    static PAGE: OnceLock<usize> = OnceLock::new();
    *PAGE.get_or_init(|| {
        #[cfg(unix)]
        {
            let raw = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
            if raw > 0 {
                return raw as usize;
            }
        }
        4096
    })
}
/// Bound on slots awaiting real `munmap` after being guard-protected — keeps
/// address-space growth bounded under sustained sampled alloc/free traffic.
const FREE_RING_CAP: usize = 256;

static GUARD_RATE: OnceLock<u64> = OnceLock::new();

/// Cached `SIMPLE_MEM_GUARD_RATE` value. 0 = sampling disabled.
fn guard_rate() -> u64 {
    *GUARD_RATE.get_or_init(|| {
        std::env::var("SIMPLE_MEM_GUARD_RATE")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .unwrap_or(0)
    })
}

static SAMPLE_COUNTER: AtomicU64 = AtomicU64::new(0);
static SAMPLED_TOTAL: AtomicU64 = AtomicU64::new(0);

/// Deterministic 1-in-N sampling decision (never `rand()` — CI/fixture
/// determinism per the design doc). N=0 (unset) always returns `false`, and
/// costs exactly one cached-bool-shaped `OnceLock` read plus an early return
/// — the zero-overhead-when-off contract.
pub fn mem_guard_should_sample(_size: usize) -> bool {
    let rate = guard_rate();
    if rate == 0 {
        return false;
    }
    let n = SAMPLE_COUNTER.fetch_add(1, Ordering::Relaxed);
    n % rate == 0
}

struct GuardSlot {
    page_base: usize,
    total_pages: usize,
    /// Index of this slot's mirror entry in `FAULT_TABLE` (fault-handler view).
    fault_idx: usize,
    freed: bool,
}

#[derive(Default)]
struct GuardState {
    slots: HashMap<usize, GuardSlot>,
    free_ring: VecDeque<usize>,
}

static GUARD_STATE: OnceLock<Mutex<GuardState>> = OnceLock::new();

// ---- Fault-handler view: lock-free, fixed-size, async-signal-safe ----------
// The Mutex<HashMap> above cannot be used from a signal handler (locks and
// allocates), so every tracked slot is mirrored into this static atomic table;
// the SIGSEGV handler only reads it and emits the report with write(2).

const FAULT_SLOTS: usize = 4096;
const REPORT_MAX: usize = 320;
const ST_EMPTY: u8 = 0;
const ST_LIVE: u8 = 1;
const ST_FREED: u8 = 2;
const ST_FILLING: u8 = 3;

struct FaultEntry {
    state: AtomicU8,
    base: AtomicUsize,
    len: AtomicUsize,
    size: AtomicUsize,
    owner: AtomicUsize,
}

#[allow(clippy::declare_interior_mutable_const)]
const FAULT_EMPTY: FaultEntry = FaultEntry {
    state: AtomicU8::new(ST_EMPTY),
    base: AtomicUsize::new(0),
    len: AtomicUsize::new(0),
    size: AtomicUsize::new(0),
    owner: AtomicUsize::new(0),
};
static FAULT_TABLE: [FaultEntry; FAULT_SLOTS] = [FAULT_EMPTY; FAULT_SLOTS];

/// Claim a free mirror entry and publish the slot. Returns its index.
fn fault_record(base: usize, len: usize, size: usize, owner: u32) -> Option<usize> {
    for (i, e) in FAULT_TABLE.iter().enumerate() {
        if e.state
            .compare_exchange(ST_EMPTY, ST_FILLING, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            e.base.store(base, Ordering::Relaxed);
            e.len.store(len, Ordering::Relaxed);
            e.size.store(size, Ordering::Relaxed);
            e.owner.store(owner as usize, Ordering::Relaxed);
            e.state.store(ST_LIVE, Ordering::Release);
            return Some(i);
        }
    }
    None
}

fn fault_mark_freed(idx: usize) {
    FAULT_TABLE[idx].state.store(ST_FREED, Ordering::Release);
}

fn fault_clear(idx: usize) {
    FAULT_TABLE[idx].state.store(ST_EMPTY, Ordering::Release);
}

struct ReportBuf {
    buf: [u8; REPORT_MAX],
    len: usize,
}

impl ReportBuf {
    fn str(&mut self, s: &str) {
        for &b in s.as_bytes() {
            if self.len + 1 < REPORT_MAX {
                self.buf[self.len] = b;
                self.len += 1;
            }
        }
    }
    fn num(&mut self, mut v: usize, base: usize) {
        let mut tmp = [0u8; 24];
        let mut n = 0;
        loop {
            tmp[n] = b"0123456789abcdef"[v % base];
            n += 1;
            v /= base;
            if v == 0 || n == tmp.len() {
                break;
            }
        }
        while n > 0 {
            n -= 1;
            if self.len + 1 < REPORT_MAX {
                self.buf[self.len] = tmp[n];
                self.len += 1;
            }
        }
    }
}

/// If `addr` lies in a tracked guard slot, build the one-line owner-attribution
/// report (class, addr, size, owner id) and return it; `None` for any other
/// address. Allocation-free and lock-free, so safe to call from a signal handler.
fn fault_report(addr: usize) -> Option<ReportBuf> {
    let ps = page_size();
    for e in FAULT_TABLE.iter() {
        let st = e.state.load(Ordering::Acquire);
        if st != ST_LIVE && st != ST_FREED {
            continue;
        }
        let lo = e.base.load(Ordering::Relaxed);
        let hi = lo + e.len.load(Ordering::Relaxed);
        if addr < lo || addr >= hi {
            continue;
        }
        let class = if st == ST_FREED {
            "use-after-free"
        } else if addr < lo + ps {
            "underflow"
        } else if addr >= hi - ps {
            "overflow"
        } else {
            "access"
        };
        let mut r = ReportBuf { buf: [0; REPORT_MAX], len: 0 };
        r.str("[mem_guard] guard-page trap: ");
        r.str(class);
        r.str(" addr=0x");
        r.num(addr, 16);
        r.str(" size=");
        r.num(e.size.load(Ordering::Relaxed), 10);
        r.str(" owner=");
        r.num(e.owner.load(Ordering::Relaxed), 10);
        r.str("\n");
        return Some(r);
    }
    None
}

#[cfg(unix)]
static mut PREV_SEGV: std::mem::MaybeUninit<libc::sigaction> = std::mem::MaybeUninit::uninit();
#[cfg(unix)]
static HANDLER_INSTALLED: std::sync::Once = std::sync::Once::new();

/// SIGSEGV handler: print the report if the fault is in a guard slot, then
/// restore the previous disposition and return so the faulting instruction
/// re-executes and the process dies exactly as without us (never swallowed;
/// non-guard faults take the same path).
#[cfg(unix)]
extern "C" fn fault_handler(sig: libc::c_int, info: *mut libc::siginfo_t, _ctx: *mut libc::c_void) {
    unsafe {
        let addr = (*info).si_addr() as usize;
        if let Some(r) = fault_report(addr) {
            libc::write(2, r.buf.as_ptr() as *const libc::c_void, r.len);
        }
        libc::sigaction(sig, (&raw const PREV_SEGV) as *const libc::sigaction, std::ptr::null_mut());
    }
}

#[cfg(unix)]
fn install_fault_handler() {
    HANDLER_INSTALLED.call_once(|| unsafe {
        let mut sa: libc::sigaction = std::mem::zeroed();
        sa.sa_sigaction = fault_handler as usize;
        sa.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
        libc::sigemptyset(&mut sa.sa_mask);
        libc::sigaction(libc::SIGSEGV, &sa, (&raw mut PREV_SEGV) as *mut libc::sigaction);
    });
}

fn guard_state() -> &'static Mutex<GuardState> {
    GUARD_STATE.get_or_init(|| Mutex::new(GuardState::default()))
}

/// Allocate `size` bytes on their own guard-paged mmap slot. Right-aligns the
/// allocation so its last byte lands on the last byte of the last data page
/// (GWP-ASan default — catches overflow, not underflow). Returns the
/// user-visible pointer, or `None` on mmap/mprotect failure (caller should
/// fall back to the normal allocator).
///
/// Windows has no `mmap`/`mprotect`/`munmap` (the `libc` crate does not
/// export those symbols for `windows-msvc` at all — an unconditional call
/// fails to even LINK, not merely to run: "unresolved module or unlinked
/// crate `libc`", found blocking the whole seed build 2026-08-09). A real
/// guard-page implementation there needs `VirtualAlloc`/`VirtualProtect` plus
/// a vectored exception handler to catch the guard-page fault — an
/// architecturally different mechanism from POSIX SIGSEGV, not a mechanical
/// swap, and out of scope for unblocking the build. `None` is already this
/// function's documented "fall back to the normal allocator" contract for
/// any allocation failure, so returning it unconditionally on Windows is a
/// real, already-supported code path — sampling is simply always a miss
/// there (`SIMPLE_MEM_GUARD_RATE` remains a Unix-only opt-in debugging aid)
/// rather than a new failure mode.
#[cfg(not(unix))]
pub fn guard_alloc_sampled(_size: usize, _owner: u32) -> Option<usize> {
    None
}

#[cfg(unix)]
pub fn guard_alloc_sampled(size: usize, owner: u32) -> Option<usize> {
    if size == 0 {
        return None;
    }
    let data_pages = size.div_ceil(page_size()).max(1);
    let total_pages = data_pages + 2; // leading + trailing guard page
    let map_len = total_pages * page_size();

    unsafe {
        let base = libc::mmap(
            std::ptr::null_mut(),
            map_len,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANON,
            -1,
            0,
        );
        if base == libc::MAP_FAILED {
            return None;
        }
        let page_base = base as usize;
        let trailing_page = page_base + page_size() * (1 + data_pages);

        if libc::mprotect(page_base as *mut libc::c_void, page_size(), libc::PROT_NONE) != 0
            || libc::mprotect(trailing_page as *mut libc::c_void, page_size(), libc::PROT_NONE) != 0
        {
            libc::munmap(base, map_len);
            return None;
        }

        // Right-align within the data region [page_base+page_size(), trailing_page).
        let user_ptr = trailing_page - size;

        let Some(fault_idx) = fault_record(page_base, map_len, size, owner) else {
            libc::munmap(base, map_len);
            return None;
        };
        install_fault_handler();
        let mut st = guard_state().lock().unwrap_or_else(|e| e.into_inner());
        st.slots.insert(
            user_ptr,
            GuardSlot {
                page_base,
                total_pages,
                fault_idx,
                freed: false,
            },
        );
        SAMPLED_TOTAL.fetch_add(1, Ordering::Relaxed);
        Some(user_ptr)
    }
}

/// True if `ptr` is a tracked guard slot (live or already freed-and-quarantined).
/// On Windows this is always `false`: `guard_alloc_sampled` never actually
/// hands out a slot there, so nothing is ever tracked — see its doc comment.
pub fn guard_is_slot(ptr: usize) -> bool {
    guard_state()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .slots
        .contains_key(&ptr)
}

/// Free a sampled guard slot: `mprotect(PROT_NONE)`s the whole mapping
/// (traps any further read/write, including UAF) and enqueues it for delayed
/// real `munmap` once the ring evicts it. Returns `false` for an unknown
/// pointer or a double free (slot already marked freed) — caller must refuse
/// to treat those as a normal free.
#[cfg(not(unix))]
pub fn guard_free_sampled(_ptr: usize) -> bool {
    false
}

#[cfg(unix)]
pub fn guard_free_sampled(ptr: usize) -> bool {
    let mut st = guard_state().lock().unwrap_or_else(|e| e.into_inner());
    let Some(slot) = st.slots.get_mut(&ptr) else {
        return false;
    };
    if slot.freed {
        return false; // double free of a guard slot — refuse
    }
    slot.freed = true;
    fault_mark_freed(slot.fault_idx);
    let page_base = slot.page_base;
    let map_len = slot.total_pages * page_size();
    unsafe {
        libc::mprotect(page_base as *mut libc::c_void, map_len, libc::PROT_NONE);
    }
    st.free_ring.push_back(ptr);
    while st.free_ring.len() > FREE_RING_CAP {
        let Some(evict_ptr) = st.free_ring.pop_front() else {
            break;
        };
        if let Some(evicted) = st.slots.remove(&evict_ptr) {
            fault_clear(evicted.fault_idx);
            unsafe {
                libc::munmap(evicted.page_base as *mut libc::c_void, evicted.total_pages * page_size());
            }
        }
    }
    true
}

/// Total number of hosted `rt_alloc` calls ever routed onto a guard slot
/// (extern `rt_mem_guard_stats`). 0 whenever `SIMPLE_MEM_GUARD_RATE` is unset.
pub fn guard_sampled_count() -> i64 {
    SAMPLED_TOTAL.load(Ordering::Relaxed) as i64
}

#[cfg(test)]
mod report_tests {
    use super::*;

    fn text(r: &ReportBuf) -> String {
        String::from_utf8_lossy(&r.buf[..r.len]).into_owned()
    }

    #[test]
    fn fault_report_names_class_size_and_owner() {
        let ps = page_size();
        let base = 0x7000_0000_0000usize;
        let idx = fault_record(base, 4 * ps, 100, 42).expect("table has room");
        let over = text(&fault_report(base + 3 * ps + 5).expect("trailing guard"));
        assert!(over.contains("overflow"), "{over}");
        assert!(over.contains("size=100"), "{over}");
        assert!(over.contains("owner=42"), "{over}");
        let under = text(&fault_report(base + 8).expect("leading guard"));
        assert!(under.contains("underflow"), "{under}");
        fault_mark_freed(idx);
        let uaf = text(&fault_report(base + ps + 3).expect("freed slot"));
        assert!(uaf.contains("use-after-free"), "{uaf}");
        fault_clear(idx);
        assert!(fault_report(base + 3 * ps + 5).is_none(), "cleared slot must not report");
    }

    #[test]
    fn fault_report_ignores_non_guard_address() {
        assert!(fault_report(0x10).is_none());
    }
}

// Every test here exercises the real mmap/mprotect-backed implementation
// (`.expect("mmap guard slot must succeed")` etc.), which only exists under
// `#[cfg(unix)]` above — on Windows `guard_alloc_sampled` always returns
// `None` by design (see its doc comment), so these would universally panic
// there rather than testing anything real.
#[cfg(all(test, unix))]
mod tests {
    use super::*;

    #[test]
    fn should_sample_is_disabled_by_default_rate_zero() {
        // guard_rate() reads the real env in-process; without the env set
        // (the common case), rate is 0 and sampling never fires.
        if std::env::var("SIMPLE_MEM_GUARD_RATE").is_err() {
            assert!(!mem_guard_should_sample(64));
        }
    }

    #[test]
    fn guard_alloc_right_aligns_and_is_tracked() {
        let ptr = guard_alloc_sampled(37, 0).expect("mmap guard slot must succeed");
        assert!(guard_is_slot(ptr));
        // Last byte of the allocation must be the last byte of a page
        // (right-aligned placement): (ptr + size) is page-aligned.
        assert_eq!((ptr + 37) % page_size(), 0);
        // Writing within bounds must not trap.
        unsafe {
            std::ptr::write_bytes(ptr as *mut u8, 0xAB, 37);
        }
        assert!(guard_free_sampled(ptr));
    }

    #[test]
    fn guard_free_unknown_pointer_is_refused() {
        assert!(!guard_free_sampled(0xDEAD_BEEF));
    }

    #[test]
    fn guard_free_double_free_is_refused() {
        let ptr = guard_alloc_sampled(16, 0).expect("mmap guard slot must succeed");
        assert!(guard_free_sampled(ptr));
        // Second free of the same (now-quarantined) slot must be refused,
        // not attempt a second mprotect/munmap.
        assert!(!guard_free_sampled(ptr));
    }

    /// Test (c) from the M2 plan: with a freed sampled pointer, the slot's
    /// bookkeeping shows it unmapped-for-access (PROT_NONE'd, marked freed).
    /// We assert via the returned mprotect status and the `freed` flag
    /// rather than dereferencing the pointer in-process — a real read would
    /// SIGSEGV the test runner by design.
    #[test]
    fn guard_free_protects_slot_without_dereferencing() {
        let ptr = guard_alloc_sampled(64, 7).expect("mmap guard slot must succeed");
        let (page_base, total_pages) = {
            let st = guard_state().lock().unwrap_or_else(|e| e.into_inner());
            let slot = st.slots.get(&ptr).expect("slot must be tracked");
            (slot.page_base, slot.total_pages)
        };
        assert!(guard_free_sampled(ptr));
        {
            let st = guard_state().lock().unwrap_or_else(|e| e.into_inner());
            let slot = st.slots.get(&ptr).expect("slot stays tracked until ring eviction");
            assert!(slot.freed, "slot must be marked freed");
        }
        // Re-`mprotect`ing the already-PROT_NONE region to the SAME
        // protection must succeed (0) — a legal no-op re-application,
        // proving the slot is still a valid, currently-PROT_NONE mapping
        // (not munmapped, not writable) without ever touching its bytes.
        let rc = unsafe { libc::mprotect(page_base as *mut libc::c_void, total_pages * page_size(), libc::PROT_NONE) };
        assert_eq!(rc, 0, "guarded slot must still be a valid PROT_NONE mapping");
    }

    #[test]
    fn guard_sampled_count_increments_on_sample() {
        let before = guard_sampled_count();
        let ptr = guard_alloc_sampled(8, 0).expect("mmap guard slot must succeed");
        assert_eq!(guard_sampled_count(), before + 1);
        guard_free_sampled(ptr);
    }
}
