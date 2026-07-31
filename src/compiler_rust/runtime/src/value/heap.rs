//! Heap object types and header structure.

use crate::hir_core::ValueKind;

/// Heap object type tags
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapObjectType {
    String = 0x01,
    Array = 0x02,
    Dict = 0x03,
    Tuple = 0x04,
    Object = 0x05,
    Closure = 0x06,
    Enum = 0x07,
    Future = 0x08,
    Generator = 0x09,
    Actor = 0x0A,
    Unique = 0x0B,
    Shared = 0x0C,
    Borrow = 0x0D,
    Channel = 0x0E,
    Weak = 0x0F,
    ContractViolation = 0x10,
    // Synchronization primitives
    Mutex = 0x11,
    RwLock = 0x12,
    Semaphore = 0x13,
    Barrier = 0x14,
    Atomic = 0x15,
    // Monoio direct async I/O (feature: monoio-direct)
    MonoioFuture = 0x16,
    // High-performance collections (Rust std::collections)
    HashMap = 0x17,
    BTreeMap = 0x18,
    HashSet = 0x19,
    BTreeSet = 0x1A,
    // SFFI-wrapped Rust objects (object-based SFFI system)
    FfiObject = 0x1B,
    // Heap-boxed f64. The inline TAG_FLOAT representation stores only the upper
    // 61 bits of the mantissa (`bits >> 3`), silently zeroing the low 3 bits, so
    // a container/Any float loses precision ([0.1][0] != 0.1). Container floats
    // are boxed here instead, preserving the full double losslessly.
    Float = 0x1C,
}

/// Header for all heap-allocated objects
#[repr(C)]
#[derive(Debug)]
pub struct HeapHeader {
    /// Type of the heap object
    pub object_type: HeapObjectType,
    /// GC flags (mark bit, etc.)
    pub gc_flags: u8,
    /// Reserved for alignment
    pub reserved: u16,
    /// Size of the object in bytes (including header)
    pub size: u32,
}

/// Heap-boxed f64 (see `HeapObjectType::Float`). A leaf object: the full
/// double is stored verbatim so container/Any floats round-trip exactly.
/// Discrimination is O(1): the pointer is validated against the shared
/// `HEAP_ALLOCATION_REGISTRY` HashSet (a pure membership test, performed
/// before any `->value`/`->header` dereference), so a stray i64 that merely
/// aliases TAG_HEAP is never dereferenced.
#[repr(C)]
pub struct HeapFloat {
    pub header: HeapHeader,
    pub value: f64,
}

/// GC flag bits stored in HeapHeader::gc_flags
pub mod gc_flags {
    /// Object has not been visited by GC (white in tri-color marking)
    pub const WHITE: u8 = 0b00;
    /// Object is reachable but not yet scanned (gray in tri-color marking)
    pub const GRAY: u8 = 0b01;
    /// Object has been scanned and is definitely reachable (black in tri-color marking)
    pub const BLACK: u8 = 0b10;
    /// Mask for the color bits
    pub const COLOR_MASK: u8 = 0b11;
    /// Object is pinned and should not be moved
    pub const PINNED: u8 = 0b100;
    /// RuntimeArray stores raw u8 bytes in data instead of RuntimeValue slots.
    pub const BYTE_PACKED: u8 = 0b1000;
    /// RuntimeArray stores raw u64 words in data instead of tagged RuntimeValue slots.
    pub const U64_PACKED: u8 = 0b1_0000;
}

impl HeapHeader {
    pub fn new(object_type: HeapObjectType, size: u32) -> Self {
        Self {
            object_type,
            gc_flags: gc_flags::WHITE,
            reserved: 0,
            size,
        }
    }

    /// Get the GC color of this object
    #[inline]
    pub fn gc_color(&self) -> u8 {
        self.gc_flags & gc_flags::COLOR_MASK
    }

    /// Check if this object is white (not yet visited)
    #[inline]
    pub fn is_white(&self) -> bool {
        self.gc_color() == gc_flags::WHITE
    }

    /// Check if this object is gray (reachable, needs scanning)
    #[inline]
    pub fn is_gray(&self) -> bool {
        self.gc_color() == gc_flags::GRAY
    }

    /// Check if this object is black (fully scanned)
    #[inline]
    pub fn is_black(&self) -> bool {
        self.gc_color() == gc_flags::BLACK
    }

    /// Mark this object as gray (reachable, needs scanning)
    #[inline]
    pub fn mark_gray(&mut self) {
        self.gc_flags = (self.gc_flags & !gc_flags::COLOR_MASK) | gc_flags::GRAY;
    }

    /// Mark this object as black (fully scanned)
    #[inline]
    pub fn mark_black(&mut self) {
        self.gc_flags = (self.gc_flags & !gc_flags::COLOR_MASK) | gc_flags::BLACK;
    }

    /// Reset this object to white (for new GC cycle)
    #[inline]
    pub fn reset_color(&mut self) {
        self.gc_flags = (self.gc_flags & !gc_flags::COLOR_MASK) | gc_flags::WHITE;
    }

    /// Check if this object is pinned
    #[inline]
    pub fn is_pinned(&self) -> bool {
        (self.gc_flags & gc_flags::PINNED) != 0
    }

    /// Pin this object (prevent moving)
    #[inline]
    pub fn pin(&mut self) {
        self.gc_flags |= gc_flags::PINNED;
    }

    /// Unpin this object
    #[inline]
    pub fn unpin(&mut self) {
        self.gc_flags &= !gc_flags::PINNED;
    }
}

// ============================================================================
// Shared heap validation utilities
// ============================================================================

use super::core::RuntimeValue;
use std::collections::HashSet;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock, RwLock};

const MIN_VALID_HEAP_ADDR: usize = 4096;

static HEAP_ALLOCATION_REGISTRY: OnceLock<Mutex<HashSet<usize>>> = OnceLock::new();

// ---------------------------------------------------------------------------
// Byte-level accounting (header bytes only).
//
// `rt_heap_registry_count()` counts objects, which says nothing about memory:
// an empty dict and a 100k-element array count as 1 each. `HeapHeader.size`
// is written by every allocation site, so the register/unregister choke
// points can account header bytes exactly with no per-site changes.
//
// Known limit (tracked as a follow-up lane, not silently ignored): container
// BACKING buffers (Vec capacity, string bytes) are separate allocations not
// covered by `size`; aux-byte accounting needs per-collection wiring.
// ---------------------------------------------------------------------------
const HEAP_KIND_SLOTS: usize = 32;

static HEAP_LIVE_BYTES: AtomicU64 = AtomicU64::new(0);
static HEAP_PEAK_BYTES: AtomicU64 = AtomicU64::new(0);
static HEAP_TOTAL_ALLOCS: AtomicU64 = AtomicU64::new(0);
static HEAP_TOTAL_FREES: AtomicU64 = AtomicU64::new(0);
static HEAP_KIND_LIVE_COUNT: [AtomicU64; HEAP_KIND_SLOTS] = [const { AtomicU64::new(0) }; HEAP_KIND_SLOTS];
static HEAP_KIND_LIVE_BYTES: [AtomicU64; HEAP_KIND_SLOTS] = [const { AtomicU64::new(0) }; HEAP_KIND_SLOTS];

#[inline]
fn note_heap_alloc(kind: u8, bytes: u64) {
    HEAP_TOTAL_ALLOCS.fetch_add(1, Ordering::Relaxed);
    let live = HEAP_LIVE_BYTES.fetch_add(bytes, Ordering::Relaxed) + bytes;
    HEAP_PEAK_BYTES.fetch_max(live, Ordering::Relaxed);
    if let Some(slot) = HEAP_KIND_LIVE_COUNT.get(kind as usize) {
        slot.fetch_add(1, Ordering::Relaxed);
    }
    if let Some(slot) = HEAP_KIND_LIVE_BYTES.get(kind as usize) {
        slot.fetch_add(bytes, Ordering::Relaxed);
    }
}

#[inline]
fn note_heap_free(kind: u8, bytes: u64) {
    HEAP_TOTAL_FREES.fetch_add(1, Ordering::Relaxed);
    HEAP_LIVE_BYTES.fetch_sub(bytes, Ordering::Relaxed);
    if let Some(slot) = HEAP_KIND_LIVE_COUNT.get(kind as usize) {
        slot.fetch_sub(1, Ordering::Relaxed);
    }
    if let Some(slot) = HEAP_KIND_LIVE_BYTES.get(kind as usize) {
        slot.fetch_sub(bytes, Ordering::Relaxed);
    }
}

fn heap_allocation_registry() -> &'static Mutex<HashSet<usize>> {
    HEAP_ALLOCATION_REGISTRY.get_or_init(|| Mutex::new(HashSet::new()))
}

#[inline]
pub fn register_heap_ptr(ptr: *mut HeapHeader) {
    if !ptr.is_null() {
        let inserted = heap_allocation_registry()
            .lock()
            .map(|mut registry| registry.insert(ptr as usize))
            .unwrap_or(false);
        if inserted {
            // Caller just allocated the object; header is valid by contract.
            let (kind, bytes) = unsafe { ((*ptr).object_type as u8, (*ptr).size as u64) };
            note_heap_alloc(kind, bytes);
            note_attr_alloc(ptr as usize, bytes);
        }
    }
}

#[inline]
pub fn unregister_heap_ptr(ptr: *mut HeapHeader) {
    if !ptr.is_null() {
        let removed = heap_allocation_registry()
            .lock()
            .map(|mut registry| registry.remove(&(ptr as usize)))
            .unwrap_or(false);
        if removed {
            // Presence in the registry means not yet freed (the erasing call
            // is the one allowed to free), so this read is not use-after-free.
            let (kind, bytes) = unsafe { ((*ptr).object_type as u8, (*ptr).size as u64) };
            note_heap_free(kind, bytes);
            note_attr_free(ptr as usize, bytes);
        }
    }
}

/// Unregister a heap pointer, reporting whether THIS call is the one that
/// erased it. Mirrors the C runtime's `rt_core_unregister_immortal_ptr`
/// (src/runtime/runtime_native.c), whose non-zero return is the single
/// serialization point that makes a free safe: the registry mutex guarantees
/// exactly one caller observes `true` for a given pointer, so a double free
/// (or a free of a never-registered pointer) is refused instead of executing.
/// `RuntimeValue` is `Copy`, so aliases are the norm — this is the gate.
#[inline]
pub fn unregister_heap_ptr_checked(ptr: *mut HeapHeader) -> bool {
    if ptr.is_null() {
        return false;
    }
    let removed = heap_allocation_registry()
        .lock()
        .map(|mut registry| registry.remove(&(ptr as usize)))
        .unwrap_or(false);
    if removed {
        let (kind, bytes) = unsafe { ((*ptr).object_type as u8, (*ptr).size as u64) };
        note_heap_free(kind, bytes);
        note_attr_free(ptr as usize, bytes);
    }
    removed
}

#[inline]
pub fn is_registered_heap_ptr(ptr: *mut HeapHeader) -> bool {
    heap_allocation_registry()
        .lock()
        .map(|registry| registry.contains(&(ptr as usize)))
        .unwrap_or(false)
}

/// Number of RuntimeValue heap objects known to the hosted runtime.
///
/// This is a diagnostic registry count, not a live-byte measurement: most
/// no-GC compiler temporaries stay registered for the process lifetime.
#[no_mangle]
pub extern "C" fn rt_heap_registry_count() -> i64 {
    heap_allocation_registry()
        .lock()
        .map(|registry| registry.len() as i64)
        .unwrap_or(0)
}

pub fn clear_heap_allocation_registry() {
    if let Some(registry) = HEAP_ALLOCATION_REGISTRY.get() {
        let _ = registry.lock().map(|mut registry| registry.clear());
    }
    HEAP_LIVE_BYTES.store(0, Ordering::Relaxed);
    HEAP_TOTAL_ALLOCS.store(0, Ordering::Relaxed);
    HEAP_TOTAL_FREES.store(0, Ordering::Relaxed);
    // Peak intentionally survives a clear: it answers "how big did this
    // process get", which a bulk reset must not erase.
    for slot in HEAP_KIND_LIVE_COUNT.iter().chain(HEAP_KIND_LIVE_BYTES.iter()) {
        slot.store(0, Ordering::Relaxed);
    }
}

/// Live heap HEADER bytes currently registered (excludes container backing
/// buffers — see the accounting comment above).
#[no_mangle]
pub extern "C" fn rt_heap_live_bytes() -> i64 {
    HEAP_LIVE_BYTES.load(Ordering::Relaxed) as i64
}

/// High-water mark of `rt_heap_live_bytes` for this process.
#[no_mangle]
pub extern "C" fn rt_heap_peak_bytes() -> i64 {
    HEAP_PEAK_BYTES.load(Ordering::Relaxed) as i64
}

/// Total registered allocations since process start (monotonic).
#[no_mangle]
pub extern "C" fn rt_heap_alloc_count() -> i64 {
    HEAP_TOTAL_ALLOCS.load(Ordering::Relaxed) as i64
}

/// Total unregistered (freed) allocations since process start (monotonic).
#[no_mangle]
pub extern "C" fn rt_heap_free_count() -> i64 {
    HEAP_TOTAL_FREES.load(Ordering::Relaxed) as i64
}

/// Live object count for one `HeapObjectType` tag (0 for out-of-range kinds).
#[no_mangle]
pub extern "C" fn rt_heap_live_count_by_kind(kind: i64) -> i64 {
    HEAP_KIND_LIVE_COUNT
        .get(kind as usize)
        .map(|slot| slot.load(Ordering::Relaxed) as i64)
        .unwrap_or(0)
}

/// Live header bytes for one `HeapObjectType` tag (0 for out-of-range kinds).
#[no_mangle]
pub extern "C" fn rt_heap_live_bytes_by_kind(kind: i64) -> i64 {
    HEAP_KIND_LIVE_BYTES
        .get(kind as usize)
        .map(|slot| slot.load(Ordering::Relaxed) as i64)
        .unwrap_or(0)
}

/// Validate heap object type, returns None if invalid
///
/// This is a shared helper to reduce boilerplate in SFFI functions.
#[inline]
pub fn validate_heap_obj(val: RuntimeValue, expected: HeapObjectType) -> Option<*mut HeapHeader> {
    if !val.is_heap() {
        return None;
    }
    let ptr = val.as_heap_ptr();
    let addr = ptr as usize;
    if ptr.is_null() || addr < MIN_VALID_HEAP_ADDR || addr & 0x7 != 0 {
        return None;
    }
    if !is_registered_heap_ptr(ptr) {
        return None;
    }
    if unsafe { (*ptr).object_type != expected } {
        return None;
    }
    Some(ptr)
}

/// Get typed pointer from heap object with validation.
/// Returns None if the value is not a valid heap object of the expected type.
#[inline]
pub fn get_typed_ptr<T>(val: RuntimeValue, expected: HeapObjectType) -> Option<*const T> {
    validate_heap_obj(val, expected).map(|ptr| ptr as *const T)
}

/// Read a typed heap object while holding the allocation registry lock.
///
/// This is for FFI adapters that must copy data from a RuntimeValue while a
/// concurrent free could otherwise invalidate the pointer after validation.
pub fn with_typed_ptr<T, R>(
    val: RuntimeValue,
    expected: HeapObjectType,
    read: impl FnOnce(*const T) -> R,
) -> Option<R> {
    if !val.is_heap() {
        return None;
    }
    let ptr = val.as_heap_ptr();
    let addr = ptr as usize;
    if ptr.is_null() || addr < MIN_VALID_HEAP_ADDR || addr & 0x7 != 0 {
        return None;
    }
    let registry = heap_allocation_registry().lock().ok()?;
    if !registry.contains(&addr) {
        return None;
    }
    if unsafe { (*ptr).object_type != expected } {
        return None;
    }
    Some(read(ptr as *const T))
}

/// Get mutable typed pointer from heap object with validation.
/// Returns None if the value is not a valid heap object of the expected type.
#[inline]
pub fn get_typed_ptr_mut<T>(val: RuntimeValue, expected: HeapObjectType) -> Option<*mut T> {
    validate_heap_obj(val, expected).map(|ptr| ptr as *mut T)
}

/// Macro to get typed pointer with early return on invalid type.
/// Usage: `let ptr = as_typed_ptr!(val, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);`
#[macro_export]
macro_rules! as_typed_ptr {
    ($val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match $crate::value::heap::get_typed_ptr::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
    (mut $val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match $crate::value::heap::get_typed_ptr_mut::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
}

// ============================================================================
// ValueKind conversion
// ============================================================================

impl From<HeapObjectType> for ValueKind {
    fn from(heap_type: HeapObjectType) -> Self {
        match heap_type {
            HeapObjectType::String => ValueKind::String,
            HeapObjectType::Array => ValueKind::Array,
            HeapObjectType::Dict => ValueKind::Dict,
            HeapObjectType::Tuple => ValueKind::Tuple,
            HeapObjectType::Object => ValueKind::Object,
            HeapObjectType::Closure => ValueKind::Closure,
            HeapObjectType::Enum => ValueKind::Enum,
            HeapObjectType::Future => ValueKind::Future,
            HeapObjectType::Generator => ValueKind::Generator,
            HeapObjectType::Actor => ValueKind::Actor,
            HeapObjectType::Unique => ValueKind::Unique,
            HeapObjectType::Shared => ValueKind::Shared,
            HeapObjectType::Borrow => ValueKind::Borrow,
            HeapObjectType::Channel => ValueKind::Channel,
            HeapObjectType::Weak => ValueKind::Weak,
            HeapObjectType::ContractViolation => ValueKind::ContractViolation,
            HeapObjectType::Mutex => ValueKind::Mutex,
            HeapObjectType::RwLock => ValueKind::RwLock,
            HeapObjectType::Semaphore => ValueKind::Semaphore,
            HeapObjectType::Barrier => ValueKind::Barrier,
            HeapObjectType::Atomic => ValueKind::Atomic,
            HeapObjectType::MonoioFuture => ValueKind::MonoioFuture,
            HeapObjectType::HashMap => ValueKind::HashMap,
            HeapObjectType::BTreeMap => ValueKind::BTreeMap,
            HeapObjectType::HashSet => ValueKind::HashSet,
            HeapObjectType::BTreeSet => ValueKind::BTreeSet,
            HeapObjectType::FfiObject => ValueKind::FfiObject,
            // Heap-boxed float presents as a plain float to the value system.
            HeapObjectType::Float => ValueKind::Float,
        }
    }
}

// ============================================================================
// Aux-byte accounting (container BACKING buffers) — lane L3, append-only.
//
// The header-byte counters above cover `HeapHeader.size` only. Containers
// keep their element storage in SEPARATE allocations (`RuntimeArray.data`,
// `RuntimeDict.data`); collection modules call these hooks at their buffer
// alloc/realloc/free sites so those bytes are visible too. Strings and
// tuples store data INLINE after the header (covered by `size`), so they
// need no aux wiring. Hot-path contract: relaxed atomics only, no locks,
// no allocation.
// ============================================================================

static AUX_LIVE_BYTES: AtomicU64 = AtomicU64::new(0);
static AUX_KIND_LIVE_BYTES: [AtomicU64; HEAP_KIND_SLOTS] = [const { AtomicU64::new(0) }; HEAP_KIND_SLOTS];

/// Record `bytes` of newly allocated container backing storage for `kind`
/// (a `HeapObjectType` tag). Called on create and on the grown size of a
/// realloc (pair with `note_aux_free` of the old size).
#[inline]
pub fn note_aux_alloc(kind: u8, bytes: u64) {
    AUX_LIVE_BYTES.fetch_add(bytes, Ordering::Relaxed);
    if let Some(slot) = AUX_KIND_LIVE_BYTES.get(kind as usize) {
        slot.fetch_add(bytes, Ordering::Relaxed);
    }
}

/// Record `bytes` of released container backing storage for `kind`.
#[inline]
pub fn note_aux_free(kind: u8, bytes: u64) {
    AUX_LIVE_BYTES.fetch_sub(bytes, Ordering::Relaxed);
    if let Some(slot) = AUX_KIND_LIVE_BYTES.get(kind as usize) {
        slot.fetch_sub(bytes, Ordering::Relaxed);
    }
}

/// Live container backing-buffer bytes across all kinds (excludes header
/// bytes — see `rt_heap_live_bytes` for those).
#[no_mangle]
pub extern "C" fn rt_heap_aux_live_bytes() -> i64 {
    AUX_LIVE_BYTES.load(Ordering::Relaxed) as i64
}

/// Live backing-buffer bytes for one `HeapObjectType` tag (0 for
/// out-of-range kinds).
#[no_mangle]
pub extern "C" fn rt_heap_aux_live_bytes_by_kind(kind: i64) -> i64 {
    AUX_KIND_LIVE_BYTES
        .get(kind as usize)
        .map(|slot| slot.load(Ordering::Relaxed) as i64)
        .unwrap_or(0)
}

/// Total live array element-buffer CAPACITY bytes. Arrays never shrink their
/// backing buffer, so capacity-vs-length drift (e.g. `clear()` keeping a big
/// buffer) shows up here while object counts stay flat.
#[no_mangle]
pub extern "C" fn rt_heap_array_capacity_bytes() -> i64 {
    AUX_KIND_LIVE_BYTES[HeapObjectType::Array as usize].load(Ordering::Relaxed) as i64
}

// ---------------------------------------------------------------------------
// Per-owner allocation attribution (plan M1).
// Gated: SIMPLE_MEM_ATTR=1 or mem_attr_enable(); OFF by default, and the off
// path is a single cached-bool check — no lock, no map, no TL write.
// ---------------------------------------------------------------------------

static ATTR_ENABLED: OnceLock<bool> = OnceLock::new();

#[inline]
fn mem_attr_enabled() -> bool {
    *ATTR_ENABLED
        .get_or_init(|| std::env::var("SIMPLE_MEM_ATTR").map(|v| v == "1").unwrap_or(false))
}

/// Programmatic enable (CLI/--mem-infra path, and tests). Must run before the
/// first allocation to win the OnceLock; later calls are no-ops.
pub fn mem_attr_enable() {
    let _ = ATTR_ENABLED.set(true);
}

// Per-owner counters live behind an `RwLock<AttrRegistry>`, but the hot
// alloc/free path now avoids taking that lock at all (see M2 note below) —
// it only exists for the rare "brand-new owner name" write and for
// `owner_report`'s read. Registration takes the write lock; everything else
// resolves through per-thread caches into stable-address atomics.
//
// M2 (this lane): a prior revision took a `read()` lock on *every*
// alloc/free to index `counters`, plus a second, independent `Mutex` lock
// for the by-ptr map — 4 lock ops per alloc+free pair. Measured ON overhead
// was ~80-120%, WORSE than the original M1 single-mutex design's 36.6%,
// because splitting counters and by-ptr into two separately-locked
// structures *increased* the total number of synchronization operations in
// the single-thread/uncontended case (which is what the alloc-heavy probe
// exercises) — RwLock::read() is not free just because it's shared.
//
// Fix: `counters` is `Vec<Box<OwnerCounters>>` so each owner's counters have
// a STABLE heap address for the lifetime of the process (the Vec's own
// backing buffer may move on growth, but the boxed `OwnerCounters` it points
// to never does — same reasoning as Rust's own `Box`-stability guarantee).
// `set_current_owner` (called on module/owner switch, not per-allocation)
// resolves the owner id AND caches a raw `*const OwnerCounters` address in a
// thread-local. `note_attr_alloc` then updates counters via that cached
// pointer with zero locks. `note_attr_free` stores the SAME resolved
// counters address (not just an owner id) in the by-ptr map, so freeing
// also never touches `ATTR_REGISTRY` — only the by-ptr shard mutex remains,
// which is unavoidable (the freeing thread has no other way to learn which
// owner allocated a given pointer).
struct OwnerCounters {
    live: AtomicI64,
    peak: AtomicI64,
    allocs: AtomicU64,
}

impl OwnerCounters {
    fn new() -> Self {
        Self { live: AtomicI64::new(0), peak: AtomicI64::new(0), allocs: AtomicU64::new(0) }
    }
}

struct AttrRegistry {
    ids: std::collections::HashMap<String, u32>,
    names: Vec<String>,
    // Boxed so each entry's address is stable across `Vec` growth — raw
    // pointers to these are cached in thread-locals and in the by-ptr map.
    counters: Vec<Box<OwnerCounters>>,
}

static ATTR_REGISTRY: OnceLock<RwLock<AttrRegistry>> = OnceLock::new();

const BY_PTR_SHARDS: usize = 16;

/// Fast, non-cryptographic hasher for `usize` heap-pointer keys. The by-ptr
/// map is an internal profiling structure never exposed to untrusted input,
/// so SipHash's DoS resistance is pure overhead here; one multiply spreads
/// alignment-clustered heap addresses across buckets well enough.
#[derive(Default)]
struct PtrHasher(u64);

impl std::hash::Hasher for PtrHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        // HashMap<usize, _> always calls write_usize; this fallback only
        // fires if that internal detail ever changes, so keep it correct
        // (fold the bytes) rather than merely present.
        let mut acc = self.0;
        for &b in bytes {
            acc = (acc ^ b as u64).wrapping_mul(0x100000001B3);
        }
        self.0 = acc;
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.0 = (i as u64 >> 3).wrapping_mul(0x9E3779B97F4A7C15);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

type PtrHashBuilder = std::hash::BuildHasherDefault<PtrHasher>;
/// by-ptr map value: the resolved owner's `*const OwnerCounters` address (0
/// is never a valid heap allocation, so it's unused as a sentinel here —
/// every insert stores a real, already-resolved counters pointer).
type PtrOwnerMap = std::collections::HashMap<usize, usize, PtrHashBuilder>;

static ATTR_BY_PTR: OnceLock<Vec<Mutex<PtrOwnerMap>>> = OnceLock::new();

thread_local! {
    static ATTR_CURRENT_OWNER: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    // Cached `*const OwnerCounters as usize` for `ATTR_CURRENT_OWNER`. 0
    // means "not yet resolved on this thread" (never a valid address) —
    // resolved lazily on first use so a thread that never calls
    // `set_current_owner` still attributes to the default "<unattributed>"
    // owner instead of silently dropping the count.
    static ATTR_CURRENT_COUNTERS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn attr_registry() -> &'static RwLock<AttrRegistry> {
    ATTR_REGISTRY.get_or_init(|| {
        let mut ids = std::collections::HashMap::new();
        ids.insert("<unattributed>".to_string(), 0u32);
        RwLock::new(AttrRegistry {
            ids,
            names: vec!["<unattributed>".to_string()],
            counters: vec![Box::new(OwnerCounters::new())],
        })
    })
}

#[inline]
fn counters_addr(reg: &AttrRegistry, id: u32) -> usize {
    reg.counters.get(id as usize).map(|b| &**b as *const OwnerCounters as usize).unwrap_or(0)
}

fn attr_by_ptr_shards() -> &'static Vec<Mutex<PtrOwnerMap>> {
    ATTR_BY_PTR.get_or_init(|| (0..BY_PTR_SHARDS).map(|_| Mutex::new(PtrOwnerMap::default())).collect())
}

#[inline]
fn attr_by_ptr_shard(ptr: usize) -> &'static Mutex<PtrOwnerMap> {
    // Heap pointers are alignment-clustered (low bits mostly constant), so
    // mix before taking the top bits to spread shards evenly.
    let mixed = (ptr as u64 >> 4).wrapping_mul(0x9E3779B97F4A7C15);
    let idx = (mixed >> 60) as usize % BY_PTR_SHARDS;
    &attr_by_ptr_shards()[idx]
}

/// Set the attribution owner for subsequent allocations on this thread.
/// Callers (interpreter module switch, .spl via rt_mem_attr_set_owner) may
/// call unconditionally — the disabled path returns immediately.
pub fn set_current_owner(name: &str) {
    if !mem_attr_enabled() {
        return;
    }
    let name = if name.is_empty() { "<entry>" } else { name };
    let reg = attr_registry();
    if let Ok(r) = reg.read() {
        if let Some(&id) = r.ids.get(name) {
            let addr = counters_addr(&r, id);
            ATTR_CURRENT_OWNER.with(|c| c.set(id));
            ATTR_CURRENT_COUNTERS.with(|c| c.set(addr));
            return;
        }
    }
    let (id, addr) = {
        let Ok(mut w) = reg.write() else { return };
        if let Some(&id) = w.ids.get(name) {
            let addr = counters_addr(&w, id);
            (id, addr)
        } else {
            let id = w.names.len() as u32;
            w.ids.insert(name.to_string(), id);
            w.names.push(name.to_string());
            w.counters.push(Box::new(OwnerCounters::new()));
            let addr = counters_addr(&w, id);
            (id, addr)
        }
    };
    ATTR_CURRENT_OWNER.with(|c| c.set(id));
    ATTR_CURRENT_COUNTERS.with(|c| c.set(addr));
}

#[inline]
pub fn current_owner_id() -> u32 {
    ATTR_CURRENT_OWNER.with(|c| c.get())
}

/// Resolve (and cache) this thread's current owner counters address without
/// requiring a prior `set_current_owner` call. Cold path: runs at most once
/// per thread (until the owner changes), guarded by the `!= 0` cache check.
#[cold]
fn resolve_current_counters_cold() -> usize {
    let id = ATTR_CURRENT_OWNER.with(|c| c.get());
    let addr = attr_registry().read().ok().map(|r| counters_addr(&r, id)).unwrap_or(0);
    if addr != 0 {
        ATTR_CURRENT_COUNTERS.with(|c| c.set(addr));
    }
    addr
}

#[inline]
fn note_attr_alloc(ptr: usize, bytes: u64) {
    if !mem_attr_enabled() {
        return;
    }
    let addr = ATTR_CURRENT_COUNTERS.with(|c| {
        let v = c.get();
        if v != 0 { v } else { resolve_current_counters_cold() }
    });
    if addr != 0 {
        // SAFETY: `addr` came from a live `Box<OwnerCounters>` inside
        // `ATTR_REGISTRY.counters`, which only ever grows (never removes or
        // moves its elements — see the M2 comment above), so the pointee
        // stays valid for the rest of the process.
        let counters = unsafe { &*(addr as *const OwnerCounters) };
        let live = counters.live.fetch_add(bytes as i64, Ordering::Relaxed) + bytes as i64;
        counters.peak.fetch_max(live, Ordering::Relaxed);
        counters.allocs.fetch_add(1, Ordering::Relaxed);
    }
    if let Ok(mut m) = attr_by_ptr_shard(ptr).lock() {
        m.insert(ptr, addr);
    }
}

#[inline]
fn note_attr_free(ptr: usize, bytes: u64) {
    if !mem_attr_enabled() {
        return;
    }
    let addr = {
        let Ok(mut m) = attr_by_ptr_shard(ptr).lock() else { return };
        m.remove(&ptr)
    };
    let Some(addr) = addr else { return };
    if addr != 0 {
        // SAFETY: same as `note_attr_alloc` — `addr` was resolved from the
        // registry at alloc time and the pointee is never moved or freed.
        let counters = unsafe { &*(addr as *const OwnerCounters) };
        counters.live.fetch_sub(bytes as i64, Ordering::Relaxed);
    }
}

/// Top-`n` owners by live bytes as "name\tlive\tpeak\tallocs" rows.
pub fn owner_report(n: usize) -> String {
    let Ok(r) = attr_registry().read() else {
        return String::new();
    };
    let mut idx: Vec<usize> = (0..r.names.len()).collect();
    idx.sort_by_key(|&i| -r.counters[i].live.load(Ordering::Relaxed));
    idx.iter()
        .take(n)
        .map(|&i| {
            let c = &r.counters[i];
            format!(
                "{}\t{}\t{}\t{}",
                r.names[i],
                c.live.load(Ordering::Relaxed),
                c.peak.load(Ordering::Relaxed),
                c.allocs.load(Ordering::Relaxed)
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[no_mangle]
pub extern "C" fn rt_mem_attr_enabled() -> i64 {
    mem_attr_enabled() as i64
}

/// # Safety
/// `name_ptr` must point at `name_len` valid UTF-8 bytes, or be null (in which
/// case the call is a no-op). This matches the calling convention native
/// codegen uses for `text` extern parameters — a raw (ptr, len) byte-span
/// pair, not a NUL-terminated C string — the same convention used by
/// `rt_file_exists`/`rt_env_get`/etc. in `sffi/`.
#[no_mangle]
pub unsafe extern "C" fn rt_mem_attr_set_owner(name_ptr: *const u8, name_len: u64) {
    if name_ptr.is_null() || !mem_attr_enabled() {
        return;
    }
    let bytes = std::slice::from_raw_parts(name_ptr, name_len as usize);
    if let Ok(name) = std::str::from_utf8(bytes) {
        set_current_owner(name);
    }
}

/// Print the top-`n` owner report to stdout (stable extern surface for .spl
/// until the mem CLI grows a structured channel).
#[no_mangle]
pub extern "C" fn rt_mem_attr_report_print(n: i64) {
    println!("{}", owner_report(n.max(0) as usize));
}

#[cfg(test)]
mod attr_tests {
    use super::*;

    #[test]
    fn owner_attribution_orders_by_live_bytes_and_frees_settle() {
        mem_attr_enable();
        set_current_owner("attr_test_mod_a");
        assert_ne!(current_owner_id(), 0);
        note_attr_alloc(0xA110C, 10_000_000);
        set_current_owner("attr_test_mod_b");
        note_attr_alloc(0xB110C, 1_000_000);

        let report = owner_report(16);
        let a = report.find("attr_test_mod_a").expect("mod_a in report");
        let b = report.find("attr_test_mod_b").expect("mod_b in report");
        assert!(a < b, "10MB owner must rank above 1MB owner:\n{report}");

        note_attr_free(0xA110C, 10_000_000);
        let r = attr_registry().read().unwrap();
        let id = r.ids["attr_test_mod_a"] as usize;
        assert_eq!(r.counters[id].live.load(Ordering::Relaxed), 0, "live returns to zero after free");
        assert_eq!(r.counters[id].peak.load(Ordering::Relaxed), 10_000_000, "peak survives the free");
    }

    #[test]
    fn owner_attribution_survives_concurrent_alloc_free_across_threads() {
        // Regression guard for the reverted sharding attempt: peak-per-owner
        // must be the exact single-threaded-equivalent value, not a sum or
        // max of per-shard partials, and by_ptr sharding must never let a
        // free land on the wrong owner's counters.
        mem_attr_enable();
        set_current_owner("attr_test_concurrent");
        let owner = current_owner_id();
        assert_ne!(owner, 0);

        let base: usize = 0xC0FFEE_0000;
        let per_thread = 64usize;
        let threads = 8usize;
        let bytes_each: u64 = 1_000;
        // Barrier forces every thread to finish its allocs before any thread
        // starts freeing, so the true peak (all bytes live at once) is
        // deterministically reached instead of racing frees against allocs.
        let barrier = std::sync::Barrier::new(threads);

        std::thread::scope(|scope| {
            for t in 0..threads {
                let barrier = &barrier;
                scope.spawn(move || {
                    set_current_owner("attr_test_concurrent");
                    for i in 0..per_thread {
                        let ptr = base + (t * per_thread + i) * 8;
                        note_attr_alloc(ptr, bytes_each);
                    }
                    barrier.wait();
                    for i in 0..per_thread {
                        let ptr = base + (t * per_thread + i) * 8;
                        note_attr_free(ptr, bytes_each);
                    }
                });
            }
        });

        let r = attr_registry().read().unwrap();
        let id = r.ids["attr_test_concurrent"] as usize;
        assert_eq!(r.counters[id].live.load(Ordering::Relaxed), 0, "all allocs freed: live must settle to 0");
        assert_eq!(
            r.counters[id].peak.load(Ordering::Relaxed),
            (threads * per_thread) as i64 * bytes_each as i64,
            "peak must equal the true global high-water mark, not a per-shard approximation"
        );
        assert_eq!(r.counters[id].allocs.load(Ordering::Relaxed), (threads * per_thread) as u64);
    }

    // Manual overhead probe (`#[ignore]`d so normal `cargo test` never runs
    // it — it must run alone in its own process to get a clean ATTR_ENABLED
    // latch). Invoke directly:
    //   cargo test --release -p simple-runtime --lib \
    //     heap::attr_tests::bench_off_overhead -- --ignored --nocapture
    //   SIMPLE_MEM_ATTR=1 cargo test --release -p simple-runtime --lib \
    //     heap::attr_tests::bench_on_overhead -- --ignored --nocapture
    #[test]
    #[ignore]
    fn bench_off_overhead() {
        assert!(!mem_attr_enabled(), "run this probe with SIMPLE_MEM_ATTR unset");
        let n = 1_000_000usize;
        let start = std::time::Instant::now();
        for i in 0..n {
            note_attr_alloc(0x1000 + i, 64);
            note_attr_free(0x1000 + i, 64);
        }
        let elapsed = start.elapsed();
        eprintln!("OFF: {n} alloc+free pairs in {elapsed:?} ({:.1} ns/pair)", elapsed.as_nanos() as f64 / n as f64);
    }

    #[test]
    #[ignore]
    fn bench_on_overhead() {
        mem_attr_enable();
        assert!(mem_attr_enabled(), "run this probe with SIMPLE_MEM_ATTR=1");
        set_current_owner("bench_owner");
        let n = 1_000_000usize;
        let start = std::time::Instant::now();
        for i in 0..n {
            note_attr_alloc(0x1000 + i, 64);
            note_attr_free(0x1000 + i, 64);
        }
        let elapsed = start.elapsed();
        eprintln!("ON: {n} alloc+free pairs in {elapsed:?} ({:.1} ns/pair)", elapsed.as_nanos() as f64 / n as f64);
    }

    // Same shape as the M1 "alloc-heavy probe" this lane targets: drives
    // real heap-registered allocations (malloc + HEAP_ALLOCATION_REGISTRY
    // mutex + note_heap_alloc/free) through register/unregister_heap_ptr, so
    // the reported percentage is ON-vs-OFF over the *whole* alloc/free path,
    // not just the attribution call in isolation.
    //   cargo test --release -p simple-runtime --lib \
    //     heap::attr_tests::bench_alloc_heavy_off -- --ignored --nocapture
    //   SIMPLE_MEM_ATTR=1 cargo test --release -p simple-runtime --lib \
    //     heap::attr_tests::bench_alloc_heavy_on -- --ignored --nocapture
    fn alloc_heavy_loop(n: usize) -> std::time::Duration {
        let start = std::time::Instant::now();
        for _ in 0..n {
            let ptr = Box::into_raw(Box::new(HeapHeader::new(HeapObjectType::Object, 64)));
            register_heap_ptr(ptr);
            unregister_heap_ptr(ptr);
            unsafe { drop(Box::from_raw(ptr)) };
        }
        start.elapsed()
    }

    #[test]
    #[ignore]
    fn bench_alloc_heavy_off() {
        assert!(!mem_attr_enabled(), "run this probe with SIMPLE_MEM_ATTR unset");
        let n = 1_000_000usize;
        let elapsed = alloc_heavy_loop(n);
        eprintln!("ALLOC-HEAVY OFF: {n} alloc+free in {elapsed:?} ({:.1} ns/pair)", elapsed.as_nanos() as f64 / n as f64);
    }

    #[test]
    #[ignore]
    fn bench_alloc_heavy_on() {
        mem_attr_enable();
        assert!(mem_attr_enabled(), "run this probe with SIMPLE_MEM_ATTR=1");
        set_current_owner("bench_owner");
        let n = 1_000_000usize;
        let elapsed = alloc_heavy_loop(n);
        eprintln!("ALLOC-HEAVY ON: {n} alloc+free in {elapsed:?} ({:.1} ns/pair)", elapsed.as_nanos() as f64 / n as f64);
    }
}
