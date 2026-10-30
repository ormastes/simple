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
    /// Heap-backed full-width unsigned integer at erased RuntimeValue boundaries.
    UInt = 0x1D,
    /// Heap-backed full-width SIGNED integer. The inline TAG_INT representation
    /// is `v << 3`, which keeps only a 61-bit payload; wide values box here.
    /// Deliberately NOT `UInt`: that variant formats via `u64::to_string`, which
    /// would print every wide NEGATIVE i64 as a huge positive number.
    Int = 0x1E,
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

/// Heap-boxed u64. This is a leaf object, like `HeapFloat`.
#[repr(C)]
pub struct HeapUInt {
    pub header: HeapHeader,
    pub value: u64,
}

/// Heap-boxed full-width signed i64 (see `HeapObjectType::Int`). A leaf object,
/// same shape as `HeapUInt` but carrying signed semantics.
#[repr(C)]
pub struct HeapInt {
    pub header: HeapHeader,
    pub value: i64,
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
    /// Set together with `U64_PACKED` when a tagged array was packed in place
    /// by a typed signed-word store (`rt_typed_words_i64_*`). The words keep the
    /// SIGNED i64 semantics the tagged layout had, so generic consumers that do
    /// not understand the packed layout unpack the array back first
    /// (`unpack_lazy_words`) instead of reading raw words as tagged values.
    pub const LAZY_WORDS: u8 = 0b10_0000;
    /// Set when a `LAZY_WORDS` array was unpacked by a consumer that does not
    /// understand the packed layout. Such an array is never packed again, so a
    /// store / generic-consumer loop cannot re-box the whole array every
    /// iteration (it degrades to the pre-lane behaviour: one box per wide store).
    pub const NO_REPACK: u8 = 0b100_0000;
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
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, AtomicU8, Ordering};
use std::sync::{Mutex, OnceLock};

const MIN_VALID_HEAP_ADDR: usize = 4096;

/// Membership-only set keyed by heap addresses. The default SipHash `RandomState`
/// buys DoS resistance that pointer keys do not need, and every validated
/// heap access (`validate_heap_obj`, e.g. each `rt_array_get`) hashes once:
/// measured 2026-10-09 on a Windows stage2 cold parse, SipHash alone was ~39%
/// of compiler CPU. aHash with fixed keys keeps the exact same membership
/// semantics and table layout.
pub(crate) type HeapPtrSet<K> = HashSet<K, std::hash::BuildHasherDefault<ahash::AHasher>>;

/// The allocation registry is split into address-hashed shards, each with
/// its own lock and its own free epoch on its own cache lines. One global
/// mutex serialized every allocation/free/validation miss across all worker
/// threads (bouncing one line between sockets on the 2-socket build host),
/// and one global free epoch meant a free on ANY thread invalidated EVERY
/// thread's validation cache. Membership semantics are unchanged: an address
/// lives in exactly one shard, chosen by the address alone.
const HEAP_REGISTRY_SHARDS: usize = 64;

#[repr(align(128))]
struct HeapRegistryShard {
    set: Mutex<HeapRegistry>,
    /// Bumped (under this shard's lock) by every erase in this shard.
    epoch: AtomicU64,
}

static HEAP_ALLOCATION_REGISTRY: OnceLock<Box<[HeapRegistryShard]>> = OnceLock::new();

/// Live-heap membership set (one per registry shard), fork-aware.
///
/// A copy-on-write fork child (`rt_fork_shared_heap_v1`, the MIR fork
/// workers) inherits a registry holding every parent object. Writing that
/// inherited table privatizes it page by page, and its first growth allocates
/// a fresh 2x table: measured on a 2-worker probe, each child mapped a new
/// 147,460 kB private table (2^24 buckets) and freed the inherited 2^23 one;
/// on the 1471-module Phase 3 closure the same step is ~4.8 GB per child, in
/// lockstep across all workers (bug
/// doc/08_tracking/bug/mir_fork_child_heap_registry_cow_resize_2026-10-25.md).
/// After `freeze_for_fork_child` the inherited table is read-only: the
/// child's own objects go into `live`, and an erase of an inherited object is
/// recorded in `frozen_erased`. Membership is unchanged.
#[derive(Default)]
pub(crate) struct HeapRegistry {
    live: HeapPtrSet<usize>,
    frozen: Option<HeapPtrSet<usize>>,
    frozen_erased: HeapPtrSet<usize>,
}

impl HeapRegistry {
    #[inline]
    fn frozen_has(&self, addr: usize) -> bool {
        match &self.frozen {
            Some(frozen) => {
                frozen.contains(&addr) && (self.frozen_erased.is_empty() || !self.frozen_erased.contains(&addr))
            }
            None => false,
        }
    }

    #[inline]
    pub(crate) fn contains(&self, addr: &usize) -> bool {
        self.live.contains(addr) || self.frozen_has(*addr)
    }

    /// True when `addr` was not registered before this call.
    #[inline]
    pub(crate) fn insert(&mut self, addr: usize) -> bool {
        if let Some(frozen) = &self.frozen {
            if frozen.contains(&addr) {
                // An inherited address re-registered after its erase.
                return self.frozen_erased.remove(&addr);
            }
        }
        self.live.insert(addr)
    }

    /// True when THIS call erased `addr`.
    #[inline]
    pub(crate) fn remove(&mut self, addr: &usize) -> bool {
        if self.live.remove(addr) {
            return true;
        }
        match &self.frozen {
            Some(frozen) if frozen.contains(addr) => self.frozen_erased.insert(*addr),
            _ => false,
        }
    }

    pub(crate) fn len(&self) -> usize {
        let inherited = self.frozen.as_ref().map_or(0, |frozen| frozen.len());
        self.live.len() + inherited - self.frozen_erased.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &usize> + '_ {
        self.frozen
            .iter()
            .flat_map(|frozen| frozen.iter())
            .filter(|addr| !self.frozen_erased.contains(*addr))
            .chain(self.live.iter())
    }

    pub(crate) fn clear(&mut self) {
        self.live.clear();
        self.frozen = None;
        self.frozen_erased.clear();
    }

    /// Freeze the inherited table in a fork child. A nested fork keeps the
    /// first frozen layer and inherits the (small) overlay unchanged.
    fn freeze_for_fork_child(&mut self) {
        if self.frozen.is_none() {
            self.frozen = Some(std::mem::take(&mut self.live));
        }
    }
}

/// Called in the child immediately after `fork()` (single-threaded there).
/// Freezes every shard's inherited table; membership (and so every shard's
/// free epoch) is unchanged.
pub(crate) fn heap_registry_freeze_for_fork_child() {
    for shard in heap_registry_shards() {
        shard
            .set
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .freeze_for_fork_child();
    }
}

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

// Counters are STRIPED: each thread writes only its own cache-line-aligned
// stripe (relaxed adds on an uncontended line), and readers sum the stripes.
// One global set of atomics bounced the same lines between every allocating
// thread (and across sockets on the 2-socket build host). An object freed on
// another thread decrements that thread's stripe, so a single stripe may go
// negative; only the sum is meaningful, so stripes hold wrapping u64 deltas.
const HEAP_COUNTER_STRIPES: usize = 64;
/// Peak is refreshed (one sum over the stripes + fetch_max) every this many
/// allocations per thread and on every peak read, so the reported high-water
/// mark can trail the true instantaneous peak by at most that window.
const HEAP_PEAK_SAMPLE_EVERY: u32 = 1024;

#[repr(align(128))]
struct HeapCounterStripe {
    live_bytes: AtomicU64,
    total_allocs: AtomicU64,
    total_frees: AtomicU64,
    kind_live_count: [AtomicU64; HEAP_KIND_SLOTS],
    kind_live_bytes: [AtomicU64; HEAP_KIND_SLOTS],
}

static HEAP_COUNTER_STRIPES_TABLE: [HeapCounterStripe; HEAP_COUNTER_STRIPES] = [const {
    HeapCounterStripe {
        live_bytes: AtomicU64::new(0),
        total_allocs: AtomicU64::new(0),
        total_frees: AtomicU64::new(0),
        kind_live_count: [const { AtomicU64::new(0) }; HEAP_KIND_SLOTS],
        kind_live_bytes: [const { AtomicU64::new(0) }; HEAP_KIND_SLOTS],
    }
}; HEAP_COUNTER_STRIPES];
static HEAP_PEAK_BYTES: AtomicU64 = AtomicU64::new(0);
static HEAP_NEXT_STRIPE: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static HEAP_STRIPE: Cell<(usize, u32)> = const { Cell::new((usize::MAX, 0)) };
}

/// This thread's stripe, plus whether this allocation should refresh the peak.
#[inline]
fn heap_counter_stripe(count_alloc: bool) -> (&'static HeapCounterStripe, bool) {
    let (index, sample) = HEAP_STRIPE
        .try_with(|cell| {
            let (mut index, mut ticks) = cell.get();
            if index == usize::MAX {
                index = HEAP_NEXT_STRIPE.fetch_add(1, Ordering::Relaxed) as usize % HEAP_COUNTER_STRIPES;
            }
            let mut sample = false;
            if count_alloc {
                ticks += 1;
                if ticks >= HEAP_PEAK_SAMPLE_EVERY {
                    ticks = 0;
                    sample = true;
                }
            }
            cell.set((index, ticks));
            (index, sample)
        })
        // TLS torn down (thread exit): stripe 0, always refresh the peak.
        .unwrap_or((0, true));
    (&HEAP_COUNTER_STRIPES_TABLE[index], sample)
}

#[inline]
fn heap_counter_sum(read: impl Fn(&HeapCounterStripe) -> &AtomicU64) -> u64 {
    HEAP_COUNTER_STRIPES_TABLE
        .iter()
        .fold(0u64, |acc, stripe| acc.wrapping_add(read(stripe).load(Ordering::Relaxed)))
}

fn heap_refresh_peak() -> u64 {
    let live = heap_counter_sum(|stripe| &stripe.live_bytes);
    // A transiently negative sum (frees counted before their allocs on
    // another stripe) wraps to a huge u64; it is not a real peak.
    if (live as i64) >= 0 {
        HEAP_PEAK_BYTES.fetch_max(live, Ordering::Relaxed);
    }
    live
}

#[inline]
fn note_heap_alloc(kind: u8, bytes: u64) {
    let (stripe, sample) = heap_counter_stripe(true);
    stripe.total_allocs.fetch_add(1, Ordering::Relaxed);
    stripe.live_bytes.fetch_add(bytes, Ordering::Relaxed);
    if let Some(slot) = stripe.kind_live_count.get(kind as usize) {
        slot.fetch_add(1, Ordering::Relaxed);
    }
    if let Some(slot) = stripe.kind_live_bytes.get(kind as usize) {
        slot.fetch_add(bytes, Ordering::Relaxed);
    }
    if sample {
        heap_refresh_peak();
    }
}

#[inline]
fn note_heap_free(kind: u8, bytes: u64) {
    let (stripe, _) = heap_counter_stripe(false);
    stripe.total_frees.fetch_add(1, Ordering::Relaxed);
    stripe.live_bytes.fetch_sub(bytes, Ordering::Relaxed);
    if let Some(slot) = stripe.kind_live_count.get(kind as usize) {
        slot.fetch_sub(1, Ordering::Relaxed);
    }
    if let Some(slot) = stripe.kind_live_bytes.get(kind as usize) {
        slot.fetch_sub(bytes, Ordering::Relaxed);
    }
}

/// Header addresses of every live array carrying `LAZY_WORDS`. Taken under the
/// registry lock (registered == live), used when user threads start.
pub(crate) fn live_lazy_word_arrays() -> Vec<usize> {
    // A poisoned lock still guards a consistent set: packed arrays must be found.
    let mut out = Vec::new();
    for shard in heap_registry_shards() {
        let registry = shard.set.lock().unwrap_or_else(|e| e.into_inner());
        out.extend(registry.iter().copied().filter(|addr| unsafe {
            let header = *addr as *const HeapHeader;
            (*header).object_type == HeapObjectType::Array && (*header).gc_flags & gc_flags::LAZY_WORDS != 0
        }));
    }
    out
}

fn heap_registry_shards() -> &'static [HeapRegistryShard] {
    HEAP_ALLOCATION_REGISTRY.get_or_init(|| {
        (0..HEAP_REGISTRY_SHARDS)
            .map(|_| HeapRegistryShard {
                set: Mutex::new(HeapRegistry::default()),
                // Starts at 1 so the zeroed validation cache never matches.
                epoch: AtomicU64::new(1),
            })
            .collect()
    })
}

#[inline]
pub(crate) fn heap_registry_shard_index(addr: usize) -> usize {
    let mixed = ((addr >> 3) as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    (mixed >> 58) as usize & (HEAP_REGISTRY_SHARDS - 1)
}

#[inline]
fn heap_registry_shard(addr: usize) -> &'static HeapRegistryShard {
    &heap_registry_shards()[heap_registry_shard_index(addr)]
}

/// A pointer that a locked probe found registered at its shard's epoch E is
/// still registered while that shard's epoch is E, so a per-thread
/// `(addr, epoch)` cache answers repeat validations without the mutex or a
/// probe into the ever-growing set. That probe was ~half of the Windows
/// stage2 full-CLI parse and HIR profiles (cdb samples, 2026-10-18).
const VALIDATED_SLOTS: usize = 1 << 12;

thread_local! {
    static VALIDATED: [Cell<(usize, u64)>; VALIDATED_SLOTS] =
        const { [const { Cell::new((0, 0)) }; VALIDATED_SLOTS] };
}

#[inline]
fn validated_slot(addr: usize) -> usize {
    ((addr >> 4) ^ (addr >> 16)) & (VALIDATED_SLOTS - 1)
}

#[inline]
fn validated_cached(addr: usize, epoch: u64) -> bool {
    VALIDATED
        .try_with(|cache| cache[validated_slot(addr)].get() == (addr, epoch))
        .unwrap_or(false)
}

#[inline]
fn validated_remember(addr: usize, epoch: u64) {
    let _ = VALIDATED.try_with(|cache| cache[validated_slot(addr)].set((addr, epoch)));
}


#[inline]
pub fn register_heap_ptr(ptr: *mut HeapHeader) {
    if !ptr.is_null() {
        let shard = heap_registry_shard(ptr as usize);
        let epoch = shard.epoch.load(Ordering::Acquire);
        let inserted = shard
            .set
            .lock()
            .map(|mut registry| registry.insert(ptr as usize))
            .unwrap_or(false);
        if inserted {
            validated_remember(ptr as usize, epoch);
            // Caller just allocated the object; header is valid by contract.
            let (kind, bytes) = unsafe { ((*ptr).object_type as u8, (*ptr).size as u64) };
            super::dict_scope_read::registered(ptr as usize, kind, bytes as u32);
            note_heap_alloc(kind, bytes);
            note_attr_alloc(ptr as usize, bytes);
        }
    }
}

#[inline]
pub fn unregister_heap_ptr(ptr: *mut HeapHeader) {
    if !ptr.is_null() {
        let shard = heap_registry_shard(ptr as usize);
        let removed = shard
            .set
            .lock()
            .map(|mut registry| {
            let removed = registry.remove(&(ptr as usize));
            if removed {
                shard.epoch.fetch_add(1, Ordering::AcqRel);
            }
            removed
        })
            .unwrap_or(false);
        if removed {
            // Presence in the registry means not yet freed (the erasing call
            // is the one allowed to free), so this read is not use-after-free.
            let (kind, bytes) = unsafe { ((*ptr).object_type as u8, (*ptr).size as u64) };
            super::dict_scope_read::unregistered(ptr as usize, kind);
            note_heap_free(kind, bytes);
            note_attr_free(ptr as usize, bytes);
            super::collections::transient_promote_share_forget(ptr as usize);
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
    let shard = heap_registry_shard(ptr as usize);
    let removed = shard
        .set
        .lock()
        .map(|mut registry| {
            let removed = registry.remove(&(ptr as usize));
            if removed {
                shard.epoch.fetch_add(1, Ordering::AcqRel);
            }
            removed
        })
        .unwrap_or(false);
    if removed {
        let (kind, bytes) = unsafe { ((*ptr).object_type as u8, (*ptr).size as u64) };
        super::dict_scope_read::unregistered(ptr as usize, kind);
        note_heap_free(kind, bytes);
        note_attr_free(ptr as usize, bytes);
        super::collections::transient_promote_share_forget(ptr as usize);
    }
    removed
}

/// Candidates erased per registry lock hold in `unregister_heap_ptrs_batch`.
/// Bounds how long other threads' registrations and validations wait
/// (~50 ns/candidate measured => a few ms per chunk).
pub(crate) const HEAP_UNREGISTER_BATCH_CHUNK: usize = 1 << 16;

/// Batch `unregister_heap_ptr_checked` for a transient scope end: one shard
/// lock and one shard epoch bump per `HEAP_UNREGISTER_BATCH_CHUNK` of that
/// shard's candidates, instead of a lock round-trip (plus a validation probe
/// that always misses, because every per-object erase bumps the shard epoch)
/// per object.
///
/// For each candidate that passes the same address checks as
/// `RuntimeValue::heap_type` and is registered, `select` is asked, under the
/// lock, whether to erase it; `select` sees a live header (registered ==
/// live, and every free erases under this lock first) and must not take any
/// lock. Erased pointers are pushed to `out` with their kind; exactly one
/// caller ever erases a given pointer, so each is the caller's to free.
///
/// The caller must free `out` only after this returns, never between
/// chunks: an erased-but-unfreed address cannot be recycled by another
/// thread, so a stale duplicate of it later in `candidates` (an object freed
/// and its address reused mid-scope) finds it unregistered and is skipped.
/// Accounting and the share-window erase run after the last lock release, as
/// in the single-pointer path.
pub(crate) fn unregister_heap_ptrs_batch(
    candidates: &[super::core::RuntimeValue],
    mut select: impl FnMut(super::core::RuntimeValue, *mut HeapHeader) -> bool,
    out: &mut Vec<(*mut HeapHeader, HeapObjectType)>,
) {
    let start = out.len();
    // The registry is sharded by address, so candidates are bucketed by shard
    // (scope order kept within a bucket) and each shard is locked once per
    // chunk of its own bucket, bumping only that shard's epoch. Every copy of
    // an address lands in the same bucket, so the stale-duplicate argument
    // above holds per shard.
    let mut buckets: Vec<Vec<super::core::RuntimeValue>> = vec![Vec::new(); HEAP_REGISTRY_SHARDS];
    for value in candidates {
        if value.is_heap() {
            buckets[heap_registry_shard_index(value.as_heap_ptr() as usize)].push(*value);
        }
    }
    let shards = heap_registry_shards();
    for (index, bucket) in buckets.iter().enumerate() {
        let shard = &shards[index];
        for chunk in bucket.chunks(HEAP_UNREGISTER_BATCH_CHUNK) {
            let chunk_start = out.len();
            // Poisoned: keep the rest of this shard registered (leaked, never
            // freed), as the single-pointer path does; what earlier chunks
            // erased is still ours.
            let Ok(mut registry) = shard.set.lock() else {
                break;
            };
            erase_selected(&mut registry, chunk, &mut select, out);
            if out.len() != chunk_start {
                shard.epoch.fetch_add(1, Ordering::AcqRel);
            }
        }
    }
    for &(ptr, kind) in &out[start..] {
        // Erased by this call and not yet freed, so the header is readable.
        let bytes = unsafe { (*ptr).size as u64 };
        super::dict_scope_read::unregistered(ptr as usize, kind as u8);
        note_heap_free(kind as u8, bytes);
        note_attr_free(ptr as usize, bytes);
        super::collections::transient_promote_share_forget(ptr as usize);
    }
}

/// One locked chunk of `unregister_heap_ptrs_batch`, over the registry it is
/// given (the live one, or a test's frozen fork-child registry).
fn erase_selected(
    registry: &mut HeapRegistry,
    chunk: &[super::core::RuntimeValue],
    select: &mut impl FnMut(super::core::RuntimeValue, *mut HeapHeader) -> bool,
    out: &mut Vec<(*mut HeapHeader, HeapObjectType)>,
) {
    for value in chunk {
        if !value.is_heap() {
            continue;
        }
        let ptr = value.as_heap_ptr();
        let addr = ptr as usize;
        if ptr.is_null() || addr < MIN_VALID_HEAP_ADDR || addr & 0x7 != 0 {
            continue;
        }
        // Erase first (one probe for the common case); a declined object
        // goes straight back. Nobody can observe the gap: the caller holds
        // the lock. In a fork child an inherited erase is an erased-set
        // insert and the put-back its removal, so the frozen table is never
        // written.
        if !registry.remove(&addr) {
            continue;
        }
        if !select(*value, ptr) {
            registry.insert(addr);
            continue;
        }
        out.push((ptr, unsafe { (*ptr).object_type }));
    }
}

#[inline]
pub fn is_registered_heap_ptr(ptr: *mut HeapHeader) -> bool {
    let addr = ptr as usize;
    let shard = heap_registry_shard(addr);
    let epoch = shard.epoch.load(Ordering::Acquire);
    if addr != 0 && validated_cached(addr, epoch) {
        return true;
    }
    let present = shard
        .set
        .lock()
        .map(|registry| registry.contains(&addr))
        .unwrap_or(false);
    if present {
        validated_remember(addr, epoch);
    }
    present
}

/// Number of RuntimeValue heap objects known to the hosted runtime.
///
/// This is a diagnostic registry count, not a live-byte measurement: most
/// no-GC compiler temporaries stay registered for the process lifetime.
#[no_mangle]
pub extern "C" fn rt_heap_registry_count() -> i64 {
    heap_registry_shards()
        .iter()
        .map(|shard| shard.set.lock().map(|registry| registry.len() as i64).unwrap_or(0))
        .sum()
}

pub fn clear_heap_allocation_registry() {
    if let Some(shards) = HEAP_ALLOCATION_REGISTRY.get() {
        for shard in shards.iter() {
            let _ = shard.set.lock().map(|mut registry| {
                registry.clear();
                shard.epoch.fetch_add(1, Ordering::AcqRel);
            });
        }
        super::dict_scope_read::cleared();
    }
    // Peak intentionally survives a clear: it answers "how big did this
    // process get", which a bulk reset must not erase. Fold the pre-clear
    // live total into it first so no sampled window is lost.
    heap_refresh_peak();
    for stripe in HEAP_COUNTER_STRIPES_TABLE.iter() {
        stripe.live_bytes.store(0, Ordering::Relaxed);
        stripe.total_allocs.store(0, Ordering::Relaxed);
        stripe.total_frees.store(0, Ordering::Relaxed);
        for slot in stripe.kind_live_count.iter().chain(stripe.kind_live_bytes.iter()) {
            slot.store(0, Ordering::Relaxed);
        }
    }
}

/// Live heap HEADER bytes currently registered (excludes container backing
/// buffers — see the accounting comment above).
#[no_mangle]
pub extern "C" fn rt_heap_live_bytes() -> i64 {
    heap_counter_sum(|stripe| &stripe.live_bytes) as i64
}

/// High-water mark of `rt_heap_live_bytes` for this process.
#[no_mangle]
pub extern "C" fn rt_heap_peak_bytes() -> i64 {
    heap_refresh_peak();
    HEAP_PEAK_BYTES.load(Ordering::Relaxed) as i64
}

/// Total registered allocations since process start (monotonic).
#[no_mangle]
pub extern "C" fn rt_heap_alloc_count() -> i64 {
    heap_counter_sum(|stripe| &stripe.total_allocs) as i64
}

/// Total unregistered (freed) allocations since process start (monotonic).
#[no_mangle]
pub extern "C" fn rt_heap_free_count() -> i64 {
    heap_counter_sum(|stripe| &stripe.total_frees) as i64
}

/// Live object count for one `HeapObjectType` tag (0 for out-of-range kinds).
#[no_mangle]
pub extern "C" fn rt_heap_live_count_by_kind(kind: i64) -> i64 {
    let kind = kind as usize;
    if kind >= HEAP_KIND_SLOTS {
        return 0;
    }
    heap_counter_sum(|stripe| &stripe.kind_live_count[kind]) as i64
}

/// Live header bytes for one `HeapObjectType` tag (0 for out-of-range kinds).
#[no_mangle]
pub extern "C" fn rt_heap_live_bytes_by_kind(kind: i64) -> i64 {
    let kind = kind as usize;
    if kind >= HEAP_KIND_SLOTS {
        return 0;
    }
    heap_counter_sum(|stripe| &stripe.kind_live_bytes[kind]) as i64
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
    let ptr = validate_heap_obj(val, expected)?;
    if expected == HeapObjectType::Array {
        // A tagged array that a typed signed-word store packed in place is
        // unpacked here, so callers that only understand tagged slots never
        // see raw words. Callers that handle the packed layout use
        // `get_typed_ptr_packed`.
        unsafe { super::collections::unpack_lazy_words(ptr as *mut super::collections::RuntimeArray) };
    }
    Some(ptr as *const T)
}

/// `get_typed_ptr` for callers that handle the packed array layouts themselves
/// (no `LAZY_WORDS` unpacking).
#[inline]
pub fn get_typed_ptr_packed<T>(val: RuntimeValue, expected: HeapObjectType) -> Option<*const T> {
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
    let registry = heap_registry_shard(addr).set.lock().ok()?;
    if !registry.contains(&addr) {
        return None;
    }
    if unsafe { (*ptr).object_type != expected } {
        return None;
    }
    Some(read(ptr as *const T))
}

/// Copy a heap object's type while holding the allocation-registry lock.
/// Safe boundary classifiers use this instead of validating membership and
/// dereferencing the header in two separately synchronized steps.
pub(crate) fn registered_heap_type(val: RuntimeValue) -> Option<HeapObjectType> {
    if !val.is_heap() {
        return None;
    }
    let ptr = val.as_heap_ptr();
    let addr = ptr as usize;
    if ptr.is_null() || addr < MIN_VALID_HEAP_ADDR || addr & 0x7 != 0 {
        return None;
    }
    let shard = heap_registry_shard(addr);
    let epoch = shard.epoch.load(Ordering::Acquire);
    if validated_cached(addr, epoch) {
        // Seqlock re-check: no erase of this address (so no free) happened
        // around the read; erases in other shards cannot free it.
        let object_type = unsafe { std::ptr::read_volatile(&(*ptr).object_type) };
        std::sync::atomic::fence(Ordering::Acquire);
        if shard.epoch.load(Ordering::Relaxed) == epoch {
            return Some(object_type);
        }
    }
    let registry = shard.set.lock().ok()?;
    if !registry.contains(&addr) {
        return None;
    }
    validated_remember(addr, epoch);
    Some(unsafe { (*ptr).object_type })
}

/// Get mutable typed pointer from heap object with validation.
/// Returns None if the value is not a valid heap object of the expected type.
#[inline]
pub fn get_typed_ptr_mut<T>(val: RuntimeValue, expected: HeapObjectType) -> Option<*mut T> {
    let ptr = validate_heap_obj(val, expected)?;
    if expected == HeapObjectType::Array {
        unsafe { super::collections::unpack_lazy_words(ptr as *mut super::collections::RuntimeArray) };
    }
    Some(ptr as *mut T)
}

/// `get_typed_ptr_mut` for callers that handle the packed array layouts
/// themselves (no `LAZY_WORDS` unpacking).
#[inline]
pub fn get_typed_ptr_mut_packed<T>(val: RuntimeValue, expected: HeapObjectType) -> Option<*mut T> {
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
            HeapObjectType::UInt | HeapObjectType::Int => ValueKind::Int,
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

// Tri-state so a programmatic enable is authoritative rather than a race
// against whoever reads the gate first. A `OnceLock<bool>` seeded from the
// environment latched OFF permanently as soon as ANY allocation observed the
// gate before `mem_attr_enable()` ran, silently turning the enable into a
// no-op (test-order dependent, and unfixable from the caller side). The off
// path is still a single relaxed atomic load — no lock, no map, no TL write.
const ATTR_UNRESOLVED: u8 = 0;
const ATTR_OFF: u8 = 1;
const ATTR_ON: u8 = 2;

static ATTR_GATE: AtomicU8 = AtomicU8::new(ATTR_UNRESOLVED);

#[inline]
fn mem_attr_enabled() -> bool {
    match ATTR_GATE.load(Ordering::Relaxed) {
        ATTR_ON => true,
        ATTR_OFF => false,
        _ => {
            let on = std::env::var("SIMPLE_MEM_ATTR").map(|v| v == "1").unwrap_or(false);
            let resolved = if on { ATTR_ON } else { ATTR_OFF };
            // Only fill in from the environment while still unresolved: an
            // explicit `mem_attr_enable()` that raced in must win.
            match ATTR_GATE.compare_exchange(ATTR_UNRESOLVED, resolved, Ordering::Relaxed, Ordering::Relaxed) {
                Ok(_) => on,
                Err(prev) => prev == ATTR_ON,
            }
        }
    }
}

/// Programmatic enable (CLI/--mem-infra path, and tests). Authoritative: it
/// overrides an environment-derived OFF no matter when it runs.
pub fn mem_attr_enable() {
    ATTR_GATE.store(ATTR_ON, Ordering::Relaxed);
}

#[derive(Default)]
struct AttrState {
    ids: std::collections::HashMap<String, u32>,
    names: Vec<String>,
    live: Vec<i64>,
    peak: Vec<i64>,
    allocs: Vec<u64>,
    by_ptr: std::collections::HashMap<usize, u32>,
}

static ATTR_STATE: OnceLock<Mutex<AttrState>> = OnceLock::new();

thread_local! {
    static ATTR_CURRENT_OWNER: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

fn attr_state() -> &'static Mutex<AttrState> {
    ATTR_STATE.get_or_init(|| {
        let mut s = AttrState::default();
        s.ids.insert("<unattributed>".to_string(), 0);
        s.names.push("<unattributed>".to_string());
        s.live.push(0);
        s.peak.push(0);
        s.allocs.push(0);
        Mutex::new(s)
    })
}

/// Set the attribution owner for subsequent allocations on this thread.
/// Callers (interpreter module switch, .spl via rt_mem_attr_set_owner) may
/// call unconditionally — the disabled path returns immediately.
pub fn set_current_owner(name: &str) {
    if !mem_attr_enabled() {
        return;
    }
    let name = if name.is_empty() { "<entry>" } else { name };
    let id = {
        let Ok(mut s) = attr_state().lock() else { return };
        if let Some(&id) = s.ids.get(name) {
            id
        } else {
            let id = s.names.len() as u32;
            s.ids.insert(name.to_string(), id);
            s.names.push(name.to_string());
            s.live.push(0);
            s.peak.push(0);
            s.allocs.push(0);
            id
        }
    };
    ATTR_CURRENT_OWNER.with(|c| c.set(id));
}

#[inline]
pub fn current_owner_id() -> u32 {
    ATTR_CURRENT_OWNER.with(|c| c.get())
}

#[inline]
fn note_attr_alloc(ptr: usize, bytes: u64) {
    if !mem_attr_enabled() {
        return;
    }
    let owner = ATTR_CURRENT_OWNER.with(|c| c.get()) as usize;
    if let Ok(mut s) = attr_state().lock() {
        if owner < s.live.len() {
            s.by_ptr.insert(ptr, owner as u32);
            s.live[owner] += bytes as i64;
            s.peak[owner] = s.peak[owner].max(s.live[owner]);
            s.allocs[owner] += 1;
        }
    }
}

#[inline]
fn note_attr_free(ptr: usize, bytes: u64) {
    if !mem_attr_enabled() {
        return;
    }
    if let Ok(mut s) = attr_state().lock() {
        if let Some(owner) = s.by_ptr.remove(&ptr) {
            let owner = owner as usize;
            if owner < s.live.len() {
                s.live[owner] -= bytes as i64;
            }
        }
    }
}

/// Top-`n` owners by live bytes as "name\tlive\tpeak\tallocs" rows.
pub fn owner_report(n: usize) -> String {
    let Ok(s) = attr_state().lock() else {
        return String::new();
    };
    let mut idx: Vec<usize> = (0..s.names.len()).collect();
    idx.sort_by_key(|&i| -s.live[i]);
    idx.iter()
        .take(n)
        .map(|&i| format!("{}\t{}\t{}\t{}", s.names[i], s.live[i], s.peak[i], s.allocs[i]))
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
        let s = attr_state().lock().unwrap();
        let id = s.ids["attr_test_mod_a"] as usize;
        assert_eq!(s.live[id], 0, "live returns to zero after free");
        assert_eq!(s.peak[id], 10_000_000, "peak survives the free");
    }
}

#[cfg(test)]
mod validated_cache_tests {
    use super::*;

    #[test]
    fn erased_pointer_is_not_answered_from_the_validated_cache() {
        let layout = std::alloc::Layout::from_size_align(64, 8).unwrap();
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) } as *mut HeapHeader;
        unsafe {
            (*ptr).object_type = HeapObjectType::String;
            (*ptr).size = 64;
        }
        register_heap_ptr(ptr);
        assert!(is_registered_heap_ptr(ptr));
        assert!(is_registered_heap_ptr(ptr), "cached hit");
        let value = unsafe { RuntimeValue::from_heap_ptr(ptr) };
        assert_eq!(registered_heap_type(value), Some(HeapObjectType::String));
        assert!(unregister_heap_ptr_checked(ptr));
        assert!(!is_registered_heap_ptr(ptr), "erase must invalidate the cache");
        assert_eq!(registered_heap_type(value), None);
        register_heap_ptr(ptr);
        assert!(is_registered_heap_ptr(ptr), "re-registered address validates again");
        assert!(unregister_heap_ptr_checked(ptr));
        unsafe { std::alloc::dealloc(ptr as *mut u8, layout) };
    }
}

#[cfg(test)]
mod fork_registry_tests {
    use super::HeapRegistry;

    #[test]
    fn frozen_registry_keeps_membership_and_is_never_written() {
        let mut registry = HeapRegistry::default();
        for addr in (1..=1000usize).map(|i| i * 16) {
            assert!(registry.insert(addr));
        }
        registry.freeze_for_fork_child();
        let frozen_len = registry.frozen.as_ref().unwrap().len();
        let frozen_cap = registry.frozen.as_ref().unwrap().capacity();
        assert_eq!(registry.len(), 1000);
        assert!(registry.contains(&16) && registry.contains(&16000));

        // Child-owned objects live in the overlay.
        for addr in (1..=5000usize).map(|i| 1_000_000 + i * 16) {
            assert!(registry.insert(addr));
            assert!(!registry.insert(addr), "duplicate insert");
        }
        assert!(!registry.insert(32), "inherited address is already present");
        for addr in (1..=5000usize).map(|i| 1_000_000 + i * 16) {
            assert!(registry.remove(&addr));
            assert!(!registry.remove(&addr), "double erase refused");
            assert!(!registry.contains(&addr));
        }

        // Erasing an inherited object succeeds exactly once.
        assert!(registry.remove(&48));
        assert!(!registry.remove(&48));
        assert!(!registry.contains(&48));
        assert_eq!(registry.len(), 999);
        assert_eq!(registry.iter().count(), 999);
        assert!(!registry.iter().any(|addr| *addr == 48));
        // Re-registering the recycled address restores it once.
        assert!(registry.insert(48));
        assert!(!registry.insert(48));
        assert!(registry.contains(&48));
        assert!(!registry.remove(&999_999), "never registered");

        let frozen = registry.frozen.as_ref().unwrap();
        assert_eq!(frozen.len(), frozen_len, "inherited table untouched");
        assert_eq!(frozen.capacity(), frozen_cap, "inherited table never regrown");

        // A nested fork keeps the first frozen layer.
        registry.freeze_for_fork_child();
        assert_eq!(registry.len(), 1000);
        registry.clear();
        assert_eq!(registry.len(), 0);
        assert!(!registry.contains(&16));
    }

    /// The scope-end batch over a fork child's frozen registry: inherited and
    /// child-owned objects are erased exactly once, a declined inherited
    /// object stays a member, and the inherited table is never written.
    #[test]
    fn batch_erase_over_frozen_registry_never_writes_inherited_table() {
        use super::{erase_selected, HeapHeader, HeapObjectType};
        use crate::value::core::RuntimeValue;
        // 8-aligned storage, as every real heap object has.
        let headers: Vec<*mut HeapHeader> = (0..4)
            .map(|_| {
                let slot = Box::into_raw(Box::new([0u64; 2])) as *mut HeapHeader;
                unsafe { slot.write(HeapHeader::new(HeapObjectType::Tuple, 16)) };
                slot
            })
            .collect();
        let addr = |i: usize| headers[i] as usize;
        let value = |i: usize| RuntimeValue(addr(i) as u64 | crate::value::tags::TAG_HEAP);
        let mut registry = HeapRegistry::default();
        for i in 0..3 {
            assert!(registry.insert(addr(i)));
        }
        registry.freeze_for_fork_child();
        let frozen_cap = registry.frozen.as_ref().unwrap().capacity();
        assert!(registry.insert(addr(3)), "child-owned object");

        // 0 inherited + erased (listed twice: second is a stale duplicate),
        // 1 inherited + declined, 2 inherited + not listed, 3 child + erased.
        let candidates = [value(0), value(1), value(3), value(0)];
        let mut out = Vec::new();
        erase_selected(&mut registry, &candidates, &mut |_, ptr| ptr as usize != addr(1), &mut out);
        let erased: Vec<usize> = out.iter().map(|(ptr, _)| *ptr as usize).collect();
        assert_eq!(erased, vec![addr(0), addr(3)]);
        assert!(out.iter().all(|(_, kind)| *kind == HeapObjectType::Tuple));
        assert!(!registry.contains(&addr(0)) && !registry.contains(&addr(3)));
        assert!(registry.contains(&addr(1)) && registry.contains(&addr(2)));
        assert_eq!(registry.len(), 2);
        let frozen = registry.frozen.as_ref().unwrap();
        assert_eq!((frozen.len(), frozen.capacity()), (3, frozen_cap), "inherited table untouched");
        for header in headers {
            drop(unsafe { Box::from_raw(header as *mut [u64; 2]) });
        }
    }
}
