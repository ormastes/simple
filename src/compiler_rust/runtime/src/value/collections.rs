//! Collection types: Array, Tuple, String and their SFFI functions.
//! Dict SFFI functions are in the dict module.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::sync::{Mutex, OnceLock};

use super::byte_kernels::{
    avx2_byte_find, avx2_byte_rfind, byte_split_ranges_for_tier, neon_byte_find, neon_byte_rfind, scalar_byte_find,
    scalar_byte_rfind, scalar_byte_split_ranges,
};
use super::core::RuntimeValue;
use super::dict::RuntimeDict;
use super::heap::{
    gc_flags, get_typed_ptr, get_typed_ptr_mut, note_aux_alloc, note_aux_free, register_heap_ptr, unregister_heap_ptr,
    unregister_heap_ptr_checked,
    HeapHeader, HeapObjectType,
};
use super::objects::{
    rt_closure_func_ptr, rt_option_map, rt_option_none, rt_option_some, RuntimeClosure, RuntimeEnum, RuntimeObject,
};
use super::primitive_sort;
use simple_simd::{clear_host_cpu_config_cache, detect_profile, host_cpu_config, SimdTier};
use simple_simd::HostCpuConfigError;

thread_local! {
    static TRANSIENT_HEAP_SCOPE: RefCell<Option<TransientHeapScope>> = const { RefCell::new(None) };
}

struct TransientHeapScope {
    paused: bool,
    objects: Vec<RuntimeValue>,
}

pub(crate) fn track_transient_heap(value: RuntimeValue) -> RuntimeValue {
    TRANSIENT_HEAP_SCOPE.with(|slot| {
        if let Some(scope) = slot.borrow_mut().as_mut() {
            if !scope.paused {
                scope.objects.push(value);
            }
        }
    });
    value
}

// ============================================================================
// Helper macros to reduce SFFI boilerplate
// ============================================================================

/// Get typed pointer from heap object with validation, returning early if invalid
macro_rules! as_typed_ptr {
    ($val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match get_typed_ptr::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
    (mut $val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match get_typed_ptr_mut::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
}

/// Normalize a Python-style index (handles negative indices)
#[inline]
fn normalize_index(index: i64, len: i64) -> i64 {
    if index < 0 {
        len + index
    } else {
        index
    }
}

/// FNV-1a hash for strings (64-bit)
/// This is a simple, fast hash suitable for hash tables.
#[inline]
fn fnv1a_hash(bytes: &[u8]) -> u64 {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;

    let mut hash = FNV_OFFSET;
    for &byte in bytes {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

// ============================================================================
// Hybrid dispatch providers for hot primitive/byte kernels
// ============================================================================

type ArraySortKernel = fn(&mut [RuntimeValue]);
type ByteFindKernel = fn(&[u8], &[u8], usize) -> Option<usize>;
type ByteRfindKernel = fn(&[u8], &[u8]) -> Option<usize>;
type ByteSplitKernel = fn(&str, &str) -> Vec<(usize, usize)>;

#[derive(Clone, Copy)]
struct CollectionProviders {
    array_sort: ArraySortKernel,
    byte_find: ByteFindKernel,
    byte_rfind: ByteRfindKernel,
    byte_split: ByteSplitKernel,
    simd_tier: SimdTier,
}

#[derive(Clone, Copy)]
struct CollectionProviderCache {
    host_simd_tier: Option<SimdTier>,
    providers: Option<CollectionProviders>,
    provider_simd_tier: Option<SimdTier>,
    resolutions: usize,
}

fn collection_provider_cache() -> &'static Mutex<CollectionProviderCache> {
    static CACHE: OnceLock<Mutex<CollectionProviderCache>> = OnceLock::new();
    CACHE.get_or_init(|| {
        Mutex::new(CollectionProviderCache {
            host_simd_tier: None,
            providers: None,
            provider_simd_tier: None,
            resolutions: 0,
        })
    })
}

fn providers_for_tier(tier: SimdTier) -> CollectionProviders {
    match tier {
        SimdTier::X86_64Sse2 => CollectionProviders {
            array_sort: scalar_array_sort,
            byte_find: scalar_byte_find,
            byte_rfind: scalar_byte_rfind,
            byte_split: scalar_byte_split_ranges,
            simd_tier: SimdTier::X86_64Sse2,
        },
        SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => CollectionProviders {
            array_sort: scalar_array_sort,
            byte_find: avx2_byte_find,
            byte_rfind: avx2_byte_rfind,
            byte_split: avx2_byte_split_ranges,
            simd_tier: SimdTier::X86_64Avx2,
        },
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => CollectionProviders {
            array_sort: scalar_array_sort,
            byte_find: neon_byte_find,
            byte_rfind: neon_byte_rfind,
            byte_split: neon_byte_split_ranges,
            simd_tier: SimdTier::Aarch64Neon,
        },
        tier => CollectionProviders {
            array_sort: scalar_array_sort,
            byte_find: scalar_byte_find,
            byte_rfind: scalar_byte_rfind,
            byte_split: scalar_byte_split_ranges,
            simd_tier: tier,
        },
    }
}

fn configured_simd_tier_override() -> Option<SimdTier> {
    std::env::var("SIMPLE_SIMD_TIER").ok()?.parse().ok()
}

fn resolve_host_simd_tier() -> (SimdTier, bool) {
    host_cpu_config()
        .map(|config| (config.enabled.simd_tier, true))
        .unwrap_or_else(|error| {
            let cacheable = !matches!(error, HostCpuConfigError::Unstable(_));
            (detect_profile().best_available_implementation(), cacheable)
        })
}

fn collection_providers() -> CollectionProviders {
    let override_tier = configured_simd_tier_override();
    let mut cache = collection_provider_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());

    let (simd_tier, cacheable) = if let Some(override_tier) = override_tier {
        (override_tier, true)
    } else if let Some(host_simd_tier) = cache.host_simd_tier {
        (host_simd_tier, true)
    } else {
        let (host_simd_tier, cacheable) = resolve_host_simd_tier();
        if cacheable {
            cache.host_simd_tier = Some(host_simd_tier);
        }
        (host_simd_tier, cacheable)
    };

    if cacheable && cache.provider_simd_tier == Some(simd_tier) {
        if let Some(providers) = cache.providers {
            return providers;
        }
    }

    let providers = providers_for_tier(simd_tier);
    cache.resolutions += 1;
    if cacheable {
        cache.provider_simd_tier = Some(simd_tier);
        cache.providers = Some(providers);
    }
    providers
}

pub(crate) fn active_collection_simd_tier() -> SimdTier {
    collection_providers().simd_tier
}

pub(crate) fn clear_collection_provider_cache() {
    let mut cache = collection_provider_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    cache.host_simd_tier = None;
    cache.providers = None;
    cache.provider_simd_tier = None;
    cache.resolutions = 0;
    clear_host_cpu_config_cache();
}

#[cfg(test)]
pub(crate) fn collection_provider_resolution_count_for_tests() -> usize {
    collection_provider_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .resolutions
}

#[inline]
fn compare_runtime_values(a: &RuntimeValue, b: &RuntimeValue) -> Ordering {
    match (a.as_heap_u64(), b.as_heap_u64()) {
        (Some(left), Some(right)) => return left.cmp(&right),
        (Some(_), None) if b.is_int() && b.as_int() < 0 => return Ordering::Greater,
        (Some(left), None) if b.is_int() => return left.cmp(&(b.as_int() as u64)),
        (None, Some(_)) if a.is_int() && a.as_int() < 0 => return Ordering::Less,
        (None, Some(right)) if a.is_int() => return (a.as_int() as u64).cmp(&right),
        _ => {}
    }
    match (a.is_int(), b.is_int(), a.is_float(), b.is_float()) {
        (true, true, _, _) => a.as_int().cmp(&b.as_int()),
        (_, _, true, true) => a.as_float().partial_cmp(&b.as_float()).unwrap_or(Ordering::Equal),
        (true, false, _, true) => Ordering::Less,
        (false, true, true, _) => Ordering::Greater,
        _ => Ordering::Equal,
    }
}

fn scalar_array_sort(values: &mut [RuntimeValue]) {
    values.sort_by(compare_runtime_values);
}

fn avx2_byte_split_ranges(haystack: &str, delimiter: &str) -> Vec<(usize, usize)> {
    byte_split_ranges_for_tier(SimdTier::X86_64Avx2, haystack, delimiter)
}

fn neon_byte_split_ranges(haystack: &str, delimiter: &str) -> Vec<(usize, usize)> {
    byte_split_ranges_for_tier(SimdTier::Aarch64Neon, haystack, delimiter)
}

// ============================================================================
// Heap-allocated collection structures
// ============================================================================

/// A heap-allocated string
#[repr(C)]
pub struct RuntimeString {
    pub header: HeapHeader,
    /// Length in bytes
    pub len: u64,
    /// Cached hash value
    pub hash: u64,
    // Followed by UTF-8 bytes (flexible array member)
}

impl RuntimeString {
    /// Get the string data as a byte slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeString was properly allocated
    /// with the correct length.
    pub unsafe fn as_bytes(&self) -> &[u8] {
        let data_ptr = (self as *const Self).add(1) as *const u8;
        std::slice::from_raw_parts(data_ptr, self.len as usize)
    }

    /// Get the string data as a str
    ///
    /// # Safety
    /// The caller must ensure the RuntimeString contains valid UTF-8.
    pub unsafe fn as_str(&self) -> &str {
        std::str::from_utf8_unchecked(self.as_bytes())
    }
}

/// Allocate a RuntimeString with given length (no data copied).
/// Returns None if allocation fails.
/// # Safety
/// The caller must initialize the string data and hash.
pub(crate) unsafe fn alloc_runtime_string(len: u64) -> Option<*mut RuntimeString> {
    let size = std::mem::size_of::<RuntimeString>() + len as usize;
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
    let ptr = std::alloc::alloc(layout) as *mut RuntimeString;
    if ptr.is_null() {
        return None;
    }
    (*ptr).header = HeapHeader::new(HeapObjectType::String, size as u32);
    (*ptr).len = len;
    Some(ptr)
}

/// Marks a heap string owned by a process-wide cache (`SHORT_STRING_CACHE` or
/// `STRING_LITERAL_INTERN`). Those objects are handed out repeatedly to
/// unrelated callers, so freeing one corrupts every other holder;
/// `rt_string_free` refuses them.
///
/// Parity note: this is the Rust twin of `RT_CORE_STRING_FLAG_SHARED` in
/// src/runtime/runtime_native.c, and like it the bit lives in the existing
/// `reserved` padding field (`HeapHeader::reserved`), so no layout changes.
pub(crate) const RT_STRING_FLAG_SHARED: u16 = 1;

/// Set once a string has been proven to contain no byte >= 0x80. Positive-only:
/// set means proven ASCII, unset means unknown (never "proven non-ASCII"), so a
/// stale-miss can only cost a rescan. Sound because Simple strings are immutable.
pub(crate) const RT_STRING_FLAG_ASCII: u16 = 1 << 1;

/// Set `RT_STRING_FLAG_SHARED` on a cache-owned string. No-op for NIL (an
/// allocation failure) or a non-heap value.
fn mark_string_shared(value: RuntimeValue) {
    if !value.is_heap() {
        return;
    }
    let ptr = value.as_heap_ptr();
    if ptr.is_null() {
        return;
    }
    unsafe {
        (*ptr).reserved |= RT_STRING_FLAG_SHARED;
    }
}

static SHORT_STRING_CACHE: OnceLock<[RuntimeValue; 257]> = OnceLock::new();

fn rt_string_new_uncached_untracked(bytes: *const u8, len: u64) -> RuntimeValue {
    unsafe {
        let Some(ptr) = alloc_runtime_string(len) else {
            return RuntimeValue::NIL;
        };

        if len > 0 {
            let data_ptr = ptr.add(1) as *mut u8;
            std::ptr::copy_nonoverlapping(bytes, data_ptr, len as usize);
            (*ptr).hash = fnv1a_hash(std::slice::from_raw_parts(bytes, len as usize));
        } else {
            (*ptr).hash = 0;
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn rt_string_new_uncached(bytes: *const u8, len: u64) -> RuntimeValue {
    track_transient_heap(rt_string_new_uncached_untracked(bytes, len))
}

fn short_string_cache() -> &'static [RuntimeValue; 257] {
    SHORT_STRING_CACHE.get_or_init(|| {
        std::array::from_fn(|index| {
            let value = if index == 0 {
                rt_string_new_uncached_untracked(std::ptr::null(), 0)
            } else {
                let byte = [(index - 1) as u8];
                rt_string_new_uncached_untracked(byte.as_ptr(), 1)
            };
            // Process-wide, handed to every len<=1 caller: never freeable.
            mark_string_shared(value);
            value
        })
    })
}

pub(crate) fn reregister_short_string_cache() {
    if let Some(cache) = SHORT_STRING_CACHE.get() {
        for value in cache {
            register_heap_ptr(value.as_heap_ptr());
        }
    }
}

/// A heap-allocated array.
///
/// The element storage lives in a SEPARATE heap allocation referenced by
/// `data`. This matters for `rt_array_push_grow`: when the backing buffer
/// needs to grow, only the element buffer is reallocated (and may move),
/// while the `RuntimeArray` header stays at a stable address. Caller-side
/// SSA values that hold the array pointer therefore remain valid across
/// growths. See the 2026-04-13 codegen bug fix in native_mcp_servers.md:
/// previously the data was laid out inline after the header and `realloc`
/// could move the whole allocation, leaving every caller holding a dangling
/// pointer — that silently corrupted every growable array in native builds.
#[repr(C)]
pub struct RuntimeArray {
    pub header: HeapHeader,
    /// Number of elements
    pub len: u64,
    /// Capacity (allocated slots in `data`)
    pub capacity: u64,
    /// Pointer to the element buffer (separate allocation).
    pub data: *mut RuntimeValue,
}

impl RuntimeArray {
    #[inline]
    pub fn is_byte_packed(&self) -> bool {
        self.header.gc_flags & gc_flags::BYTE_PACKED != 0
    }

    #[inline]
    pub fn is_u64_packed(&self) -> bool {
        self.header.gc_flags & gc_flags::U64_PACKED != 0
    }

    /// Get the elements as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeArray was properly allocated.
    pub unsafe fn as_slice(&self) -> &[RuntimeValue] {
        if self.data.is_null() {
            return &[];
        }
        std::slice::from_raw_parts(self.data, self.len as usize)
    }

    /// Get the elements as a mutable slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeArray was properly allocated.
    pub unsafe fn as_mut_slice(&mut self) -> &mut [RuntimeValue] {
        if self.data.is_null() {
            return &mut [];
        }
        std::slice::from_raw_parts_mut(self.data, self.len as usize)
    }

    /// Pointer to the element buffer (returns null if not allocated).
    #[inline]
    pub fn data_ptr(&self) -> *mut RuntimeValue {
        self.data
    }
}

/// Copy bytes from either native representation of Simple `[u8]`.
pub(crate) fn byte_array_bytes(value: RuntimeValue) -> Option<Vec<u8>> {
    let array = get_typed_ptr::<RuntimeArray>(value, HeapObjectType::Array)?;
    let array = unsafe { &*array };
    if array.len > array.capacity || array.data.is_null() {
        return None;
    }
    let len = usize::try_from(array.len).ok()?;
    if array.is_byte_packed() {
        return Some(unsafe { std::slice::from_raw_parts(array.data.cast::<u8>(), len) }.to_vec());
    }
    unsafe { array.as_slice() }
        .iter()
        .map(|value| value.is_int().then(|| (value.as_int() & 0xff) as u8))
        .collect()
}

/// Write bytes into either native representation of Simple `[u8]`.
pub(crate) fn byte_array_write(value: RuntimeValue, bytes: &[u8]) -> bool {
    let Some(array) = get_typed_ptr_mut::<RuntimeArray>(value, HeapObjectType::Array) else {
        return false;
    };
    let array = unsafe { &mut *array };
    if array.len > array.capacity || array.data.is_null() || bytes.len() > array.len as usize {
        return false;
    }
    if array.is_byte_packed() {
        unsafe { std::slice::from_raw_parts_mut(array.data.cast::<u8>(), bytes.len()) }.copy_from_slice(bytes);
    } else {
        for (slot, byte) in unsafe { array.as_mut_slice() }.iter_mut().zip(bytes) {
            *slot = RuntimeValue::from_int(*byte as i64);
        }
    }
    true
}

/// Layout used for the element storage of a `RuntimeArray` with the given
/// capacity. Capacity 0 is treated as 1 to satisfy the allocator's min-size
/// requirement.
fn array_data_layout(capacity: u64) -> std::alloc::Layout {
    let cap = capacity.max(1) as usize;
    std::alloc::Layout::from_size_align(
        cap * std::mem::size_of::<RuntimeValue>(),
        std::mem::align_of::<RuntimeValue>(),
    )
    .expect("valid array data layout")
}

fn byte_array_data_layout(capacity: u64) -> std::alloc::Layout {
    let cap = capacity.max(1) as usize;
    std::alloc::Layout::from_size_align(cap, 1).expect("valid byte array data layout")
}

/// Aux-byte accounting for an array element-buffer replacement (grow path).
/// `old_data` is the PRE-swap buffer pointer: null means no old buffer bytes
/// were ever accounted, so only the new size is added. Relaxed atomics only.
#[inline]
fn note_array_data_swap(old_data: *mut RuntimeValue, old_bytes: usize, new_bytes: usize) {
    if !old_data.is_null() {
        note_aux_free(HeapObjectType::Array as u8, old_bytes as u64);
    }
    note_aux_alloc(HeapObjectType::Array as u8, new_bytes as u64);
}

/// A heap-allocated tuple (fixed-size array)
#[repr(C)]
pub struct RuntimeTuple {
    pub header: HeapHeader,
    /// Number of elements
    pub len: u64,
    // Followed by RuntimeValue elements
}

impl RuntimeTuple {
    /// Get the elements as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeTuple was properly allocated.
    pub unsafe fn as_slice(&self) -> &[RuntimeValue] {
        let data_ptr = (self as *const Self).add(1) as *const RuntimeValue;
        std::slice::from_raw_parts(data_ptr, self.len as usize)
    }
}

// RuntimeDict is in dict.rs module

// ============================================================================
// Array SFFI functions
// ============================================================================

/// Allocate a new array with the given capacity.
/// Minimum capacity is 4 to allow a few pushes before the first grow.
/// The element buffer is allocated separately from the header, so later
/// growths do not move the header — callers' pointers stay valid.
#[no_mangle]
pub extern "C" fn rt_array_new(capacity: u64) -> RuntimeValue {
    let capacity = capacity.max(4);
    let header_size = std::mem::size_of::<RuntimeArray>();
    let header_layout = std::alloc::Layout::from_size_align(header_size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(header_layout) as *mut RuntimeArray;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        let data_layout = array_data_layout(capacity);
        let data = std::alloc::alloc_zeroed(data_layout) as *mut RuntimeValue;
        if data.is_null() {
            std::alloc::dealloc(ptr as *mut u8, header_layout);
            return RuntimeValue::NIL;
        }
        note_aux_alloc(HeapObjectType::Array as u8, data_layout.size() as u64);

        (*ptr).header = HeapHeader::new(HeapObjectType::Array, header_size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;
        (*ptr).data = data;

        track_transient_heap(RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader))
    }
}

/// Allocate an array with uninitialized element capacity and length 0.
///
/// This matches `Vec::with_capacity`/`malloc` benchmark semantics: callers must
/// write elements before publishing length or reading slots.
fn rt_array_new_uninit(capacity: u64) -> RuntimeValue {
    let capacity = capacity.max(4);
    let header_size = std::mem::size_of::<RuntimeArray>();
    let header_layout = std::alloc::Layout::from_size_align(header_size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc(header_layout) as *mut RuntimeArray;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        let data_layout = array_data_layout(capacity);
        let data = std::alloc::alloc(data_layout) as *mut RuntimeValue;
        if data.is_null() {
            std::alloc::dealloc(ptr as *mut u8, header_layout);
            return RuntimeValue::NIL;
        }
        note_aux_alloc(HeapObjectType::Array as u8, data_layout.size() as u64);

        (*ptr).header = HeapHeader::new(HeapObjectType::Array, header_size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;
        (*ptr).data = data;

        track_transient_heap(RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader))
    }
}

fn rt_array_new_uninit_u64(capacity: u64) -> RuntimeValue {
    let array = rt_array_new_uninit(capacity);
    if array.is_nil() {
        return array;
    }
    let ptr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        (*ptr).header.gc_flags |= gc_flags::U64_PACKED;
    }
    array
}

#[no_mangle]
pub extern "C" fn rt_byte_array_new(capacity: u64) -> RuntimeValue {
    let capacity = capacity.max(4);
    let header_size = std::mem::size_of::<RuntimeArray>();
    let header_layout = std::alloc::Layout::from_size_align(header_size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(header_layout) as *mut RuntimeArray;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        let data_layout = byte_array_data_layout(capacity);
        let data = std::alloc::alloc_zeroed(data_layout) as *mut RuntimeValue;
        if data.is_null() {
            std::alloc::dealloc(ptr as *mut u8, header_layout);
            return RuntimeValue::NIL;
        }
        note_aux_alloc(HeapObjectType::Array as u8, data_layout.size() as u64);

        (*ptr).header = HeapHeader::new(HeapObjectType::Array, header_size as u32);
        (*ptr).header.gc_flags |= gc_flags::BYTE_PACKED;
        (*ptr).len = 0;
        (*ptr).capacity = capacity;
        (*ptr).data = data;

        track_transient_heap(RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader))
    }
}

#[no_mangle]
pub extern "C" fn rt_byte_array_new_len(len: u64) -> RuntimeValue {
    let array = rt_byte_array_new(len);
    if array.is_nil() {
        return array;
    }
    let ptr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        (*ptr).len = len;
    }
    array
}

/// Get the length of an array
#[no_mangle]
pub extern "C" fn rt_array_len(array: RuntimeValue) -> i64 {
    if array.to_raw() & !7 == 0 {
        return 0;
    }
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, -1);
    unsafe { (*arr).len as i64 }
}

#[no_mangle]
pub extern "C" fn rt_array_len_safe(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe { (*arr).len as i64 }
}

/// Get an element from an array
#[no_mangle]
pub extern "C" fn rt_array_get(array: RuntimeValue, index: i64) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return RuntimeValue::NIL;
        }
        if (*arr).is_byte_packed() {
            return RuntimeValue::from_int(*((*arr).data as *const u8).add(idx as usize) as i64);
        }
        if (*arr).is_u64_packed() {
            return RuntimeValue::from_int(*((*arr).data as *const u64).add(idx as usize) as i64);
        }
        (*arr).as_slice()[idx as usize]
    }
}

#[no_mangle]
pub extern "C" fn rt_array_get_i64_raw(array: RuntimeValue, index: i64) -> i64 {
    rt_array_get(array, index).to_raw() as i64
}

/// Get a text element from a word-backed array.
#[no_mangle]
pub extern "C" fn rt_array_get_text(array: RuntimeValue, index: i64) -> RuntimeValue {
    rt_array_get(array, index)
}

/// Array `at`: bounds-checked element access with an optional (`T?`) result.
///
/// This is deliberately NOT `rt_array_get`: that one *normalizes* the index
/// (Python-style negatives), so `at(-1)` would silently wrap to the last
/// element instead of reporting absence. Bounds here are checked SIGNED and
/// unnormalized, matching the tree-walking interpreter's array `at` arm added
/// in f18c5963132 (`interpreter_method/collections.rs`), which is the reference
/// semantics: present iff `0 <= index < len`.
///
/// ENCODING -- the part that is easy to get wrong, and the reason this returns
/// a BOXED `Option` (`rt_option_some`/`rt_option_none`) rather than the "raw
/// migration form" (bare payload for present, `NIL` for absent).
///
/// The raw form cannot express this operation safely. `stmt_lowering.rs`
/// discriminates the two forms at runtime with `rt_enum_id(subj) >= 0`, and
/// deliberately passes a raw payload through UNTOUCHED -- so a raw payload must
/// be an untagged `i64`. But the nil sentinel IS the untagged word 3
/// (`SPECIAL_NIL` | `TAG_SPECIAL`), so a raw optional holding the value 3 would
/// be indistinguishable from absence BY CONSTRUCTION. `xs.at(3)` on
/// `[0, 1, 2, 3, 4]` is exactly that case.
///
/// The boxed form has no such collision: `Some(3)` is a heap `Option` object
/// whose payload is the tag-boxed `3 << 3` = 24, and absence is a distinct
/// `Option::None` object. The boxed path also gets the correct post-processing
/// for free -- `rt_enum_payload` followed by the tag-aware `UnboxInt`.
///
/// This does require `case nil:` to recognise a boxed `Option::None`; that is
/// what the `Pattern::Literal(Expr::Nil)` -> `rt_is_none` lowering in
/// `stmt_lowering.rs` provides. `case None:` already used `rt_is_none`.
#[no_mangle]
pub extern "C" fn rt_array_at(array: RuntimeValue, index: i64) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, rt_option_none());
    unsafe {
        let len = (*arr).len as i64;
        if index < 0 || index >= len {
            return rt_option_none();
        }
        let elem = if (*arr).is_byte_packed() {
            RuntimeValue::from_int(*((*arr).data as *const u8).add(index as usize) as i64)
        } else if (*arr).is_u64_packed() {
            RuntimeValue::from_int(*((*arr).data as *const u64).add(index as usize) as i64)
        } else {
            (*arr).as_slice()[index as usize]
        };
        rt_option_some(elem)
    }
}

/// Receiver-dispatching `at`.
///
/// The compiled lanes used to map the method name `at` straight to
/// `rt_string_char_at` by name, with no receiver-type test, so `arr.at(i)` took
/// the *text* path and silently produced `nil` for EVERY index -- in-range hits
/// included, with no error and no crash. See
/// doc/08_tracking/bug/array_at_returns_nil_for_every_index_2026-08-01.md.
///
/// The test is done here, at runtime, rather than at the five codegen sites
/// because those sites dispatch purely on the method name and do not all have a
/// reliable static receiver type available.
///
/// Text behaviour is intentionally left exactly as it was: `text.at(i)` still
/// yields a raw single-character string (or `nil`), NOT an `Option`. Only the
/// array receiver -- which previously had no implementation at all on these
/// lanes -- gains the `Option` result.
#[no_mangle]
pub extern "C" fn rt_at(receiver: RuntimeValue, index: i64) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        return rt_array_at(receiver, index);
    }
    rt_string_char_at(receiver, index)
}

/// Set an element in an array
#[no_mangle]
pub extern "C" fn rt_array_set(array: RuntimeValue, index: i64, value: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return false;
        }
        if (*arr).is_byte_packed() {
            *((*arr).data as *mut u8).add(idx as usize) = (value.as_int() & 0xff) as u8;
            return true;
        }
        if (*arr).is_u64_packed() {
            *((*arr).data as *mut u64).add(idx as usize) = value.as_int() as u64;
            return true;
        }
        (*arr).as_mut_slice()[idx as usize] = value;
        true
    }
}

/// Set a text element in a word-backed array.
#[no_mangle]
pub extern "C" fn rt_array_set_text(array: RuntimeValue, index: i64, value: RuntimeValue) -> bool {
    rt_array_set(array, index, value)
}

/// Read a single byte from a `[u8]`-style runtime array.
#[no_mangle]
pub extern "C" fn rt_bytes_u8_at(array: RuntimeValue, index: i64) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return 0;
        }
        if (*arr).is_byte_packed() {
            return *((*arr).data as *const u8).add(idx as usize) as i64;
        }
        let value = (*arr).as_slice()[idx as usize];
        if value.is_int() {
            return value.as_int() & 0xFF;
        }
        (value.to_raw() as i64) & 0xFF
    }
}

/// Read a u32 element from a `[u32]`-style runtime array without generic index dispatch.
#[no_mangle]
pub extern "C" fn rt_typed_words_u32_at(array: RuntimeValue, index: i64) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return 0;
        }
        let raw = (*arr).as_slice()[idx as usize];
        if raw.is_int() {
            return raw.as_int() & 0xFFFF_FFFF;
        }
        (raw.to_raw() as i64) & 0xFFFF_FFFF
    }
}

/// Read a u32 element when the caller has already proved `0 <= index < len`.
#[no_mangle]
pub extern "C" fn rt_typed_words_u32_unchecked(array: RuntimeValue, index: i64) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe {
        let raw = (*arr).as_slice()[index as usize];
        if raw.is_int() {
            return raw.as_int() & 0xFFFF_FFFF;
        }
        (raw.to_raw() as i64) & 0xFFFF_FFFF
    }
}

#[no_mangle]
pub extern "C" fn rt_array_data_ptr(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe { (*arr).data as i64 }
}

#[no_mangle]
pub extern "C" fn rt_array_data_ptr_text(array: RuntimeValue) -> i64 {
    rt_array_data_ptr(array)
}

/// Return the stable array header pointer for proven native fast paths.
#[no_mangle]
pub extern "C" fn rt_array_header_ptr(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    arr as i64
}

/// Set array length through a caller-proven stable header pointer.
#[no_mangle]
pub extern "C" fn rt_array_set_len_known(header_ptr: i64, len: i64) -> bool {
    if header_ptr == 0 || len < 0 {
        return false;
    }
    unsafe {
        let arr = header_ptr as *mut RuntimeArray;
        if len as u64 > (*arr).capacity {
            return false;
        }
        (*arr).len = len as u64;
        true
    }
}

#[no_mangle]
pub extern "C" fn rt_array_set_len_known_text(header_ptr: i64, len: i64) -> bool {
    rt_array_set_len_known(header_ptr, len)
}

#[no_mangle]
pub extern "C" fn rt_typed_bytes_u8_data_at(data_ptr: i64, index: i64) -> i64 {
    unsafe { *((data_ptr as *const u8).add(index as usize)) as i64 }
}

#[no_mangle]
pub extern "C" fn rt_typed_words_u32_data_at(data_ptr: i64, index: i64) -> i64 {
    unsafe {
        let raw = *((data_ptr as *const RuntimeValue).add(index as usize));
        if raw.is_int() {
            return raw.as_int() & 0xFFFF_FFFF;
        }
        (raw.to_raw() as i64) & 0xFFFF_FFFF
    }
}

/// Read a u64 element from a `[u64]`-style runtime array without generic index dispatch.
#[no_mangle]
pub extern "C" fn rt_typed_words_u64_at(array: RuntimeValue, index: i64) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return 0;
        }
        if (*arr).is_u64_packed() {
            return *((*arr).data as *const u64).add(idx as usize) as i64;
        }
        let raw = (*arr).as_slice()[idx as usize];
        if raw.is_int() {
            return raw.as_int();
        }
        raw.to_raw() as i64
    }
}

/// Read a u64 element when the caller has already proved `0 <= index < len`.
#[no_mangle]
pub extern "C" fn rt_typed_words_u64_unchecked(array: RuntimeValue, index: i64) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe {
        if (*arr).is_u64_packed() {
            return *((*arr).data as *const u64).add(index as usize) as i64;
        }
        let raw = (*arr).as_slice()[index as usize];
        if raw.is_int() {
            return raw.as_int();
        }
        raw.to_raw() as i64
    }
}

#[no_mangle]
pub extern "C" fn rt_typed_words_u64_data_at(data_ptr: i64, index: i64) -> i64 {
    unsafe {
        let raw = *((data_ptr as *const RuntimeValue).add(index as usize));
        if raw.is_int() {
            return raw.as_int();
        }
        raw.to_raw() as i64
    }
}

#[no_mangle]
pub extern "C" fn rt_typed_words_u64_data_at_checked(header_ptr: i64, data_ptr: i64, index: i64) -> i64 {
    if header_ptr == 0 || data_ptr == 0 || index < 0 {
        return 0;
    }
    unsafe {
        let arr = (header_ptr & !7) as *const RuntimeArray;
        if (*arr).is_u64_packed() {
            return *((data_ptr as *const u64).add(index as usize)) as i64;
        }
        rt_typed_words_u64_data_at(data_ptr, index)
    }
}

#[no_mangle]
pub extern "C" fn rt_typed_words_u64_raw_data_at(data_ptr: i64, index: i64) -> i64 {
    if data_ptr == 0 || index < 0 {
        return 0;
    }
    unsafe { *((data_ptr as *const u64).add(index as usize)) as i64 }
}

#[no_mangle]
pub extern "C" fn rt_bytes_u32_le_at(array: RuntimeValue, index: i64) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx + 4 > len {
            return 0;
        }
        if (*arr).is_byte_packed() {
            let ptr = ((*arr).data as *const u8).add(idx as usize);
            return u32::from_le_bytes([*ptr, *ptr.add(1), *ptr.add(2), *ptr.add(3)]) as i64;
        }
        let mut value = 0u64;
        for offset in 0..4 {
            let raw = (*arr).as_slice()[(idx + offset) as usize];
            let byte = if raw.is_int() {
                raw.as_int()
            } else {
                raw.to_raw() as i64
            } & 0xff;
            value |= (byte as u64) << (offset * 8);
        }
        value as i64
    }
}

#[no_mangle]
pub extern "C" fn rt_bytes_u64_le_at(array: RuntimeValue, index: i64) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx + 8 > len {
            return 0;
        }
        if (*arr).is_byte_packed() {
            let ptr = ((*arr).data as *const u8).add(idx as usize);
            return u64::from_le_bytes([
                *ptr,
                *ptr.add(1),
                *ptr.add(2),
                *ptr.add(3),
                *ptr.add(4),
                *ptr.add(5),
                *ptr.add(6),
                *ptr.add(7),
            ]) as i64;
        }
        let mut value = 0u64;
        for offset in 0..8 {
            let raw = (*arr).as_slice()[(idx + offset) as usize];
            let byte = if raw.is_int() {
                raw.as_int()
            } else {
                raw.to_raw() as i64
            } & 0xff;
            value |= (byte as u64) << (offset * 8);
        }
        value as i64
    }
}

/// Write a single byte into a `[u8]`-style runtime array without generic index dispatch.
#[no_mangle]
pub extern "C" fn rt_bytes_u8_set(array: RuntimeValue, index: i64, value: i64) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return false;
        }
        if (*arr).is_byte_packed() {
            *((*arr).data as *mut u8).add(idx as usize) = (value & 0xff) as u8;
            return true;
        }
        (*arr).as_mut_slice()[idx as usize] = RuntimeValue::from_int(value & 0xFF);
        true
    }
}

/// Write a u32 element into a `[u32]`-style runtime array without generic index dispatch.
#[no_mangle]
pub extern "C" fn rt_typed_words_u32_set(array: RuntimeValue, index: i64, value: i64) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return false;
        }
        (*arr).as_mut_slice()[idx as usize] = RuntimeValue::from_int(value & 0xFFFF_FFFF);
        true
    }
}

/// Write a u64 element into a `[u64]`-style runtime array without generic index dispatch.
#[no_mangle]
pub extern "C" fn rt_typed_words_u64_set(array: RuntimeValue, index: i64, value: i64) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return false;
        }
        if (*arr).is_u64_packed() {
            *((*arr).data as *mut u64).add(idx as usize) = value as u64;
        } else {
            (*arr).as_mut_slice()[idx as usize] = RuntimeValue::from_int(value);
        }
        true
    }
}

/// Push an element to an array (no grow, returns false if full)
#[no_mangle]
pub extern "C" fn rt_array_push(array: RuntimeValue, value: RuntimeValue) -> bool {
    rt_array_push_grow(array, value)
}

#[no_mangle]
pub extern "C" fn rt_array_push_i64_raw(array: RuntimeValue, value: i64) -> bool {
    rt_array_push_grow(array, RuntimeValue::from_raw(value as u64))
}

/// Push a raw byte into a `[u8]`-style runtime array without RuntimeValue boxing.
#[no_mangle]
pub extern "C" fn rt_typed_bytes_u8_push(array: RuntimeValue, value: i64) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        if (*arr).len >= (*arr).capacity {
            let old_cap = (*arr).capacity;
            let new_cap = (old_cap * 2).max(4);
            let old_layout = if (*arr).is_byte_packed() {
                byte_array_data_layout(old_cap)
            } else {
                array_data_layout(old_cap)
            };
            let new_layout = if (*arr).is_byte_packed() {
                byte_array_data_layout(new_cap)
            } else {
                array_data_layout(new_cap)
            };
            let new_size = new_layout.size();
            let new_data = if (*arr).data.is_null() {
                std::alloc::alloc_zeroed(new_layout) as *mut RuntimeValue
            } else {
                std::alloc::realloc((*arr).data as *mut u8, old_layout, new_size) as *mut RuntimeValue
            };
            if new_data.is_null() {
                return false;
            }
            let old_bytes = if (*arr).is_byte_packed() {
                old_cap as usize
            } else {
                old_cap as usize * std::mem::size_of::<RuntimeValue>()
            };
            if new_size > old_bytes {
                std::ptr::write_bytes((new_data as *mut u8).add(old_bytes), 0, new_size - old_bytes);
            }
            note_array_data_swap((*arr).data, old_layout.size(), new_size);
            (*arr).data = new_data;
            (*arr).capacity = new_cap;
        }

        if (*arr).is_byte_packed() {
            *((*arr).data as *mut u8).add((*arr).len as usize) = (value & 0xff) as u8;
        } else {
            *(*arr).data.add((*arr).len as usize) = RuntimeValue::from_int(value & 0xff);
        }
        (*arr).len += 1;
        true
    }
}

/// Push a raw u32 into a `[u32]`-style runtime array without RuntimeValue boxing.
#[no_mangle]
pub extern "C" fn rt_typed_words_u32_push(array: RuntimeValue, value: i64) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        if (*arr).is_byte_packed() {
            return false;
        }
        if (*arr).len >= (*arr).capacity {
            let old_cap = (*arr).capacity;
            let new_cap = (old_cap * 2).max(4);
            let old_layout = array_data_layout(old_cap);
            let new_size = array_data_layout(new_cap).size();
            let new_data = if (*arr).data.is_null() {
                std::alloc::alloc_zeroed(array_data_layout(new_cap)) as *mut RuntimeValue
            } else {
                std::alloc::realloc((*arr).data as *mut u8, old_layout, new_size) as *mut RuntimeValue
            };
            if new_data.is_null() {
                return false;
            }
            let old_len_bytes = old_cap as usize * std::mem::size_of::<RuntimeValue>();
            if new_size > old_len_bytes {
                std::ptr::write_bytes((new_data as *mut u8).add(old_len_bytes), 0, new_size - old_len_bytes);
            }
            note_array_data_swap((*arr).data, old_layout.size(), new_size);
            (*arr).data = new_data;
            (*arr).capacity = new_cap;
        }

        *(*arr).data.add((*arr).len as usize) = RuntimeValue::from_int(value & 0xFFFF_FFFF);
        (*arr).len += 1;
        true
    }
}

/// Push a raw u64 into a `[u64]`-style runtime array without RuntimeValue boxing.
#[no_mangle]
pub extern "C" fn rt_typed_words_u64_push(array: RuntimeValue, value: i64) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        if (*arr).is_byte_packed() {
            return false;
        }
        if (*arr).len >= (*arr).capacity {
            let old_cap = (*arr).capacity;
            let new_cap = (old_cap * 2).max(4);
            let old_layout = array_data_layout(old_cap);
            let new_size = array_data_layout(new_cap).size();
            let new_data = if (*arr).data.is_null() {
                std::alloc::alloc_zeroed(array_data_layout(new_cap)) as *mut RuntimeValue
            } else {
                std::alloc::realloc((*arr).data as *mut u8, old_layout, new_size) as *mut RuntimeValue
            };
            if new_data.is_null() {
                return false;
            }
            let old_len_bytes = old_cap as usize * std::mem::size_of::<RuntimeValue>();
            if new_size > old_len_bytes {
                std::ptr::write_bytes((new_data as *mut u8).add(old_len_bytes), 0, new_size - old_len_bytes);
            }
            note_array_data_swap((*arr).data, old_layout.size(), new_size);
            (*arr).data = new_data;
            (*arr).capacity = new_cap;
        }

        if (*arr).is_u64_packed() {
            *((*arr).data as *mut u64).add((*arr).len as usize) = value as u64;
        } else {
            *(*arr).data.add((*arr).len as usize) = RuntimeValue::from_int(value);
        }
        (*arr).len += 1;
        true
    }
}

/// Store a typed u32 at a caller-proven append slot and update length.
#[no_mangle]
pub extern "C" fn rt_typed_words_u32_push_known_at(array: RuntimeValue, index: i64, value: i64) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        if (*arr).is_byte_packed() || index < 0 || index as u64 >= (*arr).capacity {
            return false;
        }
        *(*arr).data.add(index as usize) = RuntimeValue::from_int(value & 0xFFFF_FFFF);
        (*arr).len = (index as u64 + 1).max((*arr).len);
        true
    }
}

/// Store a typed u64 at a caller-proven append slot and update length.
#[no_mangle]
pub extern "C" fn rt_typed_words_u64_push_known_at(array: RuntimeValue, index: i64, value: i64) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        if (*arr).is_byte_packed() || index < 0 || index as u64 >= (*arr).capacity {
            return false;
        }
        if (*arr).is_u64_packed() {
            *((*arr).data as *mut u64).add(index as usize) = value as u64;
        } else {
            *(*arr).data.add(index as usize) = RuntimeValue::from_int(value);
        }
        (*arr).len = (index as u64 + 1).max((*arr).len);
        true
    }
}

/// Store a typed u32 through hoisted array pointers and update length.
#[no_mangle]
pub extern "C" fn rt_typed_words_u32_push_known_data_at(
    header_ptr: i64,
    data_ptr: i64,
    index: i64,
    value: i64,
) -> bool {
    if header_ptr == 0 || data_ptr == 0 || index < 0 {
        return false;
    }
    unsafe {
        let arr = header_ptr as *mut RuntimeArray;
        if index as u64 >= (*arr).capacity {
            return false;
        }
        *((data_ptr as *mut RuntimeValue).add(index as usize)) = RuntimeValue::from_int(value & 0xFFFF_FFFF);
        (*arr).len = (index as u64 + 1).max((*arr).len);
        true
    }
}

/// Store a typed u64 through hoisted array pointers and update length.
#[no_mangle]
pub extern "C" fn rt_typed_words_u64_push_known_data_at(
    header_ptr: i64,
    data_ptr: i64,
    index: i64,
    value: i64,
) -> bool {
    if header_ptr == 0 || data_ptr == 0 || index < 0 {
        return false;
    }
    unsafe {
        let arr = header_ptr as *mut RuntimeArray;
        if index as u64 >= (*arr).capacity {
            return false;
        }
        if (*arr).is_u64_packed() {
            *((data_ptr as *mut u64).add(index as usize)) = value as u64;
        } else {
            *((data_ptr as *mut RuntimeValue).add(index as usize)) = RuntimeValue::from_int(value);
        }
        (*arr).len = (index as u64 + 1).max((*arr).len);
        true
    }
}

/// Store a typed u32 through a hoisted data pointer without updating length.
#[no_mangle]
pub extern "C" fn rt_typed_words_u32_store_known_data_at(
    _header_ptr: i64,
    data_ptr: i64,
    index: i64,
    value: i64,
) -> bool {
    if data_ptr == 0 || index < 0 {
        return false;
    }
    unsafe {
        *((data_ptr as *mut RuntimeValue).add(index as usize)) = RuntimeValue::from_int(value & 0xFFFF_FFFF);
        true
    }
}

/// Store a typed u64 through a hoisted data pointer without updating length.
#[no_mangle]
pub extern "C" fn rt_typed_words_u64_store_known_data_at(
    _header_ptr: i64,
    data_ptr: i64,
    index: i64,
    value: i64,
) -> bool {
    if data_ptr == 0 || index < 0 {
        return false;
    }
    unsafe {
        let arr = _header_ptr as *const RuntimeArray;
        if _header_ptr != 0 && (*arr).is_u64_packed() {
            *((data_ptr as *mut u64).add(index as usize)) = value as u64;
        } else {
            *((data_ptr as *mut RuntimeValue).add(index as usize)) = RuntimeValue::from_int(value);
        }
        true
    }
}

/// Push an element to an array, growing the array if necessary.
/// This is the default push behavior - arrays automatically grow.
///
/// The `RuntimeArray` header lives in a stable allocation; only the element
/// buffer (`data`) is reallocated on grow. The caller's array pointer stays
/// valid.
#[no_mangle]
pub extern "C" fn rt_array_push_grow(array: RuntimeValue, value: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        if (*arr).is_byte_packed() {
            if (*arr).len >= (*arr).capacity {
                let old_cap = (*arr).capacity;
                let new_cap = (old_cap * 2).max(4);
                let old_layout = byte_array_data_layout(old_cap);
                let new_size = byte_array_data_layout(new_cap).size();
                let new_data = if (*arr).data.is_null() {
                    std::alloc::alloc_zeroed(byte_array_data_layout(new_cap)) as *mut RuntimeValue
                } else {
                    std::alloc::realloc((*arr).data as *mut u8, old_layout, new_size) as *mut RuntimeValue
                };
                if new_data.is_null() {
                    return false;
                }
                let new_tail_bytes = new_size - old_cap as usize;
                if new_tail_bytes > 0 {
                    std::ptr::write_bytes((new_data as *mut u8).add(old_cap as usize), 0, new_tail_bytes);
                }
                note_array_data_swap((*arr).data, old_layout.size(), new_size);
                (*arr).data = new_data;
                (*arr).capacity = new_cap;
            }
            *((*arr).data as *mut u8).add((*arr).len as usize) = (value.as_int() & 0xff) as u8;
            (*arr).len += 1;
            return true;
        }

        if (*arr).is_u64_packed() {
            if (*arr).len >= (*arr).capacity {
                let old_cap = (*arr).capacity;
                let new_cap = (old_cap * 2).max(4);
                let old_layout = array_data_layout(old_cap);
                let new_size = array_data_layout(new_cap).size();
                let new_data = if (*arr).data.is_null() {
                    std::alloc::alloc_zeroed(array_data_layout(new_cap)) as *mut RuntimeValue
                } else {
                    std::alloc::realloc((*arr).data as *mut u8, old_layout, new_size) as *mut RuntimeValue
                };
                if new_data.is_null() {
                    return false;
                }
                let old_len_bytes = old_cap as usize * std::mem::size_of::<RuntimeValue>();
                if new_size > old_len_bytes {
                    std::ptr::write_bytes((new_data as *mut u8).add(old_len_bytes), 0, new_size - old_len_bytes);
                }
                note_array_data_swap((*arr).data, old_layout.size(), new_size);
                (*arr).data = new_data;
                (*arr).capacity = new_cap;
            }
            *((*arr).data as *mut u64).add((*arr).len as usize) = value.as_int() as u64;
            (*arr).len += 1;
            return true;
        }

        if (*arr).len >= (*arr).capacity {
            let old_cap = (*arr).capacity;
            let new_cap = (old_cap * 2).max(4);
            let old_layout = array_data_layout(old_cap);
            let new_size = array_data_layout(new_cap).size();
            let new_data = if (*arr).data.is_null() {
                std::alloc::alloc_zeroed(array_data_layout(new_cap)) as *mut RuntimeValue
            } else {
                std::alloc::realloc((*arr).data as *mut u8, old_layout, new_size) as *mut RuntimeValue
            };
            if new_data.is_null() {
                return false;
            }
            // Zero-init the newly grown tail so later reads of unwritten slots
            // return NIL instead of leaked memory.
            let old_len_bytes = old_cap as usize * std::mem::size_of::<RuntimeValue>();
            let new_tail_bytes = new_size - old_len_bytes;
            if new_tail_bytes > 0 {
                std::ptr::write_bytes((new_data as *mut u8).add(old_len_bytes), 0, new_tail_bytes);
            }
            note_array_data_swap((*arr).data, old_layout.size(), new_size);
            (*arr).data = new_data;
            (*arr).capacity = new_cap;
        }

        *(*arr).data.add((*arr).len as usize) = value;
        (*arr).len += 1;
        true
    }
}

/// Bulk-append `count` elements from `src` array into `dst` array.
///
/// Copies `count` `RuntimeValue` slots (8 bytes each) from `src.data` into
/// `dst`, growing `dst` as needed.  This bypasses the SplValue slot layout
/// limitation for SIMD packed-byte bulk copy (bug_simd_bulk_copy_blocked_by_spl_array_layout
/// workaround Option B).
///
/// Returns `false` if either pointer is invalid or allocation fails.
#[no_mangle]
pub extern "C" fn rt_array_extend_i64(dst: RuntimeValue, src: RuntimeValue, count: i64) -> bool {
    if count <= 0 {
        return true;
    }
    let n = count as u64;
    let dst_arr = as_typed_ptr!(mut dst, HeapObjectType::Array, RuntimeArray, false);
    let src_arr = as_typed_ptr!(src, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let src_len = (*src_arr).len;
        if n > src_len {
            return false;
        }
        if (*dst_arr).is_byte_packed() || (*src_arr).is_byte_packed() {
            if !(*dst_arr).is_byte_packed() || !(*src_arr).is_byte_packed() {
                return false;
            }
            let needed = (*dst_arr).len + n;
            if needed > (*dst_arr).capacity {
                let old_cap = (*dst_arr).capacity;
                let new_cap = needed.max(old_cap * 2).max(4);
                let old_layout = byte_array_data_layout(old_cap);
                let new_size = byte_array_data_layout(new_cap).size();
                let new_data = if (*dst_arr).data.is_null() {
                    std::alloc::alloc_zeroed(byte_array_data_layout(new_cap)) as *mut RuntimeValue
                } else {
                    std::alloc::realloc((*dst_arr).data as *mut u8, old_layout, new_size) as *mut RuntimeValue
                };
                if new_data.is_null() {
                    return false;
                }
                let new_tail_bytes = new_size - old_cap as usize;
                if new_tail_bytes > 0 {
                    std::ptr::write_bytes((new_data as *mut u8).add(old_cap as usize), 0, new_tail_bytes);
                }
                note_array_data_swap((*dst_arr).data, old_layout.size(), new_size);
                (*dst_arr).data = new_data;
                (*dst_arr).capacity = new_cap;
            }
            std::ptr::copy_nonoverlapping(
                (*src_arr).data as *const u8,
                ((*dst_arr).data as *mut u8).add((*dst_arr).len as usize),
                n as usize,
            );
            (*dst_arr).len += n;
            return true;
        }

        let needed = (*dst_arr).len + n;
        if needed > (*dst_arr).capacity {
            let old_cap = (*dst_arr).capacity;
            let new_cap = needed.max(old_cap * 2).max(4);
            let old_layout = array_data_layout(old_cap);
            let new_size = array_data_layout(new_cap).size();
            let new_data = if (*dst_arr).data.is_null() {
                std::alloc::alloc_zeroed(array_data_layout(new_cap)) as *mut RuntimeValue
            } else {
                std::alloc::realloc((*dst_arr).data as *mut u8, old_layout, new_size) as *mut RuntimeValue
            };
            if new_data.is_null() {
                return false;
            }
            let old_len_bytes = old_cap as usize * std::mem::size_of::<RuntimeValue>();
            let new_tail_bytes = new_size - old_len_bytes;
            if new_tail_bytes > 0 {
                std::ptr::write_bytes((new_data as *mut u8).add(old_len_bytes), 0, new_tail_bytes);
            }
            note_array_data_swap((*dst_arr).data, old_layout.size(), new_size);
            (*dst_arr).data = new_data;
            (*dst_arr).capacity = new_cap;
        }
        std::ptr::copy_nonoverlapping(
            (*src_arr).data,
            (*dst_arr).data.add((*dst_arr).len as usize),
            n as usize,
        );
        (*dst_arr).len += n;
        true
    }
}

/// Push element without grow (legacy behavior)
#[no_mangle]
pub extern "C" fn rt_array_push_no_grow(array: RuntimeValue, value: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        if (*arr).len >= (*arr).capacity || (*arr).data.is_null() {
            return false;
        }
        if (*arr).is_byte_packed() {
            *((*arr).data as *mut u8).add((*arr).len as usize) = (value.as_int() & 0xff) as u8;
            (*arr).len += 1;
            return true;
        }
        if (*arr).is_u64_packed() {
            *((*arr).data as *mut u64).add((*arr).len as usize) = value.as_int() as u64;
            (*arr).len += 1;
            return true;
        }
        *(*arr).data.add((*arr).len as usize) = value;
        (*arr).len += 1;
        true
    }
}

#[no_mangle]
pub extern "C" fn rt_array_new_with_cap_i64(cap: i64) -> RuntimeValue {
    rt_array_new_uninit(cap as u64)
}

#[no_mangle]
pub extern "C" fn rt_array_new_with_cap(cap: i64) -> RuntimeValue {
    rt_array_new_uninit(cap as u64)
}

#[no_mangle]
pub extern "C" fn rt_array_new_with_cap_u64(cap: i64) -> RuntimeValue {
    rt_array_new_uninit_u64(cap as u64)
}

#[no_mangle]
pub extern "C" fn rt_array_new_with_cap_text(cap: i64) -> RuntimeValue {
    rt_array_new_uninit(cap as u64)
}

#[no_mangle]
pub extern "C" fn rt_array_new_with_cap_js_value(cap: i64) -> RuntimeValue {
    rt_array_new_uninit(cap as u64)
}

#[no_mangle]
pub extern "C" fn rt_array_new_with_cap_bool(cap: i64) -> RuntimeValue {
    rt_array_new_uninit(cap as u64)
}

/// Pop an element from an array
#[no_mangle]
pub extern "C" fn rt_array_pop(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        if (*arr).len == 0 || (*arr).data.is_null() {
            return RuntimeValue::NIL;
        }
        (*arr).len -= 1;
        if (*arr).is_byte_packed() {
            return RuntimeValue::from_int(*((*arr).data as *const u8).add((*arr).len as usize) as i64);
        }
        if (*arr).is_u64_packed() {
            return RuntimeValue::from_int(*((*arr).data as *const u64).add((*arr).len as usize) as i64);
        }
        *(*arr).data.add((*arr).len as usize)
    }
}

/// Remove the element at `index` from an array IN PLACE and return THAT ELEMENT.
///
/// This function did not exist until 2026-08-08, even though
/// `method_registry/builtins.rs` had declared array `remove` as
/// `RuntimeFn::Simple("rt_array_remove")` all along — the symbol was referenced
/// by the registry and implemented nowhere. Codegen's name-keyed method table
/// therefore mapped a bare `.remove(i)` to `rt_dict_remove` for EVERY receiver,
/// and `rt_dict_remove` type-checks its receiver as a Dict: on an Array it took
/// the `as_typed_ptr!` early-out, returned NIL, and mutated nothing. So
/// `arr.remove(1)` was a complete no-op on the compiled lane that also discarded
/// the element it was supposed to return.
/// See doc/08_tracking/bug/array_remove_returns_mutated_array_not_removed_element_2026-07-20.md
///
/// CONTRACT — returns the REMOVED ELEMENT, mutates the receiver in place. This
/// matches the sibling `rt_array_pop` directly above (in-place, returns the
/// element, declared `is_mutating: true`) and `rt_dict_remove` (removes the
/// entry, returns the VALUE). Returning the mutated array — what the AST
/// interpreter used to do — had no runtime implementation, no HIR type, and no
/// spec behind it.
///
/// An out-of-range index is a NO-OP returning NIL, mirroring `rt_array_pop` on
/// an empty array. It must never panic: this is `extern "C"` and unwinding
/// across the FFI boundary from JIT-compiled code is undefined behaviour.
///
/// All three storage layouts are handled, exactly as `rt_array_pop` does. Byte-
/// and u64-packed arrays store raw scalars rather than tagged `RuntimeValue`s,
/// so their element must be read through the correctly-sized pointer and
/// re-tagged with `from_int`; reading a packed array as `RuntimeValue` would
/// hand back a raw, untagged integer that the caller then misdecodes.
#[no_mangle]
pub extern "C" fn rt_array_remove(array: RuntimeValue, index: i64) -> RuntimeValue {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len;
        if (*arr).data.is_null() || index < 0 || (index as u64) >= len {
            return RuntimeValue::NIL;
        }
        let idx = index as usize;
        let last = (len - 1) as usize;

        if (*arr).is_byte_packed() {
            let base = (*arr).data as *mut u8;
            let removed = *base.add(idx) as i64;
            // Shift the tail down one slot. `copy` (memmove) is required, not
            // `copy_nonoverlapping`: source and destination overlap by design.
            std::ptr::copy(base.add(idx + 1), base.add(idx), last - idx);
            (*arr).len -= 1;
            return RuntimeValue::from_int(removed);
        }
        if (*arr).is_u64_packed() {
            let base = (*arr).data as *mut u64;
            let removed = *base.add(idx) as i64;
            std::ptr::copy(base.add(idx + 1), base.add(idx), last - idx);
            (*arr).len -= 1;
            return RuntimeValue::from_int(removed);
        }

        let base = (*arr).data;
        let removed = *base.add(idx);
        std::ptr::copy(base.add(idx + 1), base.add(idx), last - idx);
        (*arr).len -= 1;
        removed
    }
}

/// `remove`: receiver-dispatched, so a bare `.remove(k)` is safe on an untyped
/// receiver.
///
/// Codegen's method table is keyed on the METHOD NAME ALONE and carries no
/// receiver type (see `is_bare_builtin_collection_method` in
/// codegen/instr/closures_structs.rs, where `("remove", 1)` is already listed
/// as an erased-receiver hazard). Routing that name straight to
/// `rt_dict_remove` is what silently broke every array `.remove(i)` on the
/// compiled lane. This dispatcher inspects the receiver's heap type at runtime
/// and picks the right implementation, the same shape already used by
/// `rt_pop`, `rt_reverse` and `rt_index_of`.
///
/// A non-Array, non-Dict receiver falls through to `rt_dict_remove`, preserving
/// the previous behaviour for every receiver that is not an array — this change
/// only ever ADDS the array case.
///
/// NAMED `rt_collection_remove`, NOT `rt_remove`. `rt_remove` is already taken,
/// by the POSIX file-deletion wrapper `int64_t rt_remove(const char *path)` in
/// `src/runtime/runtime_hosted_fs.c` (and `src/runtime/runtime.c`). Defining a
/// second `rt_remove` produced a hard `rust-lld: error: duplicate symbol` —
/// which is the GOOD outcome. The repo builds some link steps with `-z muldefs`
/// (see reference: "muldefs makes duplicate symbols silent, not fatal"), and
/// under that flag the linker would silently pick one definition: every
/// `arr.remove(i)` would have called `unlink()` on a pointer-shaped index, or
/// every file delete would have gone to the collection helper.
#[no_mangle]
pub extern "C" fn rt_collection_remove(receiver: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        // Array indices arrive as TAGGED ints; `as_int` untags (an arithmetic
        // shift). It is explicitly documented as UNDEFINED on a non-int, so the
        // `is_int` test is required, not defensive padding — calling it on, say,
        // a heap pointer would yield a garbage index. A non-integer index on an
        // array is out of range by definition, and `rt_array_remove` treats a
        // negative index as a no-op.
        let index = if key.is_int() { key.as_int() } else { -1 };
        return rt_array_remove(receiver, index);
    }
    crate::value::dict::rt_dict_remove(receiver, key)
}

/// Clear all elements from an array
#[no_mangle]
pub extern "C" fn rt_array_clear(array: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        (*arr).len = 0;
        true
    }
}

/// Reclaim flat-parser scratch heap objects after conversion creates owned
/// frontend values. Each parser thread owns at most one scope.
extern "C" {
    fn rt_transient_raw_scope_begin() -> i32;
    fn rt_transient_raw_scope_pause() -> i32;
    fn rt_transient_raw_scope_end() -> i32;
    fn rt_transient_raw_words(value: i64, words: *mut *const usize, canonical_ptr: *mut usize) -> i64;
    fn rt_transient_raw_promote(ptr: usize) -> i32;
}

#[no_mangle]
pub extern "C" fn rt_transient_array_scope_begin() -> bool {
    TRANSIENT_HEAP_SCOPE.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.is_some() {
            return false;
        }
        if unsafe { rt_transient_raw_scope_begin() } == 0 {
            return false;
        }
        *slot = Some(TransientHeapScope {
            paused: false,
            objects: Vec::new(),
        });
        true
    })
}

#[no_mangle]
pub extern "C" fn rt_transient_array_scope_pause() -> bool {
    TRANSIENT_HEAP_SCOPE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(scope) = slot.as_mut() else {
            return false;
        };
        if unsafe { rt_transient_raw_scope_pause() } == 0 {
            return false;
        }
        scope.paused = true;
        true
    })
}

fn transient_heap_children(value: RuntimeValue) -> Option<Vec<RuntimeValue>> {
    if !value.is_heap() {
        return Some(Vec::new());
    }
    match value.heap_type()? {
        HeapObjectType::Array => {
            let ptr = get_typed_ptr::<RuntimeArray>(value, HeapObjectType::Array)?;
            unsafe {
                if (*ptr).is_byte_packed() || (*ptr).is_u64_packed() {
                    Some(Vec::new())
                } else {
                    Some((*ptr).as_slice().to_vec())
                }
            }
        }
        HeapObjectType::Tuple => {
            let ptr = get_typed_ptr::<RuntimeTuple>(value, HeapObjectType::Tuple)?;
            unsafe { Some((*ptr).as_slice().to_vec()) }
        }
        HeapObjectType::Dict => {
            let ptr = get_typed_ptr::<RuntimeDict>(value, HeapObjectType::Dict)?;
            unsafe {
                if (*ptr).data.is_null() {
                    return Some(Vec::new());
                }
                let mut children = Vec::with_capacity((*ptr).len as usize * 2);
                for index in 0..(*ptr).capacity as usize {
                    let key = *(*ptr).data.add(index * 2);
                    if key.is_nil() {
                        continue;
                    }
                    children.push(key);
                    children.push(*(*ptr).data.add(index * 2 + 1));
                }
                Some(children)
            }
        }
        HeapObjectType::Object => {
            let ptr = get_typed_ptr::<RuntimeObject>(value, HeapObjectType::Object)?;
            unsafe { Some((*ptr).fields().to_vec()) }
        }
        HeapObjectType::Closure => {
            let ptr = get_typed_ptr::<RuntimeClosure>(value, HeapObjectType::Closure)?;
            unsafe { Some((*ptr).captures().to_vec()) }
        }
        HeapObjectType::Enum => {
            let ptr = get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum)?;
            unsafe { Some(vec![(*ptr).payload]) }
        }
        _ => Some(Vec::new()),
    }
}

fn free_transient_heap(value: RuntimeValue) {
    match value.heap_type() {
        Some(HeapObjectType::String) => {
            let _ = rt_string_free(value);
        }
        Some(HeapObjectType::Array) => rt_array_free(value),
        Some(HeapObjectType::Tuple) => rt_tuple_free(value),
        Some(HeapObjectType::Dict) => super::dict::rt_dict_free(value),
        Some(
            HeapObjectType::Object
            | HeapObjectType::Closure
            | HeapObjectType::Enum
            | HeapObjectType::Float
            | HeapObjectType::UInt,
        ) => unsafe {
            let ptr = value.as_heap_ptr();
            let size = (*ptr).size as usize;
            if let Ok(layout) = std::alloc::Layout::from_size_align(size, 8) {
                if unregister_heap_ptr_checked(ptr) {
                    std::alloc::dealloc(ptr as *mut u8, layout);
                }
            }
        },
        _ => (),
    }
}

/// Keep transient heap objects reachable from a retained graph when the scope ends.
#[no_mangle]
pub extern "C" fn rt_transient_heap_promote(value: RuntimeValue) -> bool {
    let mut root_words = std::ptr::null();
    let mut root_ptr = 0usize;
    let root_raw = unsafe { rt_transient_raw_words(value.0 as i64, &mut root_words, &mut root_ptr) >= 0 };
    if !root_raw && (!value.is_heap() || value.heap_type().is_none()) {
        return false;
    }
    TRANSIENT_HEAP_SCOPE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(scope) = slot.as_mut() else {
            return false;
        };
        if !scope.paused {
            return false;
        }

        let mut pending = vec![value];
        let mut reachable_heap = HashSet::new();
        let mut reachable_raw = HashSet::new();
        while let Some(current) = pending.pop() {
            let mut words = std::ptr::null();
            let mut canonical_ptr = 0usize;
            let word_count = unsafe { rt_transient_raw_words(current.0 as i64, &mut words, &mut canonical_ptr) };
            if word_count >= 0 {
                if !reachable_raw.insert(canonical_ptr) {
                    continue;
                }
                if word_count > 0 {
                    if words.is_null() {
                        return false;
                    }
                    let raw_words = unsafe { std::slice::from_raw_parts(words, word_count as usize) };
                    pending.extend(raw_words.iter().map(|word| RuntimeValue(*word as u64)));
                }
                continue;
            }
            if !reachable_heap.insert(current.0) {
                continue;
            }
            if let Some(children) = transient_heap_children(current) {
                pending.extend(children);
            }
        }
        for ptr in reachable_raw {
            if unsafe { rt_transient_raw_promote(ptr) } == 0 {
                return false;
            }
        }
        scope.objects.retain(|object| !reachable_heap.contains(&object.0));
        true
    })
}

#[no_mangle]
pub extern "C" fn rt_transient_array_scope_end() -> bool {
    let scope = TRANSIENT_HEAP_SCOPE.with(|slot| slot.borrow_mut().take());
    let Some(scope) = scope else {
        return false;
    };
    for object in scope.objects {
        free_transient_heap(object);
    }
    unsafe { rt_transient_raw_scope_end() != 0 }
}

/// Create an array from a slice of RuntimeValues
///
/// This is a convenience function for creating arrays with initial values.
/// The array will have capacity equal to the slice length.
pub fn rt_array_create_from_slice(values: &[RuntimeValue]) -> RuntimeValue {
    let capacity = values.len() as u64;
    let array = rt_array_new(capacity);

    if array.is_nil() {
        return RuntimeValue::NIL;
    }

    // Push all values into the array
    for value in values {
        if !rt_array_push(array, *value) {
            return RuntimeValue::NIL;
        }
    }

    array
}

/// Free a heap-allocated array.
#[no_mangle]
#[allow(clippy::unused_unit)]
pub extern "C" fn rt_array_free(array: RuntimeValue) {
    let ptr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, ());
    unsafe {
        if !(*ptr).data.is_null() {
            let data_layout = if (*ptr).is_byte_packed() {
                byte_array_data_layout((*ptr).capacity)
            } else {
                array_data_layout((*ptr).capacity)
            };
            note_aux_free(HeapObjectType::Array as u8, data_layout.size() as u64);
            std::alloc::dealloc((*ptr).data as *mut u8, data_layout);
            (*ptr).data = std::ptr::null_mut();
        }
        let header_layout = std::alloc::Layout::from_size_align(std::mem::size_of::<RuntimeArray>(), 8).unwrap();
        unregister_heap_ptr(ptr as *mut HeapHeader);
        std::alloc::dealloc(ptr as *mut u8, header_layout);
    }
}

/// Bounds the planner's own memory; exceeding it refuses rather than grows.
/// Same value as `RT_CORE_DEEP_FREE_MAX_NODES` in runtime_native.c.
const RT_DEEP_FREE_MAX_NODES: usize = 1 << 22;

#[derive(Clone, Copy, PartialEq, Eq)]
enum DeepFreeKind {
    Array,
    String,
}

enum DeepFreeClass {
    /// Nothing to free and nothing to strand.
    Leaf,
    /// Not provably freeable — refuses the WHOLE call.
    Refuse,
    Node(*mut HeapHeader, DeepFreeKind),
}

/// Classify one element slot for `rt_array_free_deep`.
///
/// Every dereference is gated on a registry membership test (a pure pointer
/// comparison inside `get_typed_ptr_mut`), so a raw i64 that merely aliases the
/// heap tag is never dereferenced. Twin of `rt_core_deep_free_classify`
/// (runtime_native.c:5311).
fn deep_free_classify(value: RuntimeValue) -> DeepFreeClass {
    // Immediates (int / float / nil / bool) hold no heap reference. Mirrors the
    // C `raw < 4096` + `tag != TAG_HEAP` leaf tests.
    if !value.is_heap() {
        return DeepFreeClass::Leaf;
    }
    if let Some(ptr) = get_typed_ptr_mut::<RuntimeArray>(value, HeapObjectType::Array) {
        return DeepFreeClass::Node(ptr as *mut HeapHeader, DeepFreeKind::Array);
    }
    if let Some(ptr) = get_typed_ptr_mut::<RuntimeString>(value, HeapObjectType::String) {
        // RT_STRING_FLAG_SHARED marks the process-wide short-string cache and
        // the literal intern table, whose objects are handed to unrelated
        // holders — rt_string_free's own rule.
        if unsafe { (*ptr).header.reserved & RT_STRING_FLAG_SHARED } != 0 {
            return DeepFreeClass::Refuse;
        }
        return DeepFreeClass::Node(ptr as *mut HeapHeader, DeepFreeKind::String);
    }
    // Heap-tagged but neither a registered array nor a freeable registered
    // string: dicts, tuples, objects, closures, enums, foreign pointers,
    // already-freed pointers, and raw i64 payloads that alias the tag bits.
    // Freeing the holding buffer would strand them irreversibly, so refuse.
    DeepFreeClass::Refuse
}

/// Deep (recursive) array free. Returns 1 only if the ENTIRE reachable
/// structure was reclaimed, 0 if the call was refused having freed NOTHING.
///
/// Rust-side twin of `rt_array_free_deep` in src/runtime/runtime_native.c
/// (:5335), matching its contract bit for bit so the C-linked self-hosted lane
/// and the Rust seed/JIT lane resolve the same symbol with the same semantics.
/// `rt_array_free` above is SHALLOW: it releases the outer buffer and header
/// and leaks every heap element the buffer pointed at.
///
/// PARTIAL-FREE POLICY: ALL-OR-NOTHING, decided in two phases. Phase 1 walks
/// the whole structure READ-ONLY and classifies every reachable node, freeing
/// nothing; if any node is not provably freeable the call returns 0 having
/// freed nothing at all. Only a fully-provable structure reaches phase 2.
///
/// Rejecting the "free the outer buffer anyway" alternative: a refused element
/// is reachable ONLY through the buffer that holds it, so freeing the buffer
/// makes it simultaneously unreachable AND unfreeable — a permanent leak.
/// Refusing also leaks, but reversibly: the caller still holds the root and can
/// retry, free the elements individually, or fall back to `rt_array_free`. A
/// reversible leak strictly dominates an irreversible one.
///
/// Provably freeable: byte-packed / u64-packed payloads (no heap references by
/// construction, element scan skipped), immediate elements, non-shared
/// registered heap strings, and registered arrays recursively under these same
/// rules. Everything else refuses.
///
/// ALIASING AND CYCLES: `RuntimeValue` is `Copy`, so an element may be the
/// array itself or appear twice. Phase 1 keeps a `seen` pointer set and the
/// second sighting of any node refuses the whole call, proving the reachable
/// structure is a TREE — which is what makes freeing it safe. That can only
/// rule out aliases INTERNAL to the structure: an interior node aliased from
/// OUTSIDE is undetectable here, exactly as `rt_string_free` cannot detect a
/// second holder. The caller must own the whole subtree, not merely the root.
/// Likewise not thread-safe against a concurrent free of the same objects.
#[no_mangle]
pub extern "C" fn rt_array_free_deep(value: RuntimeValue) -> i64 {
    // The root must be a registered array; a string root belongs to
    // rt_string_free, not here.
    let Some(root) = get_typed_ptr_mut::<RuntimeArray>(value, HeapObjectType::Array) else {
        return 0;
    };

    // `plan` doubles as the BFS worklist, so this is iterative — a deeply
    // nested structure cannot blow the stack.
    let mut plan: Vec<(*mut HeapHeader, DeepFreeKind)> = vec![(root as *mut HeapHeader, DeepFreeKind::Array)];
    let mut seen: HashSet<usize> = HashSet::new();
    seen.insert(root as usize);

    // Phase 1: read-only breadth-first classification.
    let mut refused = false;
    let mut index = 0usize;
    while !refused && index < plan.len() {
        let (ptr, kind) = plan[index];
        index += 1;
        if kind != DeepFreeKind::Array {
            continue;
        }
        let array = ptr as *mut RuntimeArray;
        let slots: Vec<RuntimeValue> = unsafe {
            if (*array).is_byte_packed() || (*array).is_u64_packed() || (*array).data.is_null() {
                continue;
            }
            (*array).as_slice().to_vec()
        };
        for slot in slots {
            match deep_free_classify(slot) {
                DeepFreeClass::Leaf => continue,
                DeepFreeClass::Refuse => {
                    refused = true;
                    break;
                }
                DeepFreeClass::Node(child, child_kind) => {
                    // Second sighting = alias or cycle: refuse.
                    if !seen.insert(child as usize) {
                        refused = true;
                        break;
                    }
                    if plan.len() >= RT_DEEP_FREE_MAX_NODES {
                        refused = true;
                        break;
                    }
                    plan.push((child, child_kind));
                }
            }
        }
    }

    if refused {
        return 0;
    }

    // Phase 2: commit. Reached only when every node is provably freeable, so no
    // partial state is observable. Freeing top-down is safe because phase 1
    // already copied out every child pointer.
    for (ptr, kind) in plan {
        unsafe {
            match kind {
                DeepFreeKind::Array => {
                    let array = ptr as *mut RuntimeArray;
                    if !unregister_heap_ptr_checked(ptr) {
                        continue;
                    }
                    if !(*array).data.is_null() {
                        let data_layout = if (*array).is_byte_packed() {
                            byte_array_data_layout((*array).capacity)
                        } else {
                            array_data_layout((*array).capacity)
                        };
                        note_aux_free(HeapObjectType::Array as u8, data_layout.size() as u64);
                        std::alloc::dealloc((*array).data as *mut u8, data_layout);
                        (*array).data = std::ptr::null_mut();
                    }
                    let header_layout =
                        std::alloc::Layout::from_size_align(std::mem::size_of::<RuntimeArray>(), 8).unwrap();
                    std::alloc::dealloc(ptr as *mut u8, header_layout);
                }
                DeepFreeKind::String => {
                    let string = ptr as *mut RuntimeString;
                    // Read len BEFORE unregistering: it sizes the dealloc
                    // layout and must match `alloc_runtime_string` exactly.
                    let len = (*string).len;
                    if !unregister_heap_ptr_checked(ptr) {
                        continue;
                    }
                    let size = std::mem::size_of::<RuntimeString>() + len as usize;
                    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
                    std::alloc::dealloc(ptr as *mut u8, layout);
                }
            }
        }
    }
    1
}

/// Free a heap string. Returns 1 if the object was reclaimed, 0 if refused.
///
/// Rust-side twin of `rt_string_free` in src/runtime/runtime_native.c, matching
/// its safety contract bit for bit so JIT/AOT/self-hosted paths agree. This
/// runtime has no refcounting and `RuntimeValue` is `Copy` (aliasing by
/// construction), so the CALLER must own the only reference.
///
/// Refuses, rather than trusting the caller, when the value is:
///   * not a heap string (`get_typed_ptr_mut` rejects non-heap, misaligned, and
///     wrong-`object_type` values),
///   * absent from `HEAP_ALLOCATION_REGISTRY` — already freed, or never
///     registered (`get_typed_ptr_mut` checks membership, and
///     `unregister_heap_ptr_checked` re-checks it atomically under the lock so
///     only one racing caller can proceed),
///   * owned by a process-wide cache — `SHORT_STRING_CACHE` (len<=1) or
///     `STRING_LITERAL_INTERN` — flagged via `RT_STRING_FLAG_SHARED`.
///
/// A refusal leaks; a wrong free corrupts every other holder. The bias toward
/// refusing is deliberate.
#[no_mangle]
pub extern "C" fn rt_string_free(value: RuntimeValue) -> i64 {
    let ptr = as_typed_ptr!(mut value, HeapObjectType::String, RuntimeString, 0);
    unsafe {
        if ((*ptr).header.reserved & RT_STRING_FLAG_SHARED) != 0 {
            return 0;
        }
        // Read len BEFORE unregistering: it sizes the dealloc layout and must
        // match `alloc_runtime_string` exactly.
        let len = (*ptr).len;
        if !unregister_heap_ptr_checked(ptr as *mut HeapHeader) {
            return 0;
        }
        let size = std::mem::size_of::<RuntimeString>() + len as usize;
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(ptr as *mut u8, layout);
    }
    1
}

// ============================================================================
// Tuple SFFI functions
// ============================================================================

/// Allocate a new tuple with the given length
#[no_mangle]
pub extern "C" fn rt_tuple_new(len: u64) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeTuple>() + len as usize * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeTuple;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Tuple, size as u32);
        (*ptr).len = len;

        track_transient_heap(RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader))
    }
}

/// Get an element from a tuple
#[no_mangle]
pub extern "C" fn rt_tuple_get(tuple: RuntimeValue, index: u64) -> RuntimeValue {
    // Lenient typing lets array literals flow into tuple-typed slots
    // (e.g. `return [a, b, c]` from a function declared `-> (A, B, C)`),
    // so statically-tuple-typed indexing must tolerate a runtime Array.
    // Without this fallback it returned NIL and callers dereferenced nil
    // (stage4 `desugar_module` SIGSEGV destructuring
    // `desugar_async_function(func)`).
    if tuple.heap_type() == Some(HeapObjectType::Array) {
        return rt_array_get(tuple, index as i64);
    }
    let tup = as_typed_ptr!(tuple, HeapObjectType::Tuple, RuntimeTuple, RuntimeValue::NIL);
    unsafe {
        if index >= (*tup).len {
            return RuntimeValue::NIL;
        }
        (*tup).as_slice()[index as usize]
    }
}

/// Set an element in a tuple (used during construction)
#[no_mangle]
pub extern "C" fn rt_tuple_set(tuple: RuntimeValue, index: u64, value: RuntimeValue) -> bool {
    let tup = as_typed_ptr!(mut tuple, HeapObjectType::Tuple, RuntimeTuple, false);
    unsafe {
        if index >= (*tup).len {
            return false;
        }
        let data_ptr = (tup.add(1)) as *mut RuntimeValue;
        *data_ptr.add(index as usize) = value;
        true
    }
}

/// Get the length of a tuple
#[no_mangle]
pub extern "C" fn rt_tuple_len(tuple: RuntimeValue) -> i64 {
    let tup = as_typed_ptr!(tuple, HeapObjectType::Tuple, RuntimeTuple, -1);
    unsafe { (*tup).len as i64 }
}

/// Free a heap-allocated tuple.
#[no_mangle]
#[allow(clippy::unused_unit)]
pub extern "C" fn rt_tuple_free(tuple: RuntimeValue) {
    let ptr = as_typed_ptr!(mut tuple, HeapObjectType::Tuple, RuntimeTuple, ());
    unsafe {
        let size = std::mem::size_of::<RuntimeTuple>() + (*ptr).len as usize * std::mem::size_of::<RuntimeValue>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        unregister_heap_ptr(ptr as *mut HeapHeader);
        std::alloc::dealloc(ptr as *mut u8, layout);
    }
}

// ============================================================================
// String SFFI functions
// ============================================================================

/// Interned boxing for compile-time string LITERALS only.
///
/// Codegen emits one `rt_string_new` per literal *evaluation*, and this no-GC
/// tier never frees, so a hot literal comparison (`tok == "fn"`) leaks one
/// registered heap string per execution — measured ~9 live objects per source
/// character during self-hosted parse
/// (doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md).
/// Literal bytes live in the binary's rodata: the (address, len) pair is
/// immutable and stable for the process lifetime, so every evaluation of the
/// same literal site can share a single boxed string. Callers MUST only pass
/// static literal data (rodata) — never a reusable heap buffer, whose address
/// could be recycled with different content.
static STRING_LITERAL_INTERN: OnceLock<std::sync::Mutex<std::collections::HashMap<(usize, u64), u64>>> =
    OnceLock::new();

#[no_mangle]
pub extern "C" fn rt_string_new_literal(bytes: *const u8, len: u64) -> RuntimeValue {
    if len <= 1 {
        // rt_string_new already returns process-wide cached values for these.
        return rt_string_new(bytes, len);
    }
    let key = (bytes as usize, len);
    let map = STRING_LITERAL_INTERN.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(guard) = map.lock() {
        if let Some(&raw) = guard.get(&key) {
            return RuntimeValue::from_raw(raw);
        }
    }
    let value = rt_string_new_uncached_untracked(bytes, len);
    // Owned by the intern table from here on: every later evaluation of this
    // literal site returns this same object, so rt_string_free must refuse it.
    mark_string_shared(value);
    if let Ok(mut guard) = map.lock() {
        guard.insert(key, value.to_raw());
    }
    value
}

/// Create a string from UTF-8 bytes
///
/// # Safety
/// The bytes must be valid UTF-8.
#[no_mangle]
pub extern "C" fn rt_string_new(bytes: *const u8, len: u64) -> RuntimeValue {
    if bytes.is_null() && len > 0 {
        return RuntimeValue::NIL;
    }

    if len == 0 {
        return short_string_cache()[0];
    }
    if len == 1 {
        let byte = unsafe { *bytes };
        return short_string_cache()[byte as usize + 1];
    }

    rt_string_new_uncached(bytes, len)
}

pub(crate) fn rt_string_new_with_len_hash(bytes: *const u8, len: u64) -> RuntimeValue {
    if bytes.is_null() && len > 0 {
        return RuntimeValue::NIL;
    }

    unsafe {
        let Some(ptr) = alloc_runtime_string(len) else {
            return RuntimeValue::NIL;
        };

        if len > 0 {
            let data_ptr = ptr.add(1) as *mut u8;
            std::ptr::copy_nonoverlapping(bytes, data_ptr, len as usize);
        }
        (*ptr).hash = len;

        track_transient_heap(RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader))
    }
}

/// Get the length of a string in bytes
#[no_mangle]
pub extern "C" fn rt_string_len(string: RuntimeValue) -> i64 {
    let str_ptr = as_typed_ptr!(string, HeapObjectType::String, RuntimeString, -1);
    unsafe { (*str_ptr).len as i64 }
}

/// Generic length function that works on any collection type (Array, String, Tuple, Dict)
/// Returns -1 for non-collection types
#[no_mangle]
pub extern "C" fn rt_len(value: RuntimeValue) -> i64 {
    match value.heap_type() {
        Some(HeapObjectType::Array) => rt_array_len(value),
        Some(HeapObjectType::String) => rt_string_len(value),
        Some(HeapObjectType::Tuple) => rt_tuple_len(value),
        Some(HeapObjectType::Dict) => super::dict::rt_dict_len(value),
        _ => -1,
    }
}

/// Get a pointer to the string data
#[no_mangle]
pub extern "C" fn rt_string_data(string: RuntimeValue) -> *const u8 {
    let str_ptr = as_typed_ptr!(string, HeapObjectType::String, RuntimeString, std::ptr::null());
    unsafe { str_ptr.add(1) as *const u8 }
}

/// Return UTF-8 data for a tagged runtime string, or preserve an already-raw
/// C string pointer used by bootstrap/interpreter call sites.
#[no_mangle]
pub extern "C" fn rt_interp_cstr(value: RuntimeValue) -> *const u8 {
    let data = rt_string_data(value);
    if data.is_null() {
        value.to_raw() as usize as *const u8
    } else {
        data
    }
}

#[cfg(test)]
mod interp_cstr_tests {
    use super::{rt_interp_cstr, rt_string_data, rt_string_new};
    use crate::value::RuntimeValue;

    #[test]
    fn accepts_runtime_string_and_raw_pointer() {
        let bytes = b"Hello";
        let string = rt_string_new(bytes.as_ptr(), bytes.len() as u64);
        assert_eq!(rt_interp_cstr(string), rt_string_data(string));

        let raw = RuntimeValue::from_raw(bytes.as_ptr() as usize as u64);
        assert_eq!(rt_interp_cstr(raw), bytes.as_ptr());
    }
}

/// Concatenate two strings
#[no_mangle]
pub extern "C" fn rt_string_concat(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue {
    let len_a = rt_string_len(a);
    let len_b = rt_string_len(b);

    if len_a < 0 || len_b < 0 {
        return RuntimeValue::NIL;
    }

    let total_len = len_a as u64 + len_b as u64;

    unsafe {
        let Some(ptr) = alloc_runtime_string(total_len) else {
            return RuntimeValue::NIL;
        };

        // Copy first string
        let data_ptr = ptr.add(1) as *mut u8;
        let data_a = rt_string_data(a);
        if !data_a.is_null() && len_a > 0 {
            std::ptr::copy_nonoverlapping(data_a, data_ptr, len_a as usize);
        }

        // Copy second string
        let data_b = rt_string_data(b);
        if !data_b.is_null() && len_b > 0 {
            std::ptr::copy_nonoverlapping(data_b, data_ptr.add(len_a as usize), len_b as usize);
        }

        // Compute hash for concatenated string
        (*ptr).hash = if total_len > 0 {
            fnv1a_hash(std::slice::from_raw_parts(data_ptr, total_len as usize))
        } else {
            0
        };

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Runtime dispatch for `any + any`.
#[no_mangle]
pub extern "C" fn rt_any_add(left: RuntimeValue, right: RuntimeValue) -> RuntimeValue {
    if matches!(left.heap_type(), Some(HeapObjectType::String))
        || matches!(right.heap_type(), Some(HeapObjectType::String))
    {
        return rt_string_concat(rt_to_string(left), rt_to_string(right));
    }

    RuntimeValue::from_int(left.as_int() + right.as_int())
}

/// Shared body for the `is_*` character-class predicates.
///
/// Mirrors the tree-walking interpreter (`interpreter_method/string.rs`, arms
/// `"is_numeric"`, `"is_alpha"`, `"is_digit"`, `"is_alphanumeric"`,
/// `"is_whitespace"`): the empty string is FALSE for every class, and a
/// non-empty string is true only when every `char` satisfies the predicate.
///
/// Classification is per-`char`, not per-byte, so it agrees with the
/// interpreter's `s.chars().all(..)` on non-ASCII input. Invalid UTF-8 is
/// reported as false rather than being silently classified byte-wise, which
/// would disagree with the interpreter.
fn string_all_chars(string: RuntimeValue, pred: fn(char) -> bool) -> i64 {
    let str_len = rt_string_len(string);
    if str_len <= 0 {
        // Includes the non-text receiver case (len < 0): no class claim.
        return 0;
    }
    let data = rt_string_data(string);
    if data.is_null() {
        return 0;
    }
    let bytes = unsafe { std::slice::from_raw_parts(data, str_len as usize) };
    match std::str::from_utf8(bytes) {
        Ok(s) => i64::from(s.chars().all(pred)),
        Err(_) => 0,
    }
}

/// `is_digit` / `is_numeric`: non-empty and all ASCII digits.
///
/// The interpreter gives these two spellings the same ASCII-digit body, so they
/// share one runtime entry point here.
#[no_mangle]
pub extern "C" fn rt_string_is_digit(string: RuntimeValue) -> i64 {
    string_all_chars(string, |c| c.is_ascii_digit())
}

/// `is_alpha` / `is_alphabetic`: non-empty and all alphabetic (Unicode).
#[no_mangle]
pub extern "C" fn rt_string_is_alpha(string: RuntimeValue) -> i64 {
    string_all_chars(string, char::is_alphabetic)
}

/// `is_alphanumeric` / `is_alnum`: non-empty and all alphanumeric (Unicode).
#[no_mangle]
pub extern "C" fn rt_string_is_alnum(string: RuntimeValue) -> i64 {
    string_all_chars(string, char::is_alphanumeric)
}

/// `is_whitespace`: non-empty and all whitespace.
#[no_mangle]
pub extern "C" fn rt_string_is_whitespace(string: RuntimeValue) -> i64 {
    string_all_chars(string, char::is_whitespace)
}

// ---------------------------------------------------------------------------
// Text methods that had NO runtime definition at all.
//
// Every function below existed only in the tree-walking interpreter
// (`interpreter_method/string.rs`). On the compiled lanes the method name fell
// through the dispatch tables to `rt_method_not_found`, which used to fabricate
// the SPECIAL_ERROR sentinel (stringifies as `error`) and keep going. Each one
// mirrors its interpreter arm exactly; where the arm is quoted in a doc comment
// the line number refers to that file.
//
// Convention shared with the pre-existing text functions here: a non-text
// receiver is detected by `rt_string_len(..) < 0` and the receiver is returned
// unchanged rather than a fabricated value.
// ---------------------------------------------------------------------------

/// Borrow a `RuntimeValue` as `&str`, or `None` when it is not valid UTF-8 text.
///
/// `None` also covers the non-text receiver (`rt_string_len` returns a negative
/// length for anything that is not a heap string), which every caller below
/// turns into "return the receiver unchanged".
///
/// # Safety
/// The returned slice borrows the runtime string's buffer. Runtime strings are
/// registered with the collector and outlive the call, matching what the
/// surrounding `from_utf8_unchecked` call sites already assume.
fn string_as_str<'a>(string: RuntimeValue) -> Option<&'a str> {
    let len = rt_string_len(string);
    if len < 0 {
        return None;
    }
    if len == 0 {
        return Some("");
    }
    let data = rt_string_data(string);
    if data.is_null() {
        return Some("");
    }
    let bytes = unsafe { std::slice::from_raw_parts(data, len as usize) };
    std::str::from_utf8(bytes).ok()
}

/// Allocate a new runtime string from a Rust `str`.
fn new_string(s: &str) -> RuntimeValue {
    rt_string_new(s.as_ptr(), s.len() as u64)
}

/// `char_count`: number of Unicode scalar values, as opposed to `len`, which is
/// the BYTE count. Returns -1 for a non-text receiver, matching `rt_string_len`
/// and `rt_len`.
#[no_mangle]
pub extern "C" fn rt_string_char_count(string: RuntimeValue) -> i64 {
    match string_as_str(string) {
        Some(s) => s.chars().count() as i64,
        None => -1,
    }
}

/// `capitalize`: uppercase the first character, lowercase the rest.
#[no_mangle]
pub extern "C" fn rt_string_capitalize(string: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return new_string("");
    };
    let mut out: String = first.to_uppercase().collect();
    for c in chars {
        out.extend(c.to_lowercase());
    }
    new_string(&out)
}

/// `swapcase`: uppercase characters become lowercase and vice versa.
#[no_mangle]
pub extern "C" fn rt_string_swapcase(string: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        if c.is_uppercase() {
            out.extend(c.to_lowercase());
        } else {
            out.extend(c.to_uppercase());
        }
    }
    new_string(&out)
}

/// `title` / `titlecase`: uppercase the first character of each word.
///
/// A word boundary is whitespace OR ASCII punctuation, exactly as the
/// interpreter's arm defines it -- not Unicode punctuation, so `"a-b"` titles
/// to `"A-B"` while `"a\u{2010}b"` (non-ASCII hyphen) titles to `"A\u{2010}b"`.
#[no_mangle]
pub extern "C" fn rt_string_title(string: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let mut out = String::with_capacity(s.len());
    let mut capitalize_next = true;
    for c in s.chars() {
        if c.is_whitespace() || c.is_ascii_punctuation() {
            out.push(c);
            capitalize_next = true;
        } else if capitalize_next {
            out.extend(c.to_uppercase());
            capitalize_next = false;
        } else {
            out.extend(c.to_lowercase());
        }
    }
    new_string(&out)
}

/// `chomp`: strip ONE trailing line terminator -- `\r\n`, `\n`, or `\r`.
#[no_mangle]
pub extern "C" fn rt_string_chomp(string: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let out = s
        .strip_suffix("\r\n")
        .or_else(|| s.strip_suffix('\n'))
        .or_else(|| s.strip_suffix('\r'))
        .unwrap_or(s);
    new_string(out)
}

/// `trim_start_matches`: repeatedly strip `pattern` from the front.
#[no_mangle]
pub extern "C" fn rt_string_trim_start_matches(string: RuntimeValue, pattern: RuntimeValue) -> RuntimeValue {
    let (Some(s), Some(p)) = (string_as_str(string), string_as_str(pattern)) else {
        return string;
    };
    new_string(s.trim_start_matches(p))
}

/// `trim_end_matches`: repeatedly strip `pattern` from the end.
#[no_mangle]
pub extern "C" fn rt_string_trim_end_matches(string: RuntimeValue, pattern: RuntimeValue) -> RuntimeValue {
    let (Some(s), Some(p)) = (string_as_str(string), string_as_str(pattern)) else {
        return string;
    };
    new_string(s.trim_end_matches(p))
}

/// `removeprefix` / `remove_prefix`: strip `prefix` ONCE if present.
#[no_mangle]
pub extern "C" fn rt_string_remove_prefix(string: RuntimeValue, prefix: RuntimeValue) -> RuntimeValue {
    let (Some(s), Some(p)) = (string_as_str(string), string_as_str(prefix)) else {
        return string;
    };
    match s.strip_prefix(p) {
        Some(rest) => new_string(rest),
        None => string,
    }
}

/// `removesuffix` / `remove_suffix`: strip `suffix` ONCE if present.
#[no_mangle]
pub extern "C" fn rt_string_remove_suffix(string: RuntimeValue, suffix: RuntimeValue) -> RuntimeValue {
    let (Some(s), Some(p)) = (string_as_str(string), string_as_str(suffix)) else {
        return string;
    };
    match s.strip_suffix(p) {
        Some(rest) => new_string(rest),
        None => string,
    }
}

/// `squeeze`: collapse runs of the same adjacent character.
///
/// The optional argument restricts the collapse to characters in that set. The
/// dispatch site pads a missing argument with tagged nil (bit pattern 3), which
/// is not a heap string, so `string_as_str` yields `None` -- that is exactly the
/// "no argument, squeeze everything" case. A caller who passes an explicit
/// empty string gets `Some("")`, which squeezes nothing, matching the
/// interpreter's `set.contains(c)` against an empty set.
#[no_mangle]
pub extern "C" fn rt_string_squeeze(string: RuntimeValue, set: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    if s.is_empty() {
        return new_string("");
    }
    let set = string_as_str(set);
    let mut out = String::with_capacity(s.len());
    let mut prev: Option<char> = None;
    for c in s.chars() {
        let squeezable = match set {
            Some(set) => set.contains(c),
            None => true,
        };
        if !squeezable || Some(c) != prev {
            out.push(c);
        }
        prev = Some(c);
    }
    new_string(&out)
}

/// `replace_first`: replace only the FIRST occurrence of `pattern`.
#[no_mangle]
pub extern "C" fn rt_string_replace_first(
    string: RuntimeValue,
    pattern: RuntimeValue,
    replacement: RuntimeValue,
) -> RuntimeValue {
    let (Some(s), Some(p), Some(r)) = (
        string_as_str(string),
        string_as_str(pattern),
        string_as_str(replacement),
    ) else {
        return string;
    };
    new_string(&s.replacen(p, r, 1))
}

/// The character a pad-family method should use when the caller omitted the
/// optional pad argument.
///
/// `adapt_args_to_signature` pads a missing argument with tagged nil (bit
/// pattern 3), which is not a heap string, so `string_as_str` yields `None`.
/// That is unambiguous here because the parameter is a TEXT slot -- unlike an
/// INT slot, where tagged nil and the integer 3 are the same 64 bits.
///
/// A supplied argument contributes its FIRST character, matching the
/// interpreter's `.chars().next().unwrap_or(' ')`.
fn pad_char_or_space(pad: RuntimeValue) -> char {
    string_as_str(pad).and_then(|s| s.chars().next()).unwrap_or(' ')
}

/// `pad_left` / `pad_start`: left-pad to `width` CHARACTERS.
///
/// Width is a character count, not a byte count, matching the interpreter's
/// `s.chars().count()`. A width at or below the current length returns the
/// receiver unchanged, so a negative width is a no-op rather than a panic --
/// the interpreter reached this through `eval_arg_usize`, which used to cast
/// `-5` to `18446744073709551611` and PANIC with "capacity overflow".
#[no_mangle]
pub extern "C" fn rt_string_pad_left(string: RuntimeValue, width: i64, pad: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let current = s.chars().count() as i64;
    if width <= current {
        return string;
    }
    let c = pad_char_or_space(pad);
    let mut out = String::new();
    for _ in 0..(width - current) {
        out.push(c);
    }
    out.push_str(s);
    new_string(&out)
}

/// `pad_right` / `pad_end`: right-pad to `width` CHARACTERS.
#[no_mangle]
pub extern "C" fn rt_string_pad_right(string: RuntimeValue, width: i64, pad: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let current = s.chars().count() as i64;
    if width <= current {
        return string;
    }
    let c = pad_char_or_space(pad);
    let mut out = String::from(s);
    for _ in 0..(width - current) {
        out.push(c);
    }
    new_string(&out)
}

/// `center`: pad both sides to `width` CHARACTERS, extra character on the RIGHT.
#[no_mangle]
pub extern "C" fn rt_string_center(string: RuntimeValue, width: i64, pad: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let current = s.chars().count() as i64;
    if width <= current {
        return string;
    }
    let total = width - current;
    let left = total / 2;
    let c = pad_char_or_space(pad);
    let mut out = String::new();
    for _ in 0..left {
        out.push(c);
    }
    out.push_str(s);
    for _ in 0..(total - left) {
        out.push(c);
    }
    new_string(&out)
}

/// `zfill`: left-pad with `0` to `width` CHARACTERS, keeping a leading sign in
/// front of the zeros (`"-7".zfill(4)` is `"-007"`, not `"00-7"`).
#[no_mangle]
pub extern "C" fn rt_string_zfill(string: RuntimeValue, width: i64) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let current = s.chars().count() as i64;
    if width <= current {
        return string;
    }
    let (sign, rest) = match s.as_bytes().first() {
        Some(b'+') | Some(b'-') => s.split_at(1),
        _ => ("", s),
    };
    let mut out = String::from(sign);
    for _ in 0..(width - current) {
        out.push('0');
    }
    out.push_str(rest);
    new_string(&out)
}

/// `find_all` / `find_indices`: BYTE offsets of every non-overlapping match.
///
/// Byte offsets, matching `find`/`index_of`/`rfind` in both engines. An empty
/// needle yields an empty array rather than an offset per position, matching the
/// interpreter's explicit empty-needle guard.
#[no_mangle]
pub extern "C" fn rt_string_find_all(string: RuntimeValue, needle: RuntimeValue) -> RuntimeValue {
    let (Some(s), Some(n)) = (string_as_str(string), string_as_str(needle)) else {
        return rt_array_new(0);
    };
    if n.is_empty() {
        return rt_array_new(0);
    }
    let result = rt_array_new(0);
    for (idx, _) in s.match_indices(n) {
        rt_array_push(result, RuntimeValue::from_int(idx as i64));
    }
    result
}

/// `substr(start, length)`: CHARACTER-indexed substring by start and length.
///
/// Deliberately NOT `rt_slice`: that one is byte-indexed (and `slice`/
/// `substring` keep those semantics on purpose), while the interpreter's
/// `substr` walks `chars()`. Routing `substr` to `rt_slice` would have been a
/// silent JIT-vs-interpreter divergence on any multi-byte receiver.
///
/// Negative `start` or `length` clamps to 0, matching the saturating
/// `eval_arg_usize` the interpreter now uses.
#[no_mangle]
pub extern "C" fn rt_string_substr(string: RuntimeValue, start: i64, length: i64) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let start = start.max(0) as usize;
    let length = length.max(0) as usize;
    let out: String = s.chars().skip(start).take(length).collect();
    new_string(&out)
}

/// `substr(start)`: CHARACTER-indexed substring from `start` to the end.
///
/// A separate entry point rather than a default argument: the omitted-argument
/// slot is padded with tagged nil, whose bit pattern IS the integer 3, so an
/// integer parameter cannot tell "absent" from "3". The dispatch site therefore
/// selects between the two symbols on the argument count.
#[no_mangle]
pub extern "C" fn rt_string_substr_from(string: RuntimeValue, start: i64) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        return string;
    };
    let start = start.max(0) as usize;
    let out: String = s.chars().skip(start).collect();
    new_string(&out)
}

/// Refuse a non-text receiver LOUDLY.
///
/// The dispatch tables in `codegen/instr/{calls,closures_structs}.rs` are keyed
/// on the method NAME only -- they have no receiver type -- so a name shared
/// with an array or dict method reaches the text entry point with the wrong
/// receiver. Returning a plausible-looking value there is how this whole bug
/// started: it trades a loud failure for a silent wrong answer. These names had
/// no compiled implementation at all before, so exiting here is exactly as loud
/// as the behaviour it replaces, and never quieter.
fn refuse_non_text_receiver(method: &str) -> ! {
    eprintln!(
        "Runtime error: str.{method} was called on a receiver that is not text. \
         This method has no compiled implementation for that receiver type -- a \
         code-generation dispatch gap, not a program error. Refusing to \
         substitute a value."
    );
    std::process::exit(70);
}

/// `rev` / `reversed`: reverse by CHARACTER for text, by ELEMENT for an array.
///
/// Receiver-dispatched, following the `rt_at`/`rt_array_at` precedent: the
/// dispatch table cannot tell the two receivers apart, so the runtime must.
///
/// `reverse` now routes here too, on every type-blind dispatch table. It used
/// to route to `rt_array_reverse`, which reverses IN PLACE and returns a
/// `bool`, for EVERY receiver including text — so text got the `false`
/// receiver-mismatch answer, and an array got its receiver MUTATED. The
/// interpreter is the spec and it mutates nothing: `interpreter_method/
/// collections.rs` `"rev" | "reverse"` copies then reverses
/// (`Value::array(new_arr)`), `interpreter_method/string.rs` `"rev" |
/// "reverse"` builds a new text, and the tuple arm builds a new tuple. This
/// function matches that: a NEW array (via `rt_array_reversed`), a NEW text, or
/// a loud refusal on any other receiver. `rt_array_reverse` keeps its in-place
/// semantics for callers that ask for it by name; nothing dispatches `reverse`
/// to it any more.
#[no_mangle]
pub extern "C" fn rt_reverse(receiver: RuntimeValue) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        return rt_array_reversed(receiver);
    }
    match string_as_str(receiver) {
        Some(s) => new_string(&s.chars().rev().collect::<String>()),
        None => refuse_non_text_receiver("rev"),
    }
}

/// `reverse`: the MUTATING spelling. Reverses an ARRAY in place and returns
/// that same array.
///
/// `reverse` and `rev`/`reversed` are NOT synonyms in this language, and that
/// is the whole reason this function exists separately from `rt_reverse`.
/// `interpreter_method/mod.rs` lists `"reverse"` in `MUTATING_METHODS` and
/// deliberately does NOT list `"rev"` or `"reversed"`, so the interpreter
/// writes the result back to the receiver binding for `reverse` only. The two
/// spellings share one arm in `interpreter_method/collections.rs`, which is why
/// reading that arm alone makes them look identical — they are not. Measured:
///
/// ```text
/// var a = [1, 2, 3]
/// a.reverse()   # -> [3,2,1] AND a == [3,2,1]   (mutating spelling)
/// a.rev()       # -> [3,2,1] AND a == [1,2,3]   (pure spelling)
/// ```
///
/// Routing `reverse` to the copying `rt_reverse` therefore left the receiver
/// unmodified under JIT/native while the interpreter rebound it — a silent
/// wrong answer on the aliasing axis. `rt_reverse` itself is CORRECT; it is
/// the `rev`/`reversed` helper and keeps every one of its guarantees.
///
/// TEXT is passed through to the copying behaviour unchanged. The interpreter
/// currently also rebinds a text receiver here, but that contradicts its own
/// documented rule that "strings in Simple are value types with NO mutating
/// methods" (`interpreter_method/mod.rs`), and the same rebinding affects
/// string `push`/`pop`/`clear` too. That is a separate, larger defect recorded
/// in the bug tracker rather than decided here — this change deliberately
/// leaves text behaviour byte-for-byte as it was.
#[no_mangle]
pub extern "C" fn rt_reverse_mut(receiver: RuntimeValue) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        rt_array_reverse(receiver);
        return receiver;
    }
    match string_as_str(receiver) {
        Some(s) => new_string(&s.chars().rev().collect::<String>()),
        None => refuse_non_text_receiver("reverse"),
    }
}

/// A receiver `sort` has no compiled implementation for. Loud, never a value.
///
/// Distinct from `refuse_non_text_receiver` because `sort` is the opposite
/// shape: text is the INVALID receiver here, not the valid one.
fn refuse_non_array_sort_receiver() -> ! {
    eprintln!(
        "Runtime error: sort() was called on a receiver that is not an array. \
         The interpreter refuses this outright (\"method `sort` not found on \
         type `str`\"), so there is no correct value to return. Refusing to \
         substitute one."
    );
    std::process::exit(70);
}

/// `sort`: sort an ARRAY in place and return that same array.
///
/// The interpreter is the spec, and the spec is NOT what reading
/// `interpreter_method/collections.rs` alone suggests. That arm builds a copy
/// (`arr.to_vec()` -> `Value::array(new_arr)`), but `interpreter_method/mod.rs`
/// then WRITES THE RESULT BACK to the receiver binding, because `"sort"` is in
/// its `MUTATING_METHODS` list. Measured end to end on the interpreter:
///
/// ```text
/// var a = [3, 1, 2]
/// val b = a.sort()     // b = [1, 2, 3]  AND  a = [1, 2, 3]
/// "cba".sort()         // error: method `sort` not found on type `str`  (rc=1)
/// ```
///
/// So `sort` must (a) leave the receiver sorted and (b) evaluate to the sorted
/// array, and (c) refuse a text receiver rather than inventing an answer.
/// Returning a fresh copy and leaving the receiver alone would satisfy only
/// (b) — a silent wrong answer on the aliasing axis.
///
/// What was actually broken about `"sort" => rt_array_sort`:
///   * `rt_array_sort` returns a `bool`, not a collection, so the value was
///     only correct while `sort` sat in the codegen `in_place` set that
///     substitutes the receiver vreg.
///   * On a TEXT receiver it returned `false` and the `in_place` substitution
///     handed back the unsorted receiver — silently, where the interpreter
///     errors.
///   * `runtime_native.c` has never defined `rt_array_sort`, so `arr.sort()`
///     did not link at all on the native lane.
///
/// `rt_sort` fixes all three and returns the right value on its own, which is
/// why `sort` is also removed from the `in_place` set: with `rt_sort` the
/// substitution would defeat the text refusal.
#[no_mangle]
pub extern "C" fn rt_sort(receiver: RuntimeValue) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        rt_array_sort(receiver);
        return receiver;
    }
    refuse_non_array_sort_receiver()
}

/// `push`: append to an ARRAY in place, or build a NEW text.
///
/// Receiver-dispatched, same shape as `rt_reverse_mut` / `rt_sort` / `rt_at`.
/// The type-blind dispatch tables used to send every `push` to
/// `rt_array_push`, which `as_typed_ptr!`-fails closed on a text receiver and
/// returns `false` — so `var t = "abc"; t.push("d")` evaluated to `0` on the
/// compiled lane while the interpreter answered `"abcd"`. Measured before this
/// helper existed (JIT / interpreter): `0` / `"abcd"`.
///
/// TEXT IS A VALUE TYPE, so the text branch returns a new text and never
/// touches the receiver — the rule `interpreter_method/mod.rs` states and that
/// `interpreter_method/string.rs`'s own `push` arm has always implemented
/// ("Returns a new string with the character appended (strings are
/// immutable)"). The array branch keeps the measured array contract exactly:
/// the receiver is mutated AND the expression evaluates to that same array.
///
/// The concatenation goes through `rt_string_concat` so a non-text argument is
/// rendered exactly as `push_str` already renders it (`push_str` has always
/// dispatched to `rt_string_concat`).
#[no_mangle]
pub extern "C" fn rt_push(receiver: RuntimeValue, value: RuntimeValue) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        rt_array_push(receiver, value);
        return receiver;
    }
    if string_as_str(receiver).is_some() {
        return rt_string_concat(receiver, value);
    }
    refuse_non_text_receiver("push")
}

/// `pop`: remove and return the last ELEMENT of an array, or return the last
/// CHARACTER of a text without modifying it.
///
/// Receiver-dispatched. `rt_array_pop` fails closed to nil on a text receiver,
/// so `var t = "abc"; t.pop()` evaluated to `nil` on the compiled lane while
/// the interpreter answered `Option::Some("c")` — two different wrong answers
/// (measured JIT / interpreter: `nil` / `Option::Some(c)`).
///
/// The return shape is the ELEMENT, not an `Option`: measured on BOTH engines,
/// `[1, 2, 3].pop()` evaluates to `3`, never `Some(3)`. Text was the only
/// `pop` in the language that wrapped, and that wrapping was unreachable from
/// any compiled lane (the JIT has no Option constructor for text). The
/// interpreter's text arm now returns the bare character too.
///
/// An empty text has no last character and yields the empty text. That is
/// unambiguous — no real character is ever the empty text — and it mirrors
/// popping an empty array, which is a no-op on both engines.
#[no_mangle]
pub extern "C" fn rt_pop(receiver: RuntimeValue) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        return rt_array_pop(receiver);
    }
    match string_as_str(receiver) {
        Some(s) => match s.chars().last() {
            Some(c) => new_string(&c.to_string()),
            None => new_string(""),
        },
        None => refuse_non_text_receiver("pop"),
    }
}

/// `clear`: empty an ARRAY in place, or return the empty text.
///
/// Receiver-dispatched. `rt_array_clear` fails closed to `false` on a text
/// receiver, and `clear` also sat in the LLVM `in_place` set that substitutes
/// the receiver vreg for the call result — so `var t = "abc"; t.clear()`
/// handed back the UNCLEARED receiver `"abc"` (measured on the JIT), which is
/// the worst shape available: a plausible value that is silently wrong.
///
/// TEXT IS A VALUE TYPE: the text branch returns the empty text and leaves the
/// receiver alone, exactly as `interpreter_method/string.rs`'s `clear` arm
/// already documented ("Returns empty string (strings are immutable)"). The
/// array branch keeps the measured array contract: receiver emptied AND the
/// expression evaluates to that same (now empty) array.
#[no_mangle]
pub extern "C" fn rt_clear(receiver: RuntimeValue) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        rt_array_clear(receiver);
        return receiver;
    }
    if string_as_str(receiver).is_some() {
        return new_string("");
    }
    refuse_non_text_receiver("clear")
}

/// `take` / `taken`: first `n` CHARACTERS of text, or first `n` ELEMENTS of an
/// array. Receiver-dispatched. A negative `n` yields an empty result, matching
/// the saturating `eval_arg_usize` the interpreter now uses.
#[no_mangle]
pub extern "C" fn rt_take(receiver: RuntimeValue, n: i64) -> RuntimeValue {
    let n = n.max(0);
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        let len = rt_array_len(receiver);
        let take = n.min(len.max(0));
        let out = rt_array_new(take.max(0) as u64);
        for i in 0..take {
            rt_array_push(out, rt_array_get(receiver, i));
        }
        return out;
    }
    match string_as_str(receiver) {
        Some(s) => new_string(&s.chars().take(n as usize).collect::<String>()),
        None => refuse_non_text_receiver("take"),
    }
}

/// `drop` / `dropped` / `skip`: all but the first `n` CHARACTERS of text, or all
/// but the first `n` ELEMENTS of an array. Receiver-dispatched.
#[no_mangle]
pub extern "C" fn rt_drop(receiver: RuntimeValue, n: i64) -> RuntimeValue {
    let n = n.max(0);
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        let len = rt_array_len(receiver).max(0);
        let start = n.min(len);
        let out = rt_array_new((len - start).max(0) as u64);
        for i in start..len {
            rt_array_push(out, rt_array_get(receiver, i));
        }
        return out;
    }
    match string_as_str(receiver) {
        Some(s) => new_string(&s.chars().skip(n as usize).collect::<String>()),
        None => refuse_non_text_receiver("drop"),
    }
}

/// `sorted` on TEXT: the receiver's characters in codepoint order.
///
/// TEXT ONLY, on purpose. `sorted` is also an array method, but ordering an
/// array means ordering tag-boxed values of mixed type, and the C runtime has no
/// such comparator (nor an `rt_array_sorted`). Implementing it in the Rust
/// runtime alone would make the two lanes disagree on `arr.sorted()`; declining
/// loudly keeps them identical and leaves array `sorted` exactly as unwired as
/// it is today.
#[no_mangle]
pub extern "C" fn rt_string_sorted(string: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        refuse_non_text_receiver("sorted");
    };
    let mut chars: Vec<char> = s.chars().collect();
    chars.sort_unstable();
    new_string(&chars.into_iter().collect::<String>())
}

/// Shared body for `partition` / `rpartition`: `[before, separator, after]`.
///
/// An empty separator, or a separator that does not occur, yields the receiver
/// in ONE of the three slots and two empty strings -- first slot for
/// `partition`, LAST slot for `rpartition`, matching the interpreter arms.
fn string_partition_at(s: &str, sep: &str, from_end: bool) -> RuntimeValue {
    let hit = if sep.is_empty() {
        None
    } else if from_end {
        s.rfind(sep)
    } else {
        s.find(sep)
    };
    let out = rt_array_new(3);
    match hit {
        Some(idx) => {
            rt_array_push(out, new_string(&s[..idx]));
            rt_array_push(out, new_string(sep));
            rt_array_push(out, new_string(&s[idx + sep.len()..]));
        }
        None if from_end => {
            rt_array_push(out, new_string(""));
            rt_array_push(out, new_string(""));
            rt_array_push(out, new_string(s));
        }
        None => {
            rt_array_push(out, new_string(s));
            rt_array_push(out, new_string(""));
            rt_array_push(out, new_string(""));
        }
    }
    out
}

/// `partition`: split at the FIRST occurrence into `[before, sep, after]`.
///
/// TEXT ONLY. `partition` is also an array method, but the array form takes a
/// PREDICATE and returns `[passing, failing]` -- a different arity, a different
/// argument type and a different result shape. Guessing between them from a
/// tagged value would be a silent wrong answer; the array form additionally
/// needs to invoke a closure, which this runtime cannot do from here.
#[no_mangle]
pub extern "C" fn rt_string_partition(string: RuntimeValue, sep: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        refuse_non_text_receiver("partition");
    };
    let sep = string_as_str(sep).unwrap_or("");
    string_partition_at(s, sep, false)
}

/// `rpartition`: split at the LAST occurrence into `[before, sep, after]`.
#[no_mangle]
pub extern "C" fn rt_string_rpartition(string: RuntimeValue, sep: RuntimeValue) -> RuntimeValue {
    let Some(s) = string_as_str(string) else {
        refuse_non_text_receiver("rpartition");
    };
    let sep = string_as_str(sep).unwrap_or("");
    string_partition_at(s, sep, true)
}

/// Check if string starts with prefix
/// Returns 1 if true, 0 if false
#[no_mangle]
pub extern "C" fn rt_string_starts_with(string: RuntimeValue, prefix: RuntimeValue) -> i64 {
    let str_len = rt_string_len(string);
    let prefix_len = rt_string_len(prefix);

    if str_len < 0 || prefix_len < 0 {
        return 0;
    }

    if prefix_len > str_len {
        return 0;
    }

    if prefix_len == 0 {
        return 1; // Empty prefix always matches
    }

    let str_data = rt_string_data(string);
    let prefix_data = rt_string_data(prefix);

    if str_data.is_null() || prefix_data.is_null() {
        return 0;
    }

    unsafe {
        let str_slice = std::slice::from_raw_parts(str_data, prefix_len as usize);
        let prefix_slice = std::slice::from_raw_parts(prefix_data, prefix_len as usize);
        if str_slice == prefix_slice {
            1
        } else {
            0
        }
    }
}

/// Check if string ends with suffix
/// Returns 1 if true, 0 if false
#[no_mangle]
pub extern "C" fn rt_string_ends_with(string: RuntimeValue, suffix: RuntimeValue) -> i64 {
    let str_len = rt_string_len(string);
    let suffix_len = rt_string_len(suffix);

    if str_len < 0 || suffix_len < 0 {
        return 0;
    }

    if suffix_len > str_len {
        return 0;
    }

    if suffix_len == 0 {
        return 1; // Empty suffix always matches
    }

    let str_data = rt_string_data(string);
    let suffix_data = rt_string_data(suffix);

    if str_data.is_null() || suffix_data.is_null() {
        return 0;
    }

    unsafe {
        let start_offset = (str_len - suffix_len) as usize;
        let str_slice = std::slice::from_raw_parts(str_data.add(start_offset), suffix_len as usize);
        let suffix_slice = std::slice::from_raw_parts(suffix_data, suffix_len as usize);
        if str_slice == suffix_slice {
            1
        } else {
            0
        }
    }
}

/// Check if two strings are equal
/// Returns 1 if true, 0 if false
#[no_mangle]
pub extern "C" fn rt_string_eq(string1: RuntimeValue, string2: RuntimeValue) -> i64 {
    let len1 = rt_string_len(string1);
    let len2 = rt_string_len(string2);

    if len1 < 0 || len2 < 0 {
        return 0;
    }

    if len1 != len2 {
        return 0;
    }

    if len1 == 0 {
        return 1; // Both empty strings are equal
    }

    let data1 = rt_string_data(string1);
    let data2 = rt_string_data(string2);

    if data1.is_null() || data2.is_null() {
        return 0;
    }

    unsafe {
        let slice1 = std::slice::from_raw_parts(data1, len1 as usize);
        let slice2 = std::slice::from_raw_parts(data2, len2 as usize);
        if slice1 == slice2 {
            1
        } else {
            0
        }
    }
}

/// P0 fix (2026-07-22): lexicographic (byte-wise) ordering comparison for two
/// strings. Backs native `<`/`<=`/`>`/`>=` on text operands -- mirrors
/// rt_string_eq just above (which backs `==`/`!=` for the same
/// codegen/instr/core.rs vreg_is_text fast path). Returns a strcmp-style
/// signed result: <0 if string1 < string2, 0 if equal, >0 if string1 >
/// string2 (shorter-common-prefix sorts first, matching runtime_native.c's
/// C-side rt_text_cmp_any used by the self-hosted .spl MIR lowering path --
/// see doc/08_tracking/bug/sspec_test_path_false_green_undercount_2026-07-20.md).
/// Before this fix, `<`/`>` on text fell through to a raw pointer/handle
/// `icmp`, comparing heap ADDRESSES instead of content.
#[no_mangle]
pub extern "C" fn rt_text_cmp_any(string1: RuntimeValue, string2: RuntimeValue) -> i64 {
    let len1 = rt_string_len(string1);
    let len2 = rt_string_len(string2);

    if len1 <= 0 && len2 <= 0 {
        return 0;
    }
    if len1 <= 0 {
        return -1;
    }
    if len2 <= 0 {
        return 1;
    }

    let data1 = rt_string_data(string1);
    let data2 = rt_string_data(string2);

    if data1.is_null() && data2.is_null() {
        return 0;
    }
    if data1.is_null() {
        return -1;
    }
    if data2.is_null() {
        return 1;
    }

    unsafe {
        let slice1 = std::slice::from_raw_parts(data1, len1 as usize);
        let slice2 = std::slice::from_raw_parts(data2, len2 as usize);
        match slice1.cmp(slice2) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        }
    }
}

/// Get a single character from a string at the given index.
/// Returns the character as a new single-character string (RuntimeValue).
/// Returns nil (TAG_SPECIAL 3) if index is out of bounds.
#[no_mangle]
pub extern "C" fn rt_string_char_at(string: RuntimeValue, index: i64) -> RuntimeValue {
    let len = rt_string_len(string);
    if len < 0 {
        // Receiver is not a text value at all — that stays NIL.
        return RuntimeValue::NIL;
    }
    if index >= len {
        // `index >= len` is a permissive fast reject: the byte length
        // upper-bounds the character count, and chars().nth enforces the
        // real character bound below.
        //
        // Forward over-run returns EMPTY TEXT, not NIL. The tree-walk
        // interpreter (interpreter_method/string.rs `"char_at" | "at"`)
        // returns `""` here, so the pervasive loop-termination idiom
        // `if ch == "": break` was FAIL-OPEN on the compiled path only —
        // `nil == ""` is false, so the guard never fired and the loop ran
        // past the end. Divergence measured 2026-08-06:
        // `"Café".char_at(99) == ""` was false on JIT, true on interpret.
        // See doc/08_tracking/bug/text_byte_len_vs_codepoint_index_family_2026-08-06.md.
        return new_string("");
    }

    let data = rt_string_data(string);
    if data.is_null() {
        return RuntimeValue::NIL;
    }

    unsafe {
        let bytes = std::slice::from_raw_parts(data, len as usize);
        // Find the character at the given index (UTF-8 aware)
        let s = std::str::from_utf8_unchecked(bytes);
        // Negative index counts from the end in CHARACTERS (Python-style),
        // matching the tree-walking interpreter and the documented
        // negative-indexing family rule. Previously any negative index
        // returned NIL, so `v[-2]` was nil under the default engine while
        // the interpreter returned the character.
        let idx = if index < 0 {
            let adjusted = s.chars().count() as i64 + index;
            if adjusted < 0 {
                return RuntimeValue::NIL;
            }
            adjusted as usize
        } else {
            index as usize
        };
        if let Some(c) = s.chars().nth(idx) {
            let mut buf = [0u8; 4];
            let char_str = c.encode_utf8(&mut buf);
            rt_string_new(char_str.as_ptr(), char_str.len() as u64)
        } else {
            // Real CHARACTER-bound over-run (index passed the byte-length fast
            // reject above but is >= the codepoint count — the common case for
            // non-ASCII text, e.g. `"Café".char_at(4)`, 5 bytes / 4 chars).
            // Same contract as the fast reject: empty text, not NIL, so
            // `if ch == "": break` terminates on the compiled path too.
            // A negative index cannot reach here: `adjusted >= 0` implies
            // `adjusted < chars().count()`.
            new_string("")
        }
    }
}

/// Byte offset of the first byte >= 0x80, or `bytes.len()` when all-ASCII.
/// Word-at-a-time so an all-ASCII document costs ~len/8 iterations.
fn first_non_ascii(bytes: &[u8]) -> usize {
    let mut i = 0usize;
    while i + 8 <= bytes.len() {
        let w = u64::from_ne_bytes(bytes[i..i + 8].try_into().unwrap());
        if w & 0x8080_8080_8080_8080 != 0 {
            break;
        }
        i += 8;
    }
    while i < bytes.len() && bytes[i] < 0x80 {
        i += 1;
    }
    i
}

/// Return the Unicode code point at the given character index, or 0 if missing.
///
/// SEMANTICS ARE UNCHANGED: `index` is a CHARACTER (codepoint) index, and the
/// `index >= len` bound still uses the BYTE length exactly as before. Only the
/// cost changed.
///
/// The old body was `s.chars().nth(index)` -- a codepoint walk from byte 0 on
/// every call, i.e. O(index). That made every `while i < s.len(): char_code_at(i)`
/// loop in the codebase O(n^2); the web renderer's hand-rolled `find_from` /
/// `text_matches_at` scanners rest entirely on this primitive.
///
/// Within an ASCII prefix a character index IS a byte index, so we answer
/// directly out of the buffer:
///   - flag cached          -> O(1) direct byte read
///   - whole string ASCII   -> cache the flag, O(1) read
///   - `index` inside prefix-> O(1) read
///   - otherwise            -> the exact original codepoint walk
///
/// The fallback never costs more than the old code did, so no input regresses.
/// The cached flag is sound because Simple strings are immutable and the flag is
/// positive-only (set => proven ASCII, unset => unknown), so a missed cache costs
/// a rescan, never a wrong answer.
#[no_mangle]
pub extern "C" fn rt_string_char_code_at(string: RuntimeValue, index: i64) -> i64 {
    let len = rt_string_len(string);
    if len < 0 || index < 0 || index >= len {
        return 0;
    }

    let data = rt_string_data(string);
    if data.is_null() {
        return 0;
    }

    unsafe {
        let bytes = std::slice::from_raw_parts(data, len as usize);
        let idx = index as usize;

        let hdr = string.as_heap_ptr();
        if !hdr.is_null() && (*hdr).reserved & RT_STRING_FLAG_ASCII != 0 {
            return bytes[idx] as i64;
        }

        let first_hi = first_non_ascii(bytes);
        if first_hi == bytes.len() {
            // Whole string is ASCII: character index == byte index, permanently.
            if !hdr.is_null() {
                (*hdr).reserved |= RT_STRING_FLAG_ASCII;
            }
            return bytes[idx] as i64;
        }
        if first_hi > idx {
            // `index` lies strictly inside the ASCII prefix.
            return bytes[idx] as i64;
        }

        let s = std::str::from_utf8_unchecked(bytes);
        s.chars().nth(idx).map_or(0, |c| c as i64)
    }
}

/// Return the raw BYTE at the given BYTE index, or 0 if out of range.
///
/// Deliberately NOT `rt_string_char_code_at`: that one is CHARACTER-indexed
/// and the two disagree on any non-ASCII text (`"café,".byte_at(3)` is 195,
/// the 0xC3 lead byte, while `char_code_at(3)` is 233 for 'é'). Byte-framing
/// callers (e.g. the web renderer's `browser_renderer_protocol.spl` scanning
/// for byte 10 `\n` / 44 `,`) index the raw UTF-8 buffer directly, so a
/// character index would desync the frame at the first multi-byte codepoint.
/// O(1): straight buffer read, no codepoint walk needed.
#[no_mangle]
pub extern "C" fn rt_string_byte_at(string: RuntimeValue, index: i64) -> i64 {
    let len = rt_string_len(string);
    if len < 0 || index < 0 || index >= len {
        return 0;
    }

    let data = rt_string_data(string);
    if data.is_null() {
        return 0;
    }

    unsafe {
        let bytes = std::slice::from_raw_parts(data, len as usize);
        bytes[index as usize] as i64
    }
}

/// Compiled symbol for `text.from_char_code(code)`.
///
/// NOTE: currently dead code on main -- codegen for `.chr()` / `.to_char()`
/// routes to the pure-Simple side (see
/// doc/08_tracking/bug/char_from_code_non_ascii_unsupported_2026-07-20.md),
/// so this function is not reached by a normal build today. Fixed anyway
/// for class completeness in case it is ever brought back into service.
#[no_mangle]
pub extern "C" fn text_dot_from_char_code(code: i64) -> RuntimeValue {
    // `code as u32` truncates without this guard: a value like
    // 0x1_0000_0041 (outside i64's low 32 bits) would silently truncate to
    // 0x41 ('A') instead of being rejected, because the truncation happens
    // *before* char::from_u32 ever sees the value. Reject out-of-range
    // codepoints on the untruncated i64 first; char::from_u32 still handles
    // the UTF-16 surrogate range (U+D800..U+DFFF) rejection on its own.
    if !(0..=0x10FFFF).contains(&code) {
        return RuntimeValue::NIL;
    }
    let Some(ch) = char::from_u32(code as u32) else {
        return RuntimeValue::NIL;
    };
    let mut buf = [0u8; 4];
    let s = ch.encode_utf8(&mut buf);
    unsafe { rt_string_new(s.as_ptr(), s.len() as u64) }
}

#[no_mangle]
pub extern "C" fn rt_text_find(haystack: RuntimeValue, needle: RuntimeValue, start: i64) -> i64 {
    // Negative start clamps to 0 (the two-arg index_of contract; matches the
    // C native runtime and simple_core impls).
    let start = start.max(0);
    let hay_len = rt_string_len(haystack);
    let needle_len = rt_string_len(needle);
    if needle_len < 0 || hay_len < 0 {
        return -1;
    }
    if needle_len == 0 {
        return start.min(hay_len);
    }
    if start >= hay_len || needle_len > hay_len {
        return -1;
    }
    let hay_ptr = rt_string_data(haystack);
    let needle_ptr = rt_string_data(needle);
    if hay_ptr.is_null() || needle_ptr.is_null() {
        return -1;
    }

    unsafe {
        let hay = std::slice::from_raw_parts(hay_ptr, hay_len as usize);
        let needle_bytes = std::slice::from_raw_parts(needle_ptr, needle_len as usize);
        (collection_providers().byte_find)(hay, needle_bytes, start as usize)
            .map(|idx| idx as i64)
            .unwrap_or(-1)
    }
}

/// Create a string from a null-terminated C string
///
/// # Safety
/// The pointer must be a valid null-terminated C string (or null).
/// The string data must be valid UTF-8.
#[no_mangle]
pub unsafe extern "C" fn rt_cstring_to_text(cstr: *const std::os::raw::c_char) -> RuntimeValue {
    if cstr.is_null() {
        return rt_string_new(std::ptr::null(), 0);
    }

    // Calculate length using strlen
    let len = {
        let mut p = cstr;
        let mut count = 0u64;
        while *p != 0 {
            p = p.add(1);
            count += 1;
        }
        count
    };

    rt_string_new(cstr as *const u8, len)
}

/// Split a string by a delimiter, returning an array of strings
#[no_mangle]
pub extern "C" fn rt_string_split(string: RuntimeValue, delimiter: RuntimeValue) -> RuntimeValue {
    let str_len = rt_string_len(string);
    let del_len = rt_string_len(delimiter);
    if str_len < 0 || del_len < 0 {
        return rt_array_new(0);
    }

    let str_data = rt_string_data(string);
    let del_data = rt_string_data(delimiter);
    if str_data.is_null() || (del_len > 0 && del_data.is_null()) {
        return rt_array_new(0);
    }

    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(str_data, str_len as usize));
        let d = std::str::from_utf8_unchecked(std::slice::from_raw_parts(del_data, del_len as usize));
        let parts = (collection_providers().byte_split)(s, d);
        let result = rt_array_new(parts.len() as u64);
        for (start, end) in parts {
            let part = &s[start..end];
            let part_rv = rt_string_new(part.as_ptr(), part.len() as u64);
            rt_array_push(result, part_rv);
        }
        result
    }
}

/// Split a string at most `limit - 1` times, preserving the remainder.
#[no_mangle]
pub extern "C" fn rt_string_split_limit(
    string: RuntimeValue,
    delimiter: RuntimeValue,
    limit: i64,
) -> RuntimeValue {
    if limit <= 0 {
        return rt_string_split(string, delimiter);
    }
    let str_len = rt_string_len(string);
    let del_len = rt_string_len(delimiter);
    if str_len < 0 || del_len < 0 {
        return rt_array_new(0);
    }
    let str_data = rt_string_data(string);
    let del_data = rt_string_data(delimiter);
    if str_data.is_null() || (del_len > 0 && del_data.is_null()) {
        return rt_array_new(0);
    }
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(str_data, str_len as usize));
        let d = std::str::from_utf8_unchecked(std::slice::from_raw_parts(del_data, del_len as usize));
        let result = rt_array_new(limit.max(1) as u64);
        if limit == 1 {
            rt_array_push(result, string);
            return result;
        }
        if d.is_empty() {
            let mut start = 0usize;
            while start < s.len() && (start as i64) < limit - 1 {
                let end = start + 1;
                rt_array_push(result, rt_string_new(s[start..end].as_ptr(), 1));
                start = end;
            }
            rt_array_push(result, rt_string_new(s[start..].as_ptr(), (s.len() - start) as u64));
            return result;
        }
        let mut start = 0usize;
        let mut count = 1i64;
        while count < limit {
            let Some(relative) = s[start..].find(d) else { break };
            let end = start + relative;
            rt_array_push(result, rt_string_new(s[start..end].as_ptr(), (end - start) as u64));
            start = end + d.len();
            count += 1;
        }
        rt_array_push(result, rt_string_new(s[start..].as_ptr(), (s.len() - start) as u64));
        result
    }
}

/// Return the UTF-8 bytes of a string as an array of ints (one per byte).
/// Mirrors the interpreter's `text.bytes()` (`interpreter_method/string.rs`)
/// so JIT/native code can call `.bytes()` instead of only the interpreter.
#[no_mangle]
pub extern "C" fn rt_string_bytes(string: RuntimeValue) -> RuntimeValue {
    let str_len = rt_string_len(string);
    if str_len <= 0 {
        return rt_array_new(0);
    }
    let str_data = rt_string_data(string);
    if str_data.is_null() {
        return rt_array_new(0);
    }
    unsafe {
        let bytes = std::slice::from_raw_parts(str_data, str_len as usize);
        let result = rt_array_new(bytes.len() as u64);
        for &b in bytes {
            rt_array_push(result, RuntimeValue::from_int(b as i64));
        }
        result
    }
}

/// Split a string into lines, returning an array of strings.
///
/// Mirrors the interpreter's `text.lines()` / `text.split_lines()`
/// (`interpreter_method/string.rs`, which delegates to Rust's `str::lines`) so
/// JIT/native code can call `.lines()` instead of only the interpreter. Before
/// this existed the method had NO codegen mapping at all and every compiled
/// call died with `Runtime error: Function 'str.lines' not found`, after which
/// `.len()` on the nil result yielded `-1`.
///
/// `str::lines` semantics, which this deliberately inherits: a final trailing
/// newline does NOT produce a trailing empty line (`"a\n"` -> 1), the empty
/// string yields 0 lines, and a `\r\n` terminator has its `\r` stripped.
#[no_mangle]
pub extern "C" fn rt_string_lines(string: RuntimeValue) -> RuntimeValue {
    let str_len = rt_string_len(string);
    if str_len <= 0 {
        return rt_array_new(0);
    }
    let str_data = rt_string_data(string);
    if str_data.is_null() {
        return rt_array_new(0);
    }
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(str_data, str_len as usize));
        let result = rt_array_new(0);
        for line in s.lines() {
            let line_rv = rt_string_new(line.as_ptr(), line.len() as u64);
            rt_array_push(result, line_rv);
        }
        result
    }
}

/// Return the characters of a string as an array of single-character strings.
/// Mirrors the interpreter's `text.chars()` (`interpreter_method/string.rs`).
#[no_mangle]
pub extern "C" fn rt_string_chars(string: RuntimeValue) -> RuntimeValue {
    let str_len = rt_string_len(string);
    if str_len <= 0 {
        return rt_array_new(0);
    }
    let str_data = rt_string_data(string);
    if str_data.is_null() {
        return rt_array_new(0);
    }
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(str_data, str_len as usize));
        let result = rt_array_new(s.chars().count() as u64);
        for c in s.chars() {
            let mut buf = [0u8; 4];
            let cs = c.encode_utf8(&mut buf);
            rt_array_push(result, rt_string_new(cs.as_ptr(), cs.len() as u64));
        }
        result
    }
}

/// Replace all occurrences of a pattern in a string
#[no_mangle]
pub extern "C" fn rt_string_replace(
    string: RuntimeValue,
    pattern: RuntimeValue,
    replacement: RuntimeValue,
) -> RuntimeValue {
    let str_len = rt_string_len(string);
    let pat_len = rt_string_len(pattern);
    let rep_len = rt_string_len(replacement);
    if str_len < 0 || pat_len < 0 || rep_len < 0 {
        return string;
    }

    let str_data = rt_string_data(string);
    let pat_data = rt_string_data(pattern);
    let rep_data = rt_string_data(replacement);

    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(str_data, str_len as usize));
        let p = std::str::from_utf8_unchecked(std::slice::from_raw_parts(pat_data, pat_len as usize));
        let r = std::str::from_utf8_unchecked(std::slice::from_raw_parts(rep_data, rep_len as usize));
        let result = s.replace(p, r);
        rt_string_new(result.as_ptr(), result.len() as u64)
    }
}

/// Repeat a string `count` times.
///
/// Mirrors the tree-walking interpreter (`interpreter_method/string.rs`, arm
/// `"repeat"`) and the pure-Simple `str_repeat` in
/// `src/lib/common/string_core.spl`: a non-positive `count` yields the empty
/// string.
///
/// This function had no definition in EITHER runtime, so the Cranelift JIT's
/// method table had nothing to route `.repeat()` to. `" ".repeat(n)` therefore
/// raised `Function 'str.repeat' not found` and substituted the SPECIAL_ERROR
/// sentinel, which stringifies as `error` -- silently corrupting every
/// indentation string built that way (notably EasyFix replacement text).
#[no_mangle]
pub extern "C" fn rt_string_repeat(string: RuntimeValue, count: i64) -> RuntimeValue {
    let str_len = rt_string_len(string);
    if str_len < 0 {
        // Not a text receiver: preserve the value rather than fabricating one.
        return string;
    }
    if count <= 0 || str_len == 0 {
        return rt_string_new(b"".as_ptr(), 0);
    }
    if count == 1 {
        return string;
    }

    let data = rt_string_data(string);
    if data.is_null() {
        return rt_string_new(b"".as_ptr(), 0);
    }

    // Refuse an allocation that cannot be expressed, instead of wrapping and
    // returning a short string that would silently truncate caller output.
    let total = match (str_len as u64).checked_mul(count as u64) {
        Some(total) if total <= isize::MAX as u64 => total as usize,
        _ => {
            eprintln!("Runtime error: str.repeat overflow (len={str_len}, count={count})");
            std::process::exit(70);
        }
    };

    unsafe {
        let bytes = std::slice::from_raw_parts(data, str_len as usize);
        let mut out = Vec::with_capacity(total);
        for _ in 0..count {
            out.extend_from_slice(bytes);
        }
        rt_string_new(out.as_ptr(), out.len() as u64)
    }
}

/// Trim whitespace from both ends of a string
#[no_mangle]
pub extern "C" fn rt_string_trim(string: RuntimeValue) -> RuntimeValue {
    let len = rt_string_len(string);
    if len <= 0 {
        return string;
    }
    let data = rt_string_data(string);
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(data, len as usize));
        let trimmed = s.trim();
        rt_string_new(trimmed.as_ptr(), trimmed.len() as u64)
    }
}

/// Trim whitespace from the start of a string
#[no_mangle]
pub extern "C" fn rt_string_trim_start(string: RuntimeValue) -> RuntimeValue {
    let len = rt_string_len(string);
    if len <= 0 {
        return string;
    }
    let data = rt_string_data(string);
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(data, len as usize));
        let trimmed = s.trim_start();
        rt_string_new(trimmed.as_ptr(), trimmed.len() as u64)
    }
}

/// Trim whitespace from the end of a string
#[no_mangle]
pub extern "C" fn rt_string_trim_end(string: RuntimeValue) -> RuntimeValue {
    let len = rt_string_len(string);
    if len <= 0 {
        return string;
    }
    let data = rt_string_data(string);
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(data, len as usize));
        let trimmed = s.trim_end();
        rt_string_new(trimmed.as_ptr(), trimmed.len() as u64)
    }
}

/// Join an array of strings with a separator
/// Called as array.join(separator) so array is first arg
#[no_mangle]
pub extern "C" fn rt_string_join(array: RuntimeValue, separator: RuntimeValue) -> RuntimeValue {
    use super::sffi::rt_value_to_string;

    let arr_len = rt_array_len(array);
    if arr_len <= 0 {
        return rt_string_new(std::ptr::null(), 0);
    }

    let sep_len = rt_string_len(separator);
    let sep_data = rt_string_data(separator);

    let mut result = String::new();
    for i in 0..arr_len {
        if i > 0 && sep_len > 0 {
            unsafe {
                let sep = std::str::from_utf8_unchecked(std::slice::from_raw_parts(sep_data, sep_len as usize));
                result.push_str(sep);
            }
        }
        // Elements are not guaranteed to already be String RuntimeValues (they
        // may be tag-boxed ints/floats/bools/etc.). Render each element via
        // the same display formatter the print path uses (rt_value_to_string
        // wraps value_to_display_string) before reading it as UTF-8, so
        // `[1,2,3].join(",")` renders bare ints instead of empty strings.
        let elem = rt_array_get(array, i);
        let elem_str = rt_value_to_string(elem);
        let elem_len = rt_string_len(elem_str);
        if elem_len > 0 {
            let elem_data = rt_string_data(elem_str);
            unsafe {
                let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(elem_data, elem_len as usize));
                result.push_str(s);
            }
        }
    }
    rt_string_new(result.as_ptr(), result.len() as u64)
}

/// Convert a string to uppercase
#[no_mangle]
pub extern "C" fn rt_string_to_upper(string: RuntimeValue) -> RuntimeValue {
    let len = rt_string_len(string);
    if len <= 0 {
        return string;
    }
    let data = rt_string_data(string);
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(data, len as usize));
        let upper = s.to_uppercase();
        rt_string_new(upper.as_ptr(), upper.len() as u64)
    }
}

/// Convert a string to lowercase
#[no_mangle]
pub extern "C" fn rt_string_to_lower(string: RuntimeValue) -> RuntimeValue {
    let len = rt_string_len(string);
    if len <= 0 {
        return string;
    }
    let data = rt_string_data(string);
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(data, len as usize));
        let lower = s.to_lowercase();
        rt_string_new(lower.as_ptr(), lower.len() as u64)
    }
}

/// Convert a string to an integer, returns 0 on failure
#[no_mangle]
pub extern "C" fn rt_string_to_int(string: RuntimeValue) -> i64 {
    let len = rt_string_len(string);
    if len <= 0 {
        return 0;
    }
    let data = rt_string_data(string);
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(data, len as usize));
        s.trim().parse::<i64>().unwrap_or(0)
    }
}

/// Task #118 canonical `int(text)` semantics: a TOTAL, non-erroring,
/// leading-numeric-prefix parse — never fails. Skips leading whitespace, an
/// optional `+`/`-` sign, then reads the longest run of leading ASCII
/// decimal digits and stops at the first non-digit (so "4.2" -> 4,
/// truncating at '.'; "4x2" -> 4). Returns 0 if no digits are found at all
/// ("abc", ""). This mirrors the C runtime's strtoll-based
/// `rt_string_to_int()` (src/runtime/runtime_native.c and
/// src/runtime/simple_core/core_string.spl) — those two implementations
/// already had the correct lenient semantics; this Rust-native crate's
/// `rt_string_to_int` above is strict (whole-string `str::parse`) because it
/// backs `.to_int()`/`.parse_int()`/`to_i64()` method calls, which are meant
/// to reject partial matches. `int(text_expr)` / `int(x)` casts route through
/// this sibling function instead so the generic `int()` builtin agrees with
/// the flat-AST interpreter (`eval_int_parse_lenient` in eval_builtins.spl)
/// and the seed's tree-walk interpreter (`parse_int_lenient` in
/// interpreter_call/builtins.rs). See
/// doc/07_guide/quick_reference/syntax_quick_reference.md "int(text)
/// Semantics" for the full matrix.
#[no_mangle]
pub extern "C" fn rt_string_to_int_lenient(string: RuntimeValue) -> i64 {
    let len = rt_string_len(string);
    if len <= 0 {
        return 0;
    }
    let data = rt_string_data(string);
    let s = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(data, len as usize)) };
    let t = s.trim();
    let mut chars = t.chars().peekable();
    let mut negative = false;
    if let Some(&c) = chars.peek() {
        if c == '-' || c == '+' {
            negative = c == '-';
            chars.next();
        }
    }
    let mut result: i64 = 0;
    let mut any_digit = false;
    for c in chars {
        match c.to_digit(10) {
            Some(d) => {
                any_digit = true;
                result = result.saturating_mul(10).saturating_add(d as i64);
            }
            None => break,
        }
    }
    if !any_digit {
        return 0;
    }
    if negative {
        -result
    } else {
        result
    }
}

/// Convert a string to a float (f64), returns the float as RuntimeValue.
/// Returns the float RuntimeValue on success, RuntimeValue::NIL on failure.
/// Callers can check `result != nil` to distinguish success from failure.
#[no_mangle]
pub extern "C" fn rt_string_to_float(string: RuntimeValue) -> RuntimeValue {
    let len = rt_string_len(string);
    if len <= 0 {
        return RuntimeValue::NIL;
    }
    let data = rt_string_data(string);
    unsafe {
        let s = std::str::from_utf8_unchecked(std::slice::from_raw_parts(data, len as usize));
        match s.trim().parse::<f64>() {
            Ok(f) => RuntimeValue::from_float(f),
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Find first occurrence of needle in string
/// Returns the byte index, or -1 if not found
#[no_mangle]
pub extern "C" fn rt_string_find(string: RuntimeValue, needle: RuntimeValue) -> i64 {
    let str_len = rt_string_len(string);
    let needle_len = rt_string_len(needle);

    if str_len < 0 || needle_len < 0 {
        return -1;
    }

    if needle_len == 0 {
        return 0;
    }

    if needle_len > str_len {
        return -1;
    }

    let str_data = rt_string_data(string);
    let needle_data = rt_string_data(needle);

    if str_data.is_null() || needle_data.is_null() {
        return -1;
    }

    unsafe {
        let haystack = std::slice::from_raw_parts(str_data, str_len as usize);
        let needle_bytes = std::slice::from_raw_parts(needle_data, needle_len as usize);
        if needle_bytes.len() == 1 {
            return haystack
                .iter()
                .position(|byte| *byte == needle_bytes[0])
                .map(|idx| idx as i64)
                .unwrap_or(-1);
        }
        (collection_providers().byte_find)(haystack, needle_bytes, 0)
            .map(|idx| idx as i64)
            .unwrap_or(-1)
    }
}

#[no_mangle]
pub extern "C" fn rt_string_contains(string: RuntimeValue, needle: RuntimeValue) -> i64 {
    (rt_string_find(string, needle) >= 0) as i64
}

/// Find last occurrence of needle in string
/// Returns the byte index, or -1 if not found
#[no_mangle]
pub extern "C" fn rt_string_rfind(string: RuntimeValue, needle: RuntimeValue) -> i64 {
    let str_len = rt_string_len(string);
    let needle_len = rt_string_len(needle);

    if str_len < 0 || needle_len < 0 {
        return -1;
    }

    if needle_len == 0 {
        return str_len;
    }

    if needle_len > str_len {
        return -1;
    }

    let str_data = rt_string_data(string);
    let needle_data = rt_string_data(needle);

    if str_data.is_null() || needle_data.is_null() {
        return -1;
    }

    unsafe {
        let haystack = std::slice::from_raw_parts(str_data, str_len as usize);
        let needle_bytes = std::slice::from_raw_parts(needle_data, needle_len as usize);
        if needle_bytes.len() == 1 {
            return haystack
                .iter()
                .rposition(|byte| *byte == needle_bytes[0])
                .map(|idx| idx as i64)
                .unwrap_or(-1);
        }
        (collection_providers().byte_rfind)(haystack, needle_bytes)
            .map(|idx| idx as i64)
            .unwrap_or(-1)
    }
}

#[no_mangle]
pub extern "C" fn rt_simd_str_search(haystack: RuntimeValue, needle: RuntimeValue) -> i64 {
    rt_string_find(haystack, needle)
}

#[no_mangle]
pub extern "C" fn rt_simd_str_last_index_of(haystack: RuntimeValue, needle: RuntimeValue) -> i64 {
    rt_string_rfind(haystack, needle)
}

#[no_mangle]
pub extern "C" fn rt_simd_str_equal(a: RuntimeValue, b: RuntimeValue) -> bool {
    if a == b {
        return true;
    }

    let a_len = rt_string_len(a);
    let b_len = rt_string_len(b);
    if a_len < 0 || b_len < 0 || a_len != b_len {
        return false;
    }

    if a_len == 0 {
        return true;
    }

    let a_data = rt_string_data(a);
    let b_data = rt_string_data(b);
    if a_data.is_null() || b_data.is_null() {
        return false;
    }

    unsafe {
        let a_bytes = std::slice::from_raw_parts(a_data, a_len as usize);
        let b_bytes = std::slice::from_raw_parts(b_data, b_len as usize);
        a_bytes == b_bytes
    }
}

#[no_mangle]
pub extern "C" fn rt_text_to_lower_ascii(value: RuntimeValue) -> RuntimeValue {
    let len = rt_string_len(value);
    if len < 0 {
        return RuntimeValue::NIL;
    }
    let data = rt_string_data(value);
    if data.is_null() {
        return RuntimeValue::NIL;
    }

    unsafe {
        let bytes = std::slice::from_raw_parts(data, len as usize);
        let lowered: Vec<u8> = bytes.iter().map(|b| b.to_ascii_lowercase()).collect();
        rt_string_new(lowered.as_ptr(), lowered.len() as u64)
    }
}

#[no_mangle]
pub extern "C" fn rt_text_to_upper_ascii(value: RuntimeValue) -> RuntimeValue {
    let len = rt_string_len(value);
    if len < 0 {
        return RuntimeValue::NIL;
    }
    let data = rt_string_data(value);
    if data.is_null() {
        return RuntimeValue::NIL;
    }

    unsafe {
        let bytes = std::slice::from_raw_parts(data, len as usize);
        let uppered: Vec<u8> = bytes.iter().map(|b| b.to_ascii_uppercase()).collect();
        rt_string_new(uppered.as_ptr(), uppered.len() as u64)
    }
}

/// Find index of a substring in a string
/// Returns Option<i64> as enum: Some(index) or None
#[no_mangle]
pub extern "C" fn rt_string_index_of(string: RuntimeValue, needle: RuntimeValue) -> RuntimeValue {
    let str_len = rt_string_len(string);
    let needle_len = rt_string_len(needle);

    if str_len < 0 || needle_len < 0 {
        return super::objects::rt_option_none();
    }

    if needle_len == 0 {
        // Empty needle: return Some(0)
        return super::objects::rt_option_some(RuntimeValue::from_int(0));
    }

    if needle_len > str_len {
        return super::objects::rt_option_none();
    }

    let str_data = rt_string_data(string);
    let needle_data = rt_string_data(needle);

    if str_data.is_null() || needle_data.is_null() {
        return super::objects::rt_option_none();
    }

    unsafe {
        let haystack = std::str::from_utf8_unchecked(std::slice::from_raw_parts(str_data, str_len as usize));
        let needle_str = std::str::from_utf8_unchecked(std::slice::from_raw_parts(needle_data, needle_len as usize));
        match haystack.find(needle_str) {
            Some(idx) => super::objects::rt_option_some(RuntimeValue::from_int(idx as i64)),
            None => super::objects::rt_option_none(),
        }
    }
}

/// Hash a text string and return as i64
///
/// Uses the same compact byte hash as the pure collection benchmark/reference.
#[no_mangle]
pub extern "C" fn rt_hash_text(string: RuntimeValue) -> i64 {
    let len = rt_string_len(string);
    if len < 0 {
        return 0;
    }
    let data = rt_string_data(string);
    if data.is_null() {
        return 0;
    }
    let mut hash = 5381u64;
    unsafe {
        for byte in std::slice::from_raw_parts(data, len as usize) {
            hash = hash.wrapping_mul(33).wrapping_add(*byte as u64);
        }
    }
    hash as i64
}

#[no_mangle]
pub extern "C" fn rt_str_hash(string: RuntimeValue) -> i64 {
    rt_hash_text(string)
}

/// Convert any value to a string representation
#[no_mangle]
pub extern "C" fn rt_to_string(value: RuntimeValue) -> RuntimeValue {
    use super::sffi::io_print::rt_value_to_string;
    rt_value_to_string(value)
}

// Dict SFFI functions are in dict.rs module

// ============================================================================
// Generic collection operations
// ============================================================================

/// Normalize a for-loop iterable for index-based iteration.
/// Dicts become an array of (key, value) tuples (matching interpreter
/// dict-iteration semantics); every other value passes through unchanged.
/// Compiled `for item in <expr>` loops call this before taking the length.
#[no_mangle]
pub extern "C" fn rt_for_iterable(collection: RuntimeValue) -> RuntimeValue {
    match collection.heap_type() {
        Some(HeapObjectType::Dict) => super::dict::rt_dict_entries(collection),
        _ => collection,
    }
}

/// Index into a collection (array, tuple, string, dict)
/// Returns NIL if out of bounds or wrong type
#[no_mangle]
pub extern "C" fn rt_index_get(collection: RuntimeValue, index: RuntimeValue) -> RuntimeValue {
    match collection.heap_type() {
        Some(HeapObjectType::Array) => {
            if index.is_int() {
                rt_array_get(collection, index.as_int())
            } else {
                RuntimeValue::NIL
            }
        }
        Some(HeapObjectType::Tuple) => {
            if index.is_int() {
                let idx = index.as_int();
                if idx < 0 {
                    RuntimeValue::NIL
                } else {
                    rt_tuple_get(collection, idx as u64)
                }
            } else {
                RuntimeValue::NIL
            }
        }
        Some(HeapObjectType::String) => {
            // String indexing returns a single-char string (consistent with char_at)
            if index.is_int() {
                rt_string_char_at(collection, index.as_int())
            } else {
                RuntimeValue::NIL
            }
        }
        Some(HeapObjectType::Dict) => super::dict::rt_dict_get(collection, index),
        _ => RuntimeValue::NIL,
    }
}

/// Set a value in a collection (array, dict)
/// Returns true on success, false on error
#[no_mangle]
pub extern "C" fn rt_index_set(collection: RuntimeValue, index: RuntimeValue, value: RuntimeValue) -> bool {
    match collection.heap_type() {
        Some(HeapObjectType::Array) => {
            if index.is_int() {
                rt_array_set(collection, index.as_int(), value)
            } else {
                false
            }
        }
        Some(HeapObjectType::Dict) => super::dict::rt_dict_set(collection, index, value),
        _ => false,
    }
}

/// Slice a collection (array, tuple, string)
/// Returns a new collection with elements from start to end (exclusive)
#[no_mangle]
pub extern "C" fn rt_slice(collection: RuntimeValue, start: i64, end: i64, step: i64) -> RuntimeValue {
    if step == 0 {
        return RuntimeValue::NIL;
    }

    // Negative step (Python-style `s[::-1]`/`s[9:0:-1]`) is not part of the
    // language: negative INDICES (Ruby-style, count from the end) remain
    // fully supported, but reversal must always be an explicit `.reversed()`
    // call, never an index trick. See
    // doc/04_architecture/language/slicing/+adr/negative_step_not_supported_2026-07-30.md.
    // Before this check, every negative-step form silently returned an EMPTY
    // result here (the string branch below unconditionally treated any
    // `step != 1` as "return empty", and the array branch below actually
    // implemented Python-style negative-step reversal correctly) -- neither
    // was intentional language behavior, and the two diverged from each
    // other and from the interpreter (which, before its own companion fix,
    // silently implemented full Python semantics). A hard abort matches the
    // established native-lane error-raise idiom (`rt_panic`, same crate) --
    // there is no `Result`-returning path back through JIT/native-compiled
    // code to a catchable Simple-level error for this expression form.
    if step < 0 {
        eprintln!(
            "error: negative slice step is not supported -- use .reversed() to reverse a string, array, or tuple"
        );
        std::process::abort();
    }

    match collection.heap_type() {
        Some(HeapObjectType::Array) => {
            let Some(arr) = get_typed_ptr::<RuntimeArray>(collection, HeapObjectType::Array) else {
                return RuntimeValue::NIL;
            };
            unsafe {
                let len = (*arr).len as i64;

                // Normalize start and end
                let start = if start < 0 {
                    (len + start).max(0)
                } else {
                    start.min(len)
                };
                let end = if end < 0 { (len + end).max(0) } else { end.min(len) };

                if step > 0 && start >= end {
                    return rt_array_new(0);
                }
                if step < 0 && start <= end {
                    return rt_array_new(0);
                }

                // Calculate result length
                let result_len = if step > 0 {
                    ((end - start + step - 1) / step) as u64
                } else {
                    ((start - end - step - 1) / (-step)) as u64
                };

                let result = rt_array_new(result_len);
                if result.is_nil() {
                    return result;
                }

                let src_slice = (*arr).as_slice();
                let mut idx = start;
                while (step > 0 && idx < end) || (step < 0 && idx > end) {
                    rt_array_push(result, src_slice[idx as usize]);
                    idx += step;
                }

                result
            }
        }
        Some(HeapObjectType::String) => {
            let Some(str_ptr) = get_typed_ptr::<RuntimeString>(collection, HeapObjectType::String) else {
                return RuntimeValue::NIL;
            };
            unsafe {
                let len = (*str_ptr).len as i64;
                let start = normalize_index(start, len).max(0).min(len);
                let end = normalize_index(end, len).max(0).min(len);

                if step != 1 || start >= end {
                    return rt_string_new(std::ptr::null(), 0);
                }

                // Identity fast path: full-string slice with step 1 returns the same heap object.
                // Mark-sweep GC keeps it alive as long as any pointer remains reachable.
                if start == 0 && end == len {
                    return collection;
                }

                let data = str_ptr.add(1) as *const u8;

                // UTF-8 slice audit, stage 1 (COUNTING ONLY, default off).
                // This range is copied RAW, so a boundary that falls inside a
                // multi-byte codepoint stores invalid bytes and only the byte
                // length betrays it -- stdout's sanitizer renders valid and
                // invalid identically. Record it; do not fail. See
                // simple_runtime::text_slice_audit.
                if crate::text_slice_audit::enabled() {
                    let src = std::slice::from_raw_parts(data, len as usize);
                    crate::text_slice_audit::note(
                        crate::text_slice_audit::site::RT_SLICE_RUST,
                        start,
                        end,
                        src,
                        &src[start as usize..end as usize],
                    );
                }
                rt_string_new(data.add(start as usize), (end - start) as u64)
            }
        }
        _ => RuntimeValue::NIL,
    }
}

// ============================================================================
// Array Higher-Order and Utility Functions
// ============================================================================

/// Reverse an array in place
///
/// # Examples
/// - [1, 2, 3] → [3, 2, 1]
#[no_mangle]
pub extern "C" fn rt_array_reverse(array: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let slice = (*arr).as_mut_slice();
        slice.reverse();
        true
    }
}

/// Create a new reversed copy of an array
///
/// # Examples
/// - reversed([1, 2, 3]) → [3, 2, 1]
#[no_mangle]
pub extern "C" fn rt_array_reversed(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }
        let src_slice = (*arr).as_slice();
        for i in (0..len as usize).rev() {
            rt_array_push(result, src_slice[i]);
        }
        result
    }
}

/// Sort an array in place (ascending order)
/// Works with integers and floats. Mixed types are sorted with ints first.
#[no_mangle]
pub extern "C" fn rt_array_sort(array: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let slice = (*arr).as_mut_slice();
        let providers = collection_providers();
        let report = primitive_sort::sort_runtime_values(slice, providers.simd_tier);
        if report.fallback.is_some() {
            (providers.array_sort)(slice);
        }
        true
    }
}

/// Create a new sorted copy of an array (ascending order)
#[no_mangle]
pub extern "C" fn rt_array_sorted(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }
        // Copy elements
        let src_slice = (*arr).as_slice();
        for item in src_slice {
            rt_array_push(result, *item);
        }
        // Sort in place
        rt_array_sort(result);
        result
    }
}

/// Sort array in descending order
#[no_mangle]
pub extern "C" fn rt_array_sort_desc(array: RuntimeValue) -> bool {
    if !rt_array_sort(array) {
        return false;
    }
    rt_array_reverse(array)
}

/// Get the first element of an array
/// Returns NIL if array is empty
#[no_mangle]
pub extern "C" fn rt_array_first(array: RuntimeValue) -> RuntimeValue {
    rt_array_get(array, 0)
}

/// Create a half-open integer range [start, end) as an array of ints.
#[no_mangle]
pub extern "C" fn rt_range(start: i64, end: i64) -> RuntimeValue {
    if end <= start {
        return rt_array_new(0);
    }

    let len = (end - start) as u64;
    let result = rt_array_new(len);
    if result.is_nil() {
        return result;
    }

    for value in start..end {
        rt_array_push(result, RuntimeValue::from_int(value));
    }

    result
}

/// Create an inclusive integer range [start, end] as an array of ints.
#[no_mangle]
pub extern "C" fn rt_range_inclusive(start: i64, end: i64) -> RuntimeValue {
    if end < start {
        return rt_array_new(0);
    }

    let len = (end - start + 1) as u64;
    let result = rt_array_new(len);
    if result.is_nil() {
        return result;
    }

    for value in start..=end {
        rt_array_push(result, RuntimeValue::from_int(value));
    }

    result
}

/// Get the last element of an array
/// Returns NIL if array is empty
#[no_mangle]
pub extern "C" fn rt_array_last(array: RuntimeValue) -> RuntimeValue {
    rt_array_get(array, -1)
}

/// Return elements for which the closure predicate returns a truthy value.
#[no_mangle]
pub extern "C" fn rt_array_filter(array: RuntimeValue, closure: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    let result = rt_array_new(0);
    if result.is_nil() {
        return result;
    }

    let func_ptr = rt_closure_func_ptr(closure);
    if func_ptr.is_null() {
        return result;
    }

    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue = unsafe { std::mem::transmute(func_ptr) };
    unsafe {
        for item in (*arr).as_slice() {
            if func(closure, *item).truthy() {
                rt_array_push(result, *item);
            }
        }
    }
    result
}

/// Return the first element for which the closure predicate is truthy.
#[no_mangle]
pub extern "C" fn rt_array_find(array: RuntimeValue, closure: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    let func_ptr = rt_closure_func_ptr(closure);
    if func_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue = unsafe { std::mem::transmute(func_ptr) };
    unsafe {
        for item in (*arr).as_slice() {
            if func(closure, *item).truthy() {
                return *item;
            }
        }
    }
    RuntimeValue::NIL
}

/// Receiver-polymorphic `find`, in the same shape as the in-tree `rt_at`,
/// `rt_index_of` and `rt_map` precedents — with ONE difference that is stated
/// here rather than hidden: the two receivers return DIFFERENT SHAPES in the
/// same machine word.
///
/// - ARRAY receiver AND a callable closure argument → `rt_array_find`, i.e. the
///   matching ELEMENT as a tagged `RuntimeValue`, or tagged NIL when no element
///   matches.
/// - EVERYTHING ELSE → `rt_string_find`, i.e. a RAW `i64` byte index, or -1.
///   Text behaviour is bit-for-bit what it was before this symbol existed.
///
/// The dual shape is not a new design choice, it is the PRE-EXISTING contract:
/// `hir/lower/expr/mod.rs` types `find` as `TypeId::I64` only inside its
/// `if is_string` arm, and the array arm gives `find` no type at all, so the
/// consumer's interpretation is already derived from the receiver's static
/// type. Returning one tagged shape for both would therefore have CHANGED text
/// `find`, which is exactly what this fix must not do.
///
/// Why the symbol is needed: `codegen/instr/calls.rs` and the type-blind table
/// in `codegen/llvm/functions.rs` each contained TWO `"find"` arms in one
/// `match` — `"find" | "find_str" => rt_string_find` and, further down,
/// `"find" => rt_array_find`. Rust `match` is first-match-wins, so the array
/// arm was UNREACHABLE; `instr/closures_structs.rs` and `llvm/emitter.rs`
/// mapped the bare name to `rt_string_find` with no array arm at all. Every
/// `arr.find(pred)` on a type-blind path therefore answered the `-1`
/// receiver-mismatch sentinel — including when the match sat at index 0 —
/// while the type-AWARE LLVM table answered with the element. Same source, two
/// answers per backend, no error, exit 0.
///
/// The array branch requires BOTH an array receiver and a callable closure, so
/// an array receiver with a non-closure argument keeps its exact previous
/// answer instead of silently acquiring a new one.
#[no_mangle]
pub extern "C" fn rt_find(receiver: RuntimeValue, arg: RuntimeValue) -> i64 {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some()
        && !rt_closure_func_ptr(arg).is_null()
    {
        return rt_array_find(receiver, arg).to_raw() as i64;
    }
    rt_string_find(receiver, arg)
}

/// Apply `closure` to every element and return a NEW array of the results.
///
/// Codegen contract: the LLVM backend maps `("Array"|"array", "map")` to this
/// symbol (`codegen/llvm/functions.rs`) and emits `receiver + args` verbatim, so
/// the call shape is exactly `rt_array_map(array, closure)`. Before this
/// existed, any `arr.map(f)` compiled under the LLVM backend failed at LINK time
/// with `undefined reference to 'rt_array_map'`.
///
/// Closure ABI matches `rt_array_filter` / `rt_array_find` / `rt_option_map`:
/// the lifted target takes the closure handle as its first argument so it can
/// reach its captures, then the element.
///
/// Iteration is by INDEX rather than over a borrowed slice: the closure is
/// arbitrary user code and may push to or clear the receiver, which would
/// invalidate a slice taken once up front. `rt_array_get` re-reads the header
/// each call and returns NIL past the end, so a shrinking receiver terminates
/// instead of reading freed memory.
#[no_mangle]
pub extern "C" fn rt_array_map(array: RuntimeValue, closure: RuntimeValue) -> RuntimeValue {
    let _ = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    let result = rt_array_new(0);
    if result.is_nil() {
        return result;
    }

    let func_ptr = rt_closure_func_ptr(closure);
    if func_ptr.is_null() {
        return result;
    }

    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue = unsafe { std::mem::transmute(func_ptr) };
    let mut i: i64 = 0;
    while i < rt_array_len(array) {
        let item = rt_array_get(array, i);
        rt_array_push(result, func(closure, item));
        i += 1;
    }
    result
}

/// Receiver-dispatching `map`, in the same shape as `rt_at` and `rt_index_of`.
///
/// The two type-BLIND dispatch tables — the Cranelift
/// `codegen/instr/closures_structs.rs` `"map"` arm and the LLVM
/// `codegen/llvm/emitter.rs` `runtime_method_name` table — mapped the method
/// name `map` straight to `rt_option_map` with no receiver test. A comment at
/// the Cranelift site claimed this "also works for arrays since rt_option_map
/// checks if the value is an enum with Some/None". It does not, and the claim
/// was wrong in a way that produced a silent wrong answer rather than an error:
///
///   * `rt_is_none(array)` is false — an array is not an Option enum — so the
///     early return does not fire;
///   * `rt_enum_payload(array)` takes the `get_typed_ptr::<RuntimeEnum>(_,
///     HeapObjectType::Enum)` path, which fails on an Array and returns NIL;
///   * the closure is then invoked EXACTLY ONCE, on that NIL, and the result is
///     wrapped in `Some`.
///
/// So `[1,2,3].map(f)` yielded `Some(f(nil))` — one call instead of three, on a
/// value that was never in the receiver, boxed in an Option that the source
/// never asked for. No error, no crash, exit 0.
///
/// The test is done here, at runtime, rather than at the two codegen sites
/// because those sites dispatch purely on the method name and have no reliable
/// static receiver type available (`try_compile_builtin_method_call` does not
/// even take one). The type-AWARE LLVM table in `codegen/llvm/functions.rs`
/// already routed `("Array", "map")` to `rt_array_map` and is left untouched.
///
/// Option behaviour is intentionally unchanged: a non-array receiver still goes
/// to `rt_option_map` and keeps its exact previous result, including the `Some`
/// wrap and the None/nil pass-through. Only the array receiver — which had no
/// correct implementation on these two lanes — changes.
#[no_mangle]
pub extern "C" fn rt_map(receiver: RuntimeValue, closure: RuntimeValue) -> RuntimeValue {
    if get_typed_ptr::<RuntimeArray>(receiver, HeapObjectType::Array).is_some() {
        return rt_array_map(receiver, closure);
    }
    rt_option_map(receiver, closure)
}

/// Apply `closure` to every element for its side effects and return the
/// RECEIVER, so `arr.each(f)` is chainable and never yields nil.
///
/// Codegen contract: the LLVM backend maps both `each` and `for_each` to this
/// symbol and emits `rt_array_each(array, closure)`. The call site is typed as
/// returning i64 unconditionally, which is why the receiver is returned rather
/// than a unit/nil value — a nil there would be indistinguishable from failure.
#[no_mangle]
pub extern "C" fn rt_array_each(array: RuntimeValue, closure: RuntimeValue) -> RuntimeValue {
    let _ = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    let func_ptr = rt_closure_func_ptr(closure);
    if func_ptr.is_null() {
        return array;
    }

    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue = unsafe { std::mem::transmute(func_ptr) };
    let mut i: i64 = 0;
    while i < rt_array_len(array) {
        let item = rt_array_get(array, i);
        func(closure, item);
        i += 1;
    }
    array
}

/// Left fold: seed the accumulator with `init` and combine each element with
/// `closure(acc, item)`.
///
/// Codegen contract: the LLVM backend maps both `reduce` and `fold` to this
/// symbol and emits `receiver + args` verbatim, so the call shape is
/// `rt_array_reduce(array, init, closure)` — matching the interpreter, where
/// `reduce`/`fold` take `(init, func)` in that order
/// (`interpreter_method/collections.rs`) and invoke the function as
/// `(acc, item)` (`interpreter_helpers/collections.rs`). Getting that order
/// wrong would be a silently wrong answer for any non-commutative combiner, so
/// it is pinned to the interpreter rather than guessed.
///
/// The lifted closure target therefore has THREE parameters: the closure handle
/// (for captures), the accumulator, and the element.
#[no_mangle]
pub extern "C" fn rt_array_reduce(array: RuntimeValue, init: RuntimeValue, closure: RuntimeValue) -> RuntimeValue {
    let _ = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, init);
    let func_ptr = rt_closure_func_ptr(closure);
    if func_ptr.is_null() {
        return init;
    }

    let func: extern "C" fn(RuntimeValue, RuntimeValue, RuntimeValue) -> RuntimeValue =
        unsafe { std::mem::transmute(func_ptr) };
    let mut acc = init;
    let mut i: i64 = 0;
    while i < rt_array_len(array) {
        let item = rt_array_get(array, i);
        acc = func(closure, acc, item);
        i += 1;
    }
    acc
}

/// Find the index of a value in an array
/// Returns -1 if not found
#[no_mangle]
pub extern "C" fn rt_array_index_of(array: RuntimeValue, value: RuntimeValue) -> i64 {
    use super::sffi::rt_value_eq;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, -1);
    unsafe {
        let slice = (*arr).as_slice();
        for (i, item) in slice.iter().enumerate() {
            if rt_value_eq(*item, value) != 0 {
                return i as i64;
            }
        }
        -1
    }
}

/// Receiver-polymorphic `index_of`: works on both arrays and text.
///
/// ROOT FIX (array_index_of_always_minus_one_2026-07-28): codegen mapped the
/// `index_of` method name unconditionally to `rt_string_find`, so
/// `[T].index_of(v)` called a *string* search on an array receiver.
/// `rt_string_find` bails with -1 when `rt_string_len` reports a non-string, so
/// EVERY array `index_of` returned -1 — including when the element was present
/// at index 0. `rt_array_index_of` already existed and was correct, but was
/// never wired into codegen. (The `"find" => rt_array_find` arm sitting below
/// `"index_of" | "find" | "find_str" => rt_string_find` in those same match
/// tables was likewise unreachable.)
///
/// Dispatch is by trial rather than a kind test because both callees are total
/// and return -1 on receiver-type mismatch: an array receiver makes
/// `rt_string_find` return -1, and a text receiver makes `rt_array_index_of`
/// return -1. Array is tried first so a text receiver never hits the array path.
#[no_mangle]
pub extern "C" fn rt_index_of(haystack: RuntimeValue, needle: RuntimeValue) -> i64 {
    let as_array = rt_array_index_of(haystack, needle);
    if as_array >= 0 {
        return as_array;
    }
    rt_string_find(haystack, needle)
}

/// Find the last index of a value in an array
/// Returns -1 if not found
#[no_mangle]
pub extern "C" fn rt_array_last_index_of(array: RuntimeValue, value: RuntimeValue) -> i64 {
    use super::sffi::rt_value_eq;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, -1);
    unsafe {
        let slice = (*arr).as_slice();
        for (i, item) in slice.iter().enumerate().rev() {
            if rt_value_eq(*item, value) != 0 {
                return i as i64;
            }
        }
        -1
    }
}

/// Concatenate two arrays into a new array
#[no_mangle]
pub extern "C" fn rt_array_concat(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue {
    let arr_a = as_typed_ptr!(a, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    let arr_b = as_typed_ptr!(b, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len_a = (*arr_a).len;
        let len_b = (*arr_b).len;
        let result = rt_array_new(len_a + len_b);
        if result.is_nil() {
            return result;
        }

        // Copy from first array
        for item in (*arr_a).as_slice() {
            rt_array_push(result, *item);
        }
        // Copy from second array
        for item in (*arr_b).as_slice() {
            rt_array_push(result, *item);
        }
        result
    }
}

/// Create a shallow copy of an array
#[no_mangle]
pub extern "C" fn rt_array_copy(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }
        for item in (*arr).as_slice() {
            rt_array_push(result, *item);
        }
        result
    }
}

/// Sum all numeric elements in an array
/// Returns 0 for empty arrays, NIL for non-numeric elements
#[no_mangle]
pub extern "C" fn rt_array_sum(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let slice = (*arr).as_slice();
        if slice.is_empty() {
            return RuntimeValue::from_int(0);
        }

        let mut int_sum: i64 = 0;
        let mut float_sum: f64 = 0.0;
        let mut has_float = false;

        for item in slice {
            if item.is_int() {
                int_sum += item.as_int();
            } else if item.is_float() {
                has_float = true;
                float_sum += item.as_float();
            }
        }

        if has_float {
            RuntimeValue::from_float(int_sum as f64 + float_sum)
        } else {
            RuntimeValue::from_int(int_sum)
        }
    }
}

/// Find the minimum element in an array
/// Returns NIL for empty arrays
#[no_mangle]
pub extern "C" fn rt_array_min(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let slice = (*arr).as_slice();
        if slice.is_empty() {
            return RuntimeValue::NIL;
        }

        let mut min_val = slice[0];
        for item in &slice[1..] {
            let cmp = if min_val.is_int() && item.is_int() {
                item.as_int() < min_val.as_int()
            } else if min_val.is_float() && item.is_float() {
                item.as_float() < min_val.as_float()
            } else if min_val.is_int() && item.is_float() {
                item.as_float() < min_val.as_int() as f64
            } else if min_val.is_float() && item.is_int() {
                (item.as_int() as f64) < min_val.as_float()
            } else {
                false
            };
            if cmp {
                min_val = *item;
            }
        }
        min_val
    }
}

/// Find the maximum element in an array
/// Returns NIL for empty arrays
#[no_mangle]
pub extern "C" fn rt_array_max(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let slice = (*arr).as_slice();
        if slice.is_empty() {
            return RuntimeValue::NIL;
        }

        let mut max_val = slice[0];
        for item in &slice[1..] {
            let cmp = if max_val.is_int() && item.is_int() {
                item.as_int() > max_val.as_int()
            } else if max_val.is_float() && item.is_float() {
                item.as_float() > max_val.as_float()
            } else if max_val.is_int() && item.is_float() {
                item.as_float() > max_val.as_int() as f64
            } else if max_val.is_float() && item.is_int() {
                (item.as_int() as f64) > max_val.as_float()
            } else {
                false
            };
            if cmp {
                max_val = *item;
            }
        }
        max_val
    }
}

/// Count occurrences of a value in an array
#[no_mangle]
pub extern "C" fn rt_array_count(array: RuntimeValue, value: RuntimeValue) -> i64 {
    use super::sffi::rt_value_eq;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, -1);
    unsafe {
        let slice = (*arr).as_slice();
        let mut count = 0i64;
        for item in slice {
            if rt_value_eq(*item, value) != 0 {
                count += 1;
            }
        }
        count
    }
}

/// Zip two arrays together into an array of tuples
/// The result length is the minimum of the two input lengths
#[no_mangle]
pub extern "C" fn rt_array_zip(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue {
    let arr_a = as_typed_ptr!(a, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    let arr_b = as_typed_ptr!(b, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len_a = (*arr_a).len;
        let len_b = (*arr_b).len;
        let result_len = len_a.min(len_b);

        let result = rt_array_new(result_len);
        if result.is_nil() {
            return result;
        }

        let slice_a = (*arr_a).as_slice();
        let slice_b = (*arr_b).as_slice();

        for i in 0..result_len as usize {
            // Create a tuple for each pair
            let tuple = rt_tuple_new(2);
            if tuple.is_nil() {
                return RuntimeValue::NIL;
            }
            rt_tuple_set(tuple, 0, slice_a[i]);
            rt_tuple_set(tuple, 1, slice_b[i]);
            rt_array_push(result, tuple);
        }
        result
    }
}

/// Enumerate an array, returning array of (index, value) tuples
#[no_mangle]
pub extern "C" fn rt_array_enumerate(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len = (*arr).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }

        let slice = (*arr).as_slice();
        for (i, item) in slice.iter().enumerate() {
            let tuple = rt_tuple_new(2);
            if tuple.is_nil() {
                return RuntimeValue::NIL;
            }
            rt_tuple_set(tuple, 0, RuntimeValue::from_int(i as i64));
            rt_tuple_set(tuple, 1, *item);
            rt_array_push(result, tuple);
        }
        result
    }
}

/// Flatten a nested array one level deep
/// [[1, 2], [3, 4]] → [1, 2, 3, 4]
#[no_mangle]
pub extern "C" fn rt_array_flatten(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let slice = (*arr).as_slice();

        // First pass: count total elements
        let mut total_len = 0u64;
        for item in slice {
            if let Some(inner) = get_typed_ptr::<RuntimeArray>(*item, HeapObjectType::Array) {
                total_len += (*inner).len;
                continue;
            }
            total_len += 1;
        }

        let result = rt_array_new(total_len);
        if result.is_nil() {
            return result;
        }

        // Second pass: copy elements
        for item in slice {
            if let Some(inner) = get_typed_ptr::<RuntimeArray>(*item, HeapObjectType::Array) {
                for inner_item in (*inner).as_slice() {
                    rt_array_push(result, *inner_item);
                }
                continue;
            }
            rt_array_push(result, *item);
        }
        result
    }
}

/// Remove duplicate values from array (keeps first occurrence)
/// Returns a new array
#[no_mangle]
pub extern "C" fn rt_array_unique(array: RuntimeValue) -> RuntimeValue {
    use super::sffi::rt_value_eq;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let slice = (*arr).as_slice();
        let result = rt_array_new((*arr).len);
        if result.is_nil() {
            return result;
        }

        let result_arr = get_typed_ptr::<RuntimeArray>(result, HeapObjectType::Array).unwrap();

        for item in slice {
            // Check if item already exists in result
            let mut found = false;
            for existing in (*result_arr).as_slice() {
                if rt_value_eq(*existing, *item) != 0 {
                    found = true;
                    break;
                }
            }
            if !found {
                rt_array_push(result, *item);
            }
        }
        result
    }
}

/// Take first n elements from array
#[no_mangle]
pub extern "C" fn rt_array_take(array: RuntimeValue, n: i64) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len = (*arr).len as i64;
        let take_count = n.max(0).min(len) as u64;

        let result = rt_array_new(take_count);
        if result.is_nil() {
            return result;
        }

        let slice = (*arr).as_slice();
        for item in slice.iter().take(take_count as usize) {
            rt_array_push(result, *item);
        }
        result
    }
}

/// Drop first n elements from array
#[no_mangle]
pub extern "C" fn rt_array_drop(array: RuntimeValue, n: i64) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len = (*arr).len as i64;
        let skip_count = n.max(0).min(len) as usize;
        let result_len = (len - skip_count as i64) as u64;

        let result = rt_array_new(result_len);
        if result.is_nil() {
            return result;
        }

        let slice = (*arr).as_slice();
        for item in slice.iter().take(len as usize).skip(skip_count) {
            rt_array_push(result, *item);
        }
        result
    }
}

/// Join array elements into a string with separator
#[no_mangle]
pub extern "C" fn rt_array_join(array: RuntimeValue, separator: RuntimeValue) -> RuntimeValue {
    use super::sffi::rt_value_to_string;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let slice = (*arr).as_slice();
        if slice.is_empty() {
            return rt_string_new(std::ptr::null(), 0);
        }

        // Get separator string
        let sep_len = rt_string_len(separator);
        let sep_data = if sep_len > 0 {
            rt_string_data(separator)
        } else {
            std::ptr::null()
        };

        // Build result by concatenating
        let mut result = rt_value_to_string(slice[0]);

        for item in &slice[1..] {
            if sep_len > 0 {
                result = rt_string_concat(result, separator);
            }
            let item_str = rt_value_to_string(*item);
            result = rt_string_concat(result, item_str);
        }

        result
    }
}

/// Check if all elements satisfy a condition (all non-falsy)
/// Returns 1 if all elements are truthy, 0 otherwise
#[no_mangle]
pub extern "C" fn rt_array_all_truthy(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);

    unsafe {
        let slice = (*arr).as_slice();
        for item in slice {
            // Check if falsy: nil, false, 0, 0.0
            if item.is_nil() {
                return 0;
            }
            if item.is_bool() && !item.as_bool() {
                return 0;
            }
            if item.is_int() && item.as_int() == 0 {
                return 0;
            }
            if item.as_heap_u64() == Some(0) {
                return 0;
            }
            if item.is_float() && item.as_float() == 0.0 {
                return 0;
            }
        }
        1
    }
}

/// `arr.all(pred)`: true when `pred` is truthy for EVERY element.
///
/// Codegen contract: all four backend dispatch sites — `codegen/llvm/
/// functions.rs` (both the type-blind fallback table and the
/// `("Array", "all")` table), `codegen/llvm/emitter.rs` and the Cranelift
/// `codegen/instr/{calls,closures_structs}.rs` — map `all` here and emit
/// `receiver + args` verbatim, i.e. `rt_array_all(array, closure)`. This
/// function previously took only `(array)` and forwarded to
/// `rt_array_all_truthy`, so the predicate operand was accepted by the ABI and
/// then DISCARDED: `[1,2,3].all(x => x > 10)` answered `true` (every element is
/// truthy) instead of `false`, and the predicate was never invoked even once.
///
/// Semantics are pinned to the interpreter (`interpreter_helpers/collections.rs`
/// `eval_array_all`), not guessed: the predicate is called with the element
/// alone, iteration SHORT-CIRCUITS on the first falsy result, and an empty
/// receiver is vacuously `true`.
///
/// The zero-predicate spelling is a SEPARATE symbol, not a defaulted argument:
/// `arr.all_truthy()` lowers to `rt_array_all_truthy(array)` via its own MIR arm
/// (`mir/lower/lowering_expr_method.rs`), so no caller reaches this function
/// with one operand. A non-closure `closure` (nil, or a value that is not a
/// registered closure) therefore still degrades to element truthiness rather
/// than calling through an unvalidated address — the same bail-out
/// `rt_array_filter`/`rt_array_find`/`rt_array_map` use.
#[no_mangle]
pub extern "C" fn rt_array_all(array: RuntimeValue, closure: RuntimeValue) -> i64 {
    let _ = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    let func_ptr = rt_closure_func_ptr(closure);
    if func_ptr.is_null() {
        return rt_array_all_truthy(array);
    }

    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue = unsafe { std::mem::transmute(func_ptr) };
    let mut i: i64 = 0;
    while i < rt_array_len(array) {
        if !func(closure, rt_array_get(array, i)).truthy() {
            return 0;
        }
        i += 1;
    }
    1
}

/// Check if any element is truthy
/// Returns 1 if any element is truthy, 0 otherwise
#[no_mangle]
pub extern "C" fn rt_array_any_truthy(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);

    unsafe {
        let slice = (*arr).as_slice();
        for item in slice {
            // Check if truthy: not (nil, false, 0, 0.0)
            if item.is_nil() {
                continue;
            }
            if item.is_bool() && !item.as_bool() {
                continue;
            }
            if item.is_int() && item.as_int() == 0 {
                continue;
            }
            if item.as_heap_u64() == Some(0) {
                continue;
            }
            if item.is_float() && item.as_float() == 0.0 {
                continue;
            }
            return 1;
        }
        0
    }
}

/// `arr.any(pred)`: true when `pred` is truthy for AT LEAST ONE element.
///
/// See `rt_array_all` for the full codegen contract and the arity divergence
/// this fixes; the two are the same defect. Semantics pinned to
/// `eval_array_any` (`interpreter_helpers/collections.rs`): the predicate takes
/// the element alone, iteration SHORT-CIRCUITS on the first truthy result, and
/// an empty receiver is `false`.
#[no_mangle]
pub extern "C" fn rt_array_any(array: RuntimeValue, closure: RuntimeValue) -> i64 {
    let _ = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    let func_ptr = rt_closure_func_ptr(closure);
    if func_ptr.is_null() {
        return rt_array_any_truthy(array);
    }

    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue = unsafe { std::mem::transmute(func_ptr) };
    let mut i: i64 = 0;
    while i < rt_array_len(array) {
        if func(closure, rt_array_get(array, i)).truthy() {
            return 1;
        }
        i += 1;
    }
    0
}

/// Fill array with a value (in place)
#[no_mangle]
pub extern "C" fn rt_array_fill(array: RuntimeValue, value: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let slice = (*arr).as_mut_slice();
        for item in slice {
            *item = value;
        }
        true
    }
}

/// Create a new array filled with a value
#[no_mangle]
pub extern "C" fn rt_array_repeat(value: RuntimeValue, count: i64) -> RuntimeValue {
    if count <= 0 {
        return rt_array_new(0);
    }

    let result = rt_array_new(count as u64);
    if result.is_nil() {
        return result;
    }

    let arr = as_typed_ptr!(mut result, HeapObjectType::Array, RuntimeArray, result);
    unsafe {
        (*arr).len = count as u64;
        (*arr).as_mut_slice().fill(value);
    }
    result
}

/// Create an array with a range of integers [start, end)
#[no_mangle]
pub extern "C" fn rt_array_range(start: i64, end: i64, step: i64) -> RuntimeValue {
    if step == 0 {
        return RuntimeValue::NIL;
    }

    let count = if step > 0 {
        if end <= start {
            0
        } else {
            ((end - start + step - 1) / step) as u64
        }
    } else if start <= end {
        0
    } else {
        ((start - end - step - 1) / (-step)) as u64
    };

    let result = rt_array_new(count);
    if result.is_nil() {
        return result;
    }

    let mut i = start;
    while (step > 0 && i < end) || (step < 0 && i > end) {
        rt_array_push(result, RuntimeValue::from_int(i));
        i += step;
    }
    result
}

// ============================================================================
// Membership Testing
// ============================================================================

/// Check if a value is contained in a collection (array, dict, string)
/// Returns true (1) if found, false (0) if not
#[no_mangle]
pub extern "C" fn rt_contains(collection: RuntimeValue, value: RuntimeValue) -> u8 {
    use super::sffi::rt_value_eq;

    match collection.heap_type() {
        Some(HeapObjectType::Array) => {
            let Some(arr) = get_typed_ptr::<RuntimeArray>(collection, HeapObjectType::Array) else {
                return 0;
            };
            unsafe {
                let slice = (*arr).as_slice();
                for item in slice {
                    if rt_value_eq(*item, value) != 0 {
                        return 1;
                    }
                }
            }
            0
        }
        Some(HeapObjectType::Dict) => {
            // For dicts, 'in' checks if the key exists using hash lookup
            let result = super::dict::rt_dict_get(collection, value);
            if result.is_nil() {
                0
            } else {
                1
            }
        }
        Some(HeapObjectType::String) => {
            let Some(str_ptr) = get_typed_ptr::<RuntimeString>(collection, HeapObjectType::String) else {
                return 0;
            };
            unsafe {
                let haystack = (*str_ptr).as_bytes();

                if let Some(needle_ptr) = get_typed_ptr::<RuntimeString>(value, HeapObjectType::String) {
                    let needle = (*needle_ptr).as_bytes();
                    if needle.is_empty() {
                        return 1;
                    }
                    if needle.len() > haystack.len() {
                        return 0;
                    }
                    return haystack.windows(needle.len()).any(|window| window == needle) as u8;
                }

                if value.is_int() {
                    let char_code = value.as_int();
                    for &byte in haystack {
                        if byte as i64 == char_code {
                            return 1;
                        }
                    }
                }
                0
            }
        }
        _ => 0,
    }
}

#[no_mangle]
pub extern "C" fn __simple_intrinsic_bounds_check(index: i64, len: i64) -> i64 {
    if index < 0 || index >= len {
        eprintln!("PANIC: bounds_check intrinsic index={index} len={len}");
        std::process::exit(1);
    }
    0
}

#[cfg(test)]
#[path = "collection_tests.rs"]
mod tests;

/// Rust-side twin of `src/runtime/test/rt_string_free_selfcheck.c`.
///
/// The C runtime and this one must agree bit for bit on rt_string_free's
/// contract, or the same .spl leaks on one backend and frees on the other.
/// The C side had 16 assertions and this side had none, so a divergence here
/// would have been invisible. These mirror the C cases.
///
/// The heap registry is process-global and `cargo test` runs tests in parallel,
/// so every case here serializes on GUARD and asserts on RETURN VALUES and
/// readability rather than absolute registry counts. Count deltas are taken
/// under the lock; an unlocked absolute count would flake against other tests.
#[cfg(test)]
mod string_free_contract_tests {
    use super::{
        rt_array_new, rt_array_push, rt_string_free, rt_string_len, rt_string_new,
        rt_string_new_literal, rt_transient_array_scope_begin, rt_transient_array_scope_end,
        rt_transient_array_scope_pause, rt_transient_heap_promote,
    };
    use crate::value::dict::{rt_dict_get, rt_dict_new, rt_dict_set};
    use crate::value::objects::{
        rt_closure_get_capture, rt_closure_new, rt_closure_set_capture, rt_enum_new,
        rt_enum_payload,
    };
    use crate::value::heap::rt_heap_registry_count;
    use std::sync::Mutex;

    static GUARD: Mutex<()> = Mutex::new(());

    fn mkstr(s: &str) -> crate::value::RuntimeValue {
        rt_string_new(s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn ordinary_string_is_reclaimed_and_registry_shrinks() {
        let _g = GUARD.lock().unwrap();
        let before = rt_heap_registry_count();
        let s = mkstr("a reasonably long unique string for the rust twin");
        assert_eq!(rt_heap_registry_count(), before + 1, "new string registers");
        assert_eq!(rt_string_free(s), 1, "ordinary string is freed");
        assert_eq!(rt_heap_registry_count(), before, "registry returns to baseline");
    }

    #[test]
    fn double_free_is_refused_without_decrementing() {
        let _g = GUARD.lock().unwrap();
        let s = mkstr("string freed exactly once, rust twin");
        assert_eq!(rt_string_free(s), 1);
        let after_first = rt_heap_registry_count();
        assert_eq!(rt_string_free(s), 0, "double free refused");
        assert_eq!(rt_heap_registry_count(), after_first, "refusal does not decrement");
    }

    #[test]
    fn short_cached_string_is_refused_and_stays_usable() {
        let _g = GUARD.lock().unwrap();
        // len <= 1 comes from the process-wide SHORT_STRING_CACHE and is shared
        // by every caller; freeing one would corrupt all the others.
        let sh = mkstr("x");
        assert_eq!(rt_string_free(sh), 0, "short/cached string refused");
        assert_eq!(rt_string_len(mkstr("x")), 1, "still usable after refused free");
    }

    #[test]
    fn interned_literal_is_refused_and_stays_interned() {
        let _g = GUARD.lock().unwrap();
        const LIT: &[u8] = b"an interned literal value for the rust twin";
        let a = rt_string_new_literal(LIT.as_ptr(), LIT.len() as u64);
        assert_eq!(rt_string_free(a), 0, "interned literal refused");
        let b = rt_string_new_literal(LIT.as_ptr(), LIT.len() as u64);
        assert_eq!(a.to_raw(), b.to_raw(), "interning still returns the same object");
        assert_eq!(rt_string_len(b), LIT.len() as i64, "interned literal intact");
    }

    /// The case a tombstone-less registry erase would fail: free every other
    /// entry out of a batch, then confirm each survivor is still readable AND
    /// still freeable, i.e. no live entry was stranded by a deletion.
    #[test]
    fn interleaved_frees_do_not_strand_survivors() {
        let _g = GUARD.lock().unwrap();
        const N: usize = 512;
        let mut v = Vec::with_capacity(N);
        for i in 0..N {
            v.push(mkstr(&format!("probe-chain-integrity-rust-{i}")));
        }
        let freed = (0..N).step_by(2).filter(|&i| rt_string_free(v[i]) == 1).count();
        assert_eq!(freed, N / 2, "every even-indexed string freed");

        for i in (1..N).step_by(2) {
            let expect = format!("probe-chain-integrity-rust-{i}").len() as i64;
            assert_eq!(rt_string_len(v[i]), expect, "survivor {i} still readable");
        }
        let refreed = (1..N).step_by(2).filter(|&i| rt_string_free(v[i]) == 1).count();
        assert_eq!(refreed, N / 2, "every survivor still found and freed");
    }

    #[test]
    fn transient_ordinary_string_is_reclaimed_and_aliases_free_once() {
        let _g = GUARD.lock().unwrap();
        let before = rt_heap_registry_count();
        assert!(rt_transient_array_scope_begin());
        let string = mkstr("transient ordinary rust string");
        let left = rt_array_new(1);
        let right = rt_array_new(1);
        assert!(rt_array_push(left, string));
        assert!(rt_array_push(right, string));
        assert_eq!(rt_heap_registry_count(), before + 3);
        assert!(rt_transient_array_scope_end());
        assert_eq!(rt_heap_registry_count(), before, "string and aliases reclaim exactly once");
        assert_eq!(rt_string_len(string), -1, "reclaimed string is no longer readable");
    }

    #[test]
    fn promoted_string_and_reachable_alias_graph_survive() {
        extern "C" fn retained_closure_target() {}

        let _g = GUARD.lock().unwrap();
        let before = rt_heap_registry_count();
        assert!(rt_transient_array_scope_begin());
        let text = mkstr("promoted graph string");
        let unreachable = mkstr("unreachable sibling string");
        let root = rt_array_new(3);
        let dict = rt_dict_new(0);
        let en = rt_enum_new(700_003, 1, text);
        let closure = rt_closure_new(retained_closure_target as *const () as *const u8, 1);
        assert!(rt_closure_set_capture(closure, 0, text));
        assert!(rt_array_push(root, text));
        assert!(rt_array_push(root, dict));
        assert!(rt_array_push(root, closure));
        assert!(rt_dict_set(dict, text, en));
        assert!(rt_dict_set(dict, en, root));
        assert!(rt_transient_array_scope_pause());
        assert!(rt_transient_heap_promote(root));
        assert!(rt_transient_array_scope_end());
        assert_eq!(rt_string_len(text), 21);
        assert_eq!(rt_dict_get(dict, text), en);
        assert_eq!(rt_enum_payload(en), text);
        assert_eq!(rt_closure_get_capture(closure, 0), text);
        assert_eq!(rt_string_len(unreachable), -1, "unreachable sibling is reclaimed");
        assert_eq!(rt_heap_registry_count(), before + 5, "only five promoted graph nodes survive");
    }

    #[test]
    fn direct_promoted_shared_interned_and_post_pause_strings_obey_boundaries() {
        const LIT: &[u8] = b"scope-created shared literal rust";
        let _g = GUARD.lock().unwrap();

        assert!(rt_transient_array_scope_begin());
        let direct = mkstr("direct promoted rust string");
        let short = mkstr("q");
        let literal = rt_string_new_literal(LIT.as_ptr(), LIT.len() as u64);
        assert!(rt_transient_array_scope_pause());
        assert!(rt_transient_heap_promote(direct));
        let post_pause = mkstr("post pause persistent rust string");
        assert!(rt_transient_array_scope_end());

        assert_eq!(rt_string_len(direct), 27);
        assert_eq!(rt_string_len(post_pause), 33);
        assert_eq!(mkstr("q"), short, "short cache stays pointer-identical");
        assert_eq!(
            rt_string_new_literal(b"q".as_ptr(), 1),
            short,
            "one-byte literal reuses the ordinary short cache"
        );
        assert_eq!(rt_string_new_literal(LIT.as_ptr(), LIT.len() as u64), literal);
        assert_eq!(rt_string_free(short), 0, "shared short string remains protected");
        assert_eq!(
            rt_string_free(rt_string_new_literal(b"q".as_ptr(), 1)),
            0,
            "one-byte literal remains shared and refuses free"
        );
        assert_eq!(rt_string_free(literal), 0, "interned literal remains protected");
        assert_eq!(rt_string_free(direct), 1);
        assert_eq!(rt_string_free(post_pause), 1);
    }

    #[test]
    fn repeated_transient_string_scopes_return_to_fixed_registry_bound() {
        let _g = GUARD.lock().unwrap();
        let before = rt_heap_registry_count();
        for round in 0..128 {
            assert!(rt_transient_array_scope_begin());
            for item in 0..256 {
                let value = format!("rust-scope-{round}-transient-{item}");
                let string = rt_string_new(value.as_ptr(), value.len() as u64);
                assert!(rt_string_len(string) > 1);
            }
            assert!(rt_transient_array_scope_end());
            assert_eq!(rt_heap_registry_count(), before, "registry drift after round {round}");
        }
    }
}

/// Lane-L3 aux-byte accounting: array backing-buffer capacity bytes must rise
/// on create/grow and fall on free. The counters are process-global and other
/// tests allocate concurrently, so assertions use a delta large enough (1 MiB)
/// to dominate unrelated churn instead of exact equality.
#[cfg(test)]
mod aux_byte_accounting_tests {
    use super::{rt_array_free, rt_array_new, rt_array_push_grow};
    use crate::value::core::RuntimeValue;
    use crate::value::heap::{rt_heap_array_capacity_bytes, rt_heap_aux_live_bytes, rt_heap_aux_live_bytes_by_kind, HeapObjectType};

    #[test]
    fn aux_counters_rise_on_array_growth_and_fall_on_free() {
        const SLOTS: i64 = 1 << 17; // 128K RuntimeValue slots = 1 MiB capacity
        const BYTES: i64 = SLOTS * 8;

        let before = rt_heap_array_capacity_bytes();
        let arr = rt_array_new(4);
        assert!(!arr.is_nil(), "array allocation succeeded");
        for i in 0..SLOTS {
            assert!(rt_array_push_grow(arr, RuntimeValue::from_int(i)));
        }
        let grown = rt_heap_array_capacity_bytes();
        assert!(
            grown >= before + BYTES,
            "growth must raise array capacity bytes: before={before} grown={grown}"
        );
        assert!(
            rt_heap_aux_live_bytes_by_kind(HeapObjectType::Array as i64) >= before + BYTES,
            "by-kind view must see the same growth"
        );
        assert!(
            rt_heap_aux_live_bytes() >= before + BYTES,
            "all-kind aux total must include array backing bytes"
        );

        rt_array_free(arr);
        let freed = rt_heap_array_capacity_bytes();
        assert!(
            freed <= grown - BYTES,
            "free must return capacity bytes: grown={grown} freed={freed}"
        );
    }
}

/// Contract tests for `rt_array_free_deep`, the Rust twin of the C primitive at
/// src/runtime/runtime_native.c:5335.
///
/// The two runtimes must agree bit for bit or the same `.spl` leaks on one
/// backend and frees on the other — the exact divergence class the
/// `rt_string_free` twin tests above exist to catch. These assert the
/// all-or-nothing policy: a refused call must leave the registry EXACTLY where
/// it was, because a partial free is the irreversible failure the contract is
/// built to prevent.
///
/// The heap registry is process-global and `cargo test` runs in parallel, so
/// every case serializes on GUARD and asserts on registry DELTAS.
#[cfg(test)]
mod array_free_deep_contract_tests {
    use super::{
        rt_array_free_deep, rt_array_get, rt_array_new, rt_array_push, rt_byte_array_new, rt_string_len, rt_string_new,
        rt_string_new_literal,
    };
    use crate::value::dict::rt_dict_new;
    use crate::value::heap::rt_heap_registry_count;
    use crate::value::RuntimeValue;
    use std::sync::Mutex;

    static GUARD: Mutex<()> = Mutex::new(());

    fn mkstr(s: &str) -> RuntimeValue {
        rt_string_new(s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn array_of_strings_is_freed_whole_and_registry_returns_to_baseline() {
        let _g = GUARD.lock().unwrap();
        let before = rt_heap_registry_count();
        let a = rt_array_new(4);
        assert!(rt_array_push(a, mkstr("deep free element one, long enough to avoid the cache")));
        assert!(rt_array_push(a, mkstr("deep free element two, long enough to avoid the cache")));
        assert!(rt_array_push(a, mkstr("deep free element three, long enough to avoid the cache")));
        assert_eq!(rt_heap_registry_count(), before + 4, "array + three strings register");
        assert_eq!(rt_array_free_deep(a), 1, "tree of non-shared strings is reclaimed");
        assert_eq!(rt_heap_registry_count(), before, "every node returned to the registry baseline");
    }

    #[test]
    fn nested_arrays_are_freed_recursively() {
        let _g = GUARD.lock().unwrap();
        let before = rt_heap_registry_count();
        let inner = rt_array_new(4);
        assert!(rt_array_push(inner, mkstr("nested deep free leaf string, unique and long")));
        let outer = rt_array_new(4);
        assert!(rt_array_push(outer, inner));
        assert!(rt_array_push(outer, RuntimeValue::from_int(41)));
        assert_eq!(rt_heap_registry_count(), before + 3, "outer + inner + leaf string");
        assert_eq!(rt_array_free_deep(outer), 1, "nested tree is reclaimed");
        assert_eq!(rt_heap_registry_count(), before, "recursion reached every level");
    }

    #[test]
    fn immediate_only_array_is_freed_and_needs_no_element_scan() {
        let _g = GUARD.lock().unwrap();
        let before = rt_heap_registry_count();
        let a = rt_array_new(4);
        for n in 0..4i64 {
            assert!(rt_array_push(a, RuntimeValue::from_int(n)));
        }
        assert_eq!(rt_array_free_deep(a), 1, "immediates are leaves, nothing to strand");
        assert_eq!(rt_heap_registry_count(), before);
    }

    #[test]
    fn byte_packed_array_is_freed_without_reading_payload_as_values() {
        let _g = GUARD.lock().unwrap();
        let before = rt_heap_registry_count();
        let a = rt_byte_array_new(64);
        assert_eq!(rt_array_free_deep(a), 1, "packed payload holds no heap refs by construction");
        assert_eq!(rt_heap_registry_count(), before);
    }

    /// The load-bearing case: a dict element cannot be freed here (no free path
    /// that would not strand its entries buffer), so the WHOLE call must refuse
    /// and the sibling string must remain both registered and readable.
    #[test]
    fn dict_element_refuses_whole_call_and_frees_nothing() {
        let _g = GUARD.lock().unwrap();
        let survivor = mkstr("sibling that must survive a refused deep free, unique");
        let a = rt_array_new(4);
        assert!(rt_array_push(a, survivor));
        assert!(rt_array_push(a, rt_dict_new(8)));
        let before = rt_heap_registry_count();
        assert_eq!(rt_array_free_deep(a), 0, "unfreeable element refuses the call");
        assert_eq!(rt_heap_registry_count(), before, "ALL-OR-NOTHING: nothing was freed");
        assert!(rt_string_len(rt_array_get(a, 0)) > 0, "survivor still readable");
    }

    /// A shared (interned literal) string is handed to unrelated holders, so it
    /// refuses exactly as `rt_string_free` refuses it — and takes the whole
    /// call with it.
    #[test]
    fn shared_string_element_refuses_whole_call() {
        let _g = GUARD.lock().unwrap();
        let lit = "an interned literal that other holders share, rust twin";
        let interned = rt_string_new_literal(lit.as_ptr(), lit.len() as u64);
        let a = rt_array_new(4);
        assert!(rt_array_push(a, mkstr("ordinary sibling of a shared string, unique")));
        assert!(rt_array_push(a, interned));
        let before = rt_heap_registry_count();
        assert_eq!(rt_array_free_deep(a), 0, "SHARED element refuses");
        assert_eq!(rt_heap_registry_count(), before, "nothing freed");
        assert!(rt_string_len(interned) > 0, "interned literal still readable");
    }

    /// Phase 1's `seen` set proves the reachable structure is a TREE. A self
    /// reference is the smallest cycle; freeing it bottom-up would double-free.
    #[test]
    fn self_referencing_array_refuses() {
        let _g = GUARD.lock().unwrap();
        let a = rt_array_new(4);
        assert!(rt_array_push(a, a));
        let before = rt_heap_registry_count();
        assert_eq!(rt_array_free_deep(a), 0, "cycle refuses");
        assert_eq!(rt_heap_registry_count(), before, "nothing freed");
    }

    #[test]
    fn duplicated_element_alias_refuses() {
        let _g = GUARD.lock().unwrap();
        let shared_child = mkstr("one string reachable through two slots, unique and long");
        let a = rt_array_new(4);
        assert!(rt_array_push(a, shared_child));
        assert!(rt_array_push(a, shared_child));
        let before = rt_heap_registry_count();
        assert_eq!(rt_array_free_deep(a), 0, "internal alias refuses");
        assert_eq!(rt_heap_registry_count(), before, "nothing freed");
        assert!(rt_string_len(shared_child) > 0, "aliased string still readable");
    }

    #[test]
    fn non_array_root_and_double_free_are_refused() {
        let _g = GUARD.lock().unwrap();
        assert_eq!(
            rt_array_free_deep(mkstr("a string root belongs to rt_string_free, unique")),
            0,
            "string root refused"
        );
        assert_eq!(rt_array_free_deep(RuntimeValue::from_int(7)), 0, "immediate root refused");
        assert_eq!(rt_array_free_deep(RuntimeValue::NIL), 0, "nil root refused");
        let a = rt_array_new(4);
        assert!(rt_array_push(a, mkstr("freed exactly once by the deep path, unique")));
        assert_eq!(rt_array_free_deep(a), 1);
        let after_first = rt_heap_registry_count();
        assert_eq!(rt_array_free_deep(a), 0, "double deep-free refused");
        assert_eq!(rt_heap_registry_count(), after_first, "refusal does not decrement");
    }
}
