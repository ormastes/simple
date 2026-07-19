//! Collection types: Array, Tuple, String and their SFFI functions.
//! Dict SFFI functions are in the dict module.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::sync::OnceLock;

use super::byte_kernels::{
    avx2_byte_find, avx2_byte_rfind, byte_split_ranges_for_tier, neon_byte_find, neon_byte_rfind, scalar_byte_find,
    scalar_byte_rfind, scalar_byte_split_ranges,
};
use super::core::RuntimeValue;
use super::dict::RuntimeDict;
use super::heap::{
    gc_flags, get_typed_ptr, get_typed_ptr_mut, register_heap_ptr, unregister_heap_ptr, HeapHeader, HeapObjectType,
};
use super::objects::rt_closure_func_ptr;
use super::primitive_sort;
use simple_simd::{active_simd_tier, SimdTier};

thread_local! {
    static U8_ARRAY_SCRATCH: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
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

fn collection_providers() -> CollectionProviders {
    providers_for_tier(active_simd_tier())
}

pub(crate) fn active_collection_simd_tier() -> SimdTier {
    collection_providers().simd_tier
}

pub(crate) fn clear_collection_provider_cache() {}

#[inline]
fn compare_runtime_values(a: &RuntimeValue, b: &RuntimeValue) -> Ordering {
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

static SHORT_STRING_CACHE: OnceLock<[RuntimeValue; 257]> = OnceLock::new();

fn rt_string_new_uncached(bytes: *const u8, len: u64) -> RuntimeValue {
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

fn short_string_cache() -> &'static [RuntimeValue; 257] {
    SHORT_STRING_CACHE.get_or_init(|| {
        std::array::from_fn(|index| {
            if index == 0 {
                rt_string_new_uncached(std::ptr::null(), 0)
            } else {
                let byte = [(index - 1) as u8];
                rt_string_new_uncached(byte.as_ptr(), 1)
            }
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

        (*ptr).header = HeapHeader::new(HeapObjectType::Array, header_size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;
        (*ptr).data = data;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
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

        (*ptr).header = HeapHeader::new(HeapObjectType::Array, header_size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;
        (*ptr).data = data;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
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

        (*ptr).header = HeapHeader::new(HeapObjectType::Array, header_size as u32);
        (*ptr).header.gc_flags |= gc_flags::BYTE_PACKED;
        (*ptr).len = 0;
        (*ptr).capacity = capacity;
        (*ptr).data = data;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
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

#[no_mangle]
pub extern "C" fn rt_array_data_ptr_u8(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);
    unsafe {
        if (*arr).is_byte_packed() {
            return (*arr).data as i64;
        }
        let len = (*arr).len as usize;
        let slice = (*arr).as_slice();
        U8_ARRAY_SCRATCH.with(|scratch| {
            let mut bytes = scratch.borrow_mut();
            bytes.clear();
            bytes.reserve(len);
            for value in slice.iter().take(len) {
                if value.is_int() {
                    bytes.push((value.as_int() & 0xff) as u8);
                } else {
                    bytes.push((value.to_raw() & 0xff) as u8);
                }
            }
            bytes.as_ptr() as i64
        })
    }
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

/// Clear all elements from an array
#[no_mangle]
pub extern "C" fn rt_array_clear(array: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        (*arr).len = 0;
        true
    }
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
            std::alloc::dealloc((*ptr).data as *mut u8, data_layout);
            (*ptr).data = std::ptr::null_mut();
        }
        let header_layout = std::alloc::Layout::from_size_align(std::mem::size_of::<RuntimeArray>(), 8).unwrap();
        unregister_heap_ptr(ptr as *mut HeapHeader);
        std::alloc::dealloc(ptr as *mut u8, header_layout);
    }
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

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
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

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
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

/// Get a single character from a string at the given index.
/// Returns the character as a new single-character string (RuntimeValue).
/// Returns nil (TAG_SPECIAL 3) if index is out of bounds.
#[no_mangle]
pub extern "C" fn rt_string_char_at(string: RuntimeValue, index: i64) -> RuntimeValue {
    let len = rt_string_len(string);
    if len < 0 || index < 0 || index >= len {
        return RuntimeValue::NIL;
    }

    let data = rt_string_data(string);
    if data.is_null() {
        return RuntimeValue::NIL;
    }

    unsafe {
        let bytes = std::slice::from_raw_parts(data, len as usize);
        // Find the character at the given index (UTF-8 aware)
        let s = std::str::from_utf8_unchecked(bytes);
        if let Some(c) = s.chars().nth(index as usize) {
            let mut buf = [0u8; 4];
            let char_str = c.encode_utf8(&mut buf);
            rt_string_new(char_str.as_ptr(), char_str.len() as u64)
        } else {
            RuntimeValue::NIL
        }
    }
}

/// Return the Unicode code point at the given character index, or 0 if missing.
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
        let s = std::str::from_utf8_unchecked(bytes);
        s.chars().nth(index as usize).map_or(0, |c| c as i64)
    }
}

/// Compiled symbol for `text.from_char_code(code)`.
#[no_mangle]
pub extern "C" fn text_dot_from_char_code(code: i64) -> RuntimeValue {
    let Some(ch) = char::from_u32(code as u32) else {
        return RuntimeValue::NIL;
    };
    let mut buf = [0u8; 4];
    let s = ch.encode_utf8(&mut buf);
    unsafe { rt_string_new(s.as_ptr(), s.len() as u64) }
}

#[no_mangle]
pub extern "C" fn rt_text_find(haystack: RuntimeValue, needle: RuntimeValue, start: i64) -> i64 {
    if start < 0 {
        return -1;
    }
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
        let elem = rt_array_get(array, i);
        let elem_len = rt_string_len(elem);
        if elem_len > 0 {
            let elem_data = rt_string_data(elem);
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
        return RuntimeValue::NIL;
    }

    if needle_len == 0 {
        // Empty needle: return Some(0)
        let payload = RuntimeValue::from_int(0);
        return super::objects::rt_enum_new(
            0,
            {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                "Some".hash(&mut hasher);
                (hasher.finish() & 0xFFFFFFFF) as u32
            },
            payload,
        );
    }

    if needle_len > str_len {
        return RuntimeValue::NIL;
    }

    let str_data = rt_string_data(string);
    let needle_data = rt_string_data(needle);

    if str_data.is_null() || needle_data.is_null() {
        return RuntimeValue::NIL;
    }

    unsafe {
        let haystack = std::str::from_utf8_unchecked(std::slice::from_raw_parts(str_data, str_len as usize));
        let needle_str = std::str::from_utf8_unchecked(std::slice::from_raw_parts(needle_data, needle_len as usize));
        match haystack.find(needle_str) {
            Some(idx) => {
                let payload = RuntimeValue::from_int(idx as i64);
                super::objects::rt_enum_new(
                    0,
                    {
                        use std::collections::hash_map::DefaultHasher;
                        use std::hash::{Hash, Hasher};
                        let mut hasher = DefaultHasher::new();
                        "Some".hash(&mut hasher);
                        (hasher.finish() & 0xFFFFFFFF) as u32
                    },
                    payload,
                )
            }
            None => RuntimeValue::NIL,
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
            if item.is_float() && item.as_float() == 0.0 {
                return 0;
            }
        }
        1
    }
}

#[no_mangle]
pub extern "C" fn rt_array_all(array: RuntimeValue) -> i64 {
    rt_array_all_truthy(array)
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
            if item.is_float() && item.as_float() == 0.0 {
                continue;
            }
            return 1;
        }
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_array_any(array: RuntimeValue) -> i64 {
    rt_array_any_truthy(array)
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
