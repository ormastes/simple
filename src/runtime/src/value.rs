//! Runtime value representation for compiled code.
//!
//! This module provides a tagged pointer value representation that can be
//! used by the code generator. It mirrors the interpreter's `Value` enum
//! but uses a compact 64-bit representation suitable for machine code.
//!
//! ## Tagged Pointer Layout (64-bit)
//!
//! ```text
//! | Payload (61 bits)                              | Tag (3 bits) |
//! ```
//!
//! Tag values:
//! - 000 (0): Signed integer (61-bit, sign-extended)
//! - 001 (1): Heap pointer to object
//! - 010 (2): Float (uses NaN-boxing trick)
//! - 011 (3): Special values (nil, bool, symbol ID)
//! - 100-111: Reserved for future use

use std::cell::RefCell;
use std::sync::{mpsc, Arc, Mutex};
use std::time::Duration;

use crate::concurrency::{spawn_actor, ActorHandle, Message};

/// Tag bits for the tagged pointer representation
pub mod tags {
    pub const TAG_MASK: u64 = 0b111;
    pub const TAG_INT: u64 = 0b000;
    pub const TAG_HEAP: u64 = 0b001;
    pub const TAG_FLOAT: u64 = 0b010;
    pub const TAG_SPECIAL: u64 = 0b011;

    // Special value subtypes (encoded in payload)
    pub const SPECIAL_NIL: u64 = 0;
    pub const SPECIAL_TRUE: u64 = 1;
    pub const SPECIAL_FALSE: u64 = 2;
    // Symbol IDs start at 3
}

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

impl HeapHeader {
    pub fn new(object_type: HeapObjectType, size: u32) -> Self {
        Self {
            object_type,
            gc_flags: 0,
            reserved: 0,
            size,
        }
    }
}

/// A 64-bit tagged runtime value.
///
/// This is the primary value type used in compiled code. It can represent
/// all Simple Language values in a single 64-bit word, with heap-allocated
/// objects stored as tagged pointers.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct RuntimeValue(u64);

impl std::fmt::Debug for RuntimeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.tag() {
            tags::TAG_INT => write!(f, "RuntimeValue::Int({})", self.as_int()),
            tags::TAG_FLOAT => write!(f, "RuntimeValue::Float({})", self.as_float()),
            tags::TAG_SPECIAL => {
                let payload = self.payload();
                match payload {
                    tags::SPECIAL_NIL => write!(f, "RuntimeValue::Nil"),
                    tags::SPECIAL_TRUE => write!(f, "RuntimeValue::Bool(true)"),
                    tags::SPECIAL_FALSE => write!(f, "RuntimeValue::Bool(false)"),
                    _ => write!(f, "RuntimeValue::Symbol({})", payload),
                }
            }
            tags::TAG_HEAP => write!(f, "RuntimeValue::Heap({:p})", self.as_heap_ptr()),
            _ => write!(f, "RuntimeValue(0x{:016x})", self.0),
        }
    }
}

impl PartialEq for RuntimeValue {
    fn eq(&self, other: &Self) -> bool {
        // For floats, need to handle NaN specially
        if self.tag() == tags::TAG_FLOAT && other.tag() == tags::TAG_FLOAT {
            self.as_float() == other.as_float()
        } else {
            self.0 == other.0
        }
    }
}

impl Eq for RuntimeValue {}

thread_local! {
    static CURRENT_ACTOR_INBOX: RefCell<Option<Arc<Mutex<mpsc::Receiver<Message>>>>> = RefCell::new(None);
    static CURRENT_ACTOR_OUTBOX: RefCell<Option<mpsc::Sender<Message>>> = RefCell::new(None);
    static GENERATOR_YIELDS: RefCell<Option<Vec<RuntimeValue>>> = RefCell::new(None);
}

impl RuntimeValue {
    /// The NIL value constant
    pub const NIL: RuntimeValue = RuntimeValue::from_special(tags::SPECIAL_NIL);
    /// The TRUE value constant
    pub const TRUE: RuntimeValue = RuntimeValue::from_special(tags::SPECIAL_TRUE);
    /// The FALSE value constant
    pub const FALSE: RuntimeValue = RuntimeValue::from_special(tags::SPECIAL_FALSE);

    /// Create a RuntimeValue from raw bits
    #[inline]
    pub const fn from_raw(bits: u64) -> Self {
        Self(bits)
    }

    /// Get the raw bits of this value
    #[inline]
    pub const fn to_raw(self) -> u64 {
        self.0
    }

    /// Get the tag bits (lowest 3 bits)
    #[inline]
    pub const fn tag(self) -> u64 {
        self.0 & tags::TAG_MASK
    }

    /// Get the payload (upper 61 bits)
    #[inline]
    pub const fn payload(self) -> u64 {
        self.0 >> 3
    }

    /// Create a value from tag and payload
    #[inline]
    const fn from_tag_payload(tag: u64, payload: u64) -> Self {
        Self((payload << 3) | tag)
    }

    /// Create a special value (nil, bool, symbol)
    #[inline]
    const fn from_special(payload: u64) -> Self {
        Self::from_tag_payload(tags::TAG_SPECIAL, payload)
    }

    // =========================================================================
    // Integer operations
    // =========================================================================

    /// Create an integer value
    ///
    /// Note: Only 61-bit signed integers can be stored directly.
    /// Larger integers would need heap allocation.
    #[inline]
    pub fn from_int(i: i64) -> Self {
        // Sign-extend to fit in 61 bits
        // The tag is 0, so we just shift
        Self((i as u64) << 3)
    }

    /// Check if this is an integer
    #[inline]
    pub const fn is_int(self) -> bool {
        self.tag() == tags::TAG_INT
    }

    /// Get the integer value (undefined behavior if not an int)
    #[inline]
    pub fn as_int(self) -> i64 {
        // Sign-extend from 61 bits
        (self.0 as i64) >> 3
    }

    // =========================================================================
    // Float operations
    // =========================================================================

    /// Create a float value
    #[inline]
    pub fn from_float(f: f64) -> Self {
        // Store float bits in the upper 61 bits
        // We lose 3 bits of precision but that's acceptable for most uses
        let bits = f.to_bits();
        Self::from_tag_payload(tags::TAG_FLOAT, bits >> 3)
    }

    /// Check if this is a float
    #[inline]
    pub const fn is_float(self) -> bool {
        self.tag() == tags::TAG_FLOAT
    }

    /// Get the float value (undefined behavior if not a float)
    #[inline]
    pub fn as_float(self) -> f64 {
        f64::from_bits(self.payload() << 3)
    }

    // =========================================================================
    // Boolean operations
    // =========================================================================

    /// Create a boolean value
    #[inline]
    pub const fn from_bool(b: bool) -> Self {
        if b {
            Self::TRUE
        } else {
            Self::FALSE
        }
    }

    /// Check if this is a boolean
    #[inline]
    pub const fn is_bool(self) -> bool {
        self.tag() == tags::TAG_SPECIAL
            && (self.payload() == tags::SPECIAL_TRUE || self.payload() == tags::SPECIAL_FALSE)
    }

    /// Get the boolean value (returns false if not a bool)
    #[inline]
    pub const fn as_bool(self) -> bool {
        self.tag() == tags::TAG_SPECIAL && self.payload() == tags::SPECIAL_TRUE
    }

    // =========================================================================
    // Nil operations
    // =========================================================================

    /// Check if this is nil
    #[inline]
    pub const fn is_nil(self) -> bool {
        self.0 == Self::NIL.0
    }

    // =========================================================================
    // Heap pointer operations
    // =========================================================================

    /// Create a heap pointer value
    ///
    /// # Safety
    /// The pointer must be valid and properly aligned.
    #[inline]
    pub unsafe fn from_heap_ptr(ptr: *mut HeapHeader) -> Self {
        debug_assert!(!ptr.is_null());
        debug_assert!(ptr as u64 & tags::TAG_MASK == 0, "pointer not aligned");
        Self((ptr as u64) | tags::TAG_HEAP)
    }

    /// Check if this is a heap pointer
    #[inline]
    pub const fn is_heap(self) -> bool {
        self.tag() == tags::TAG_HEAP
    }

    /// Get the heap pointer (null if not a heap value)
    #[inline]
    pub fn as_heap_ptr(self) -> *mut HeapHeader {
        if self.is_heap() {
            (self.0 & !tags::TAG_MASK) as *mut HeapHeader
        } else {
            std::ptr::null_mut()
        }
    }

    /// Get the heap object type (returns None if not a heap value)
    #[inline]
    pub fn heap_type(self) -> Option<HeapObjectType> {
        if self.is_heap() {
            let ptr = self.as_heap_ptr();
            if !ptr.is_null() {
                Some(unsafe { (*ptr).object_type })
            } else {
                None
            }
        } else {
            None
        }
    }

    // =========================================================================
    // Truthiness
    // =========================================================================

    /// Check if this value is "truthy" (non-zero, non-nil, non-empty)
    #[inline]
    pub fn truthy(self) -> bool {
        match self.tag() {
            tags::TAG_INT => self.as_int() != 0,
            tags::TAG_FLOAT => self.as_float() != 0.0,
            tags::TAG_SPECIAL => self.payload() == tags::SPECIAL_TRUE,
            tags::TAG_HEAP => {
                // Heap objects are truthy if they exist
                // For arrays/strings, should check if empty
                !self.as_heap_ptr().is_null()
            }
            _ => false,
        }
    }

    // =========================================================================
    // Type checking
    // =========================================================================

    /// Get a string representation of this value's type
    pub fn type_name(self) -> &'static str {
        match self.tag() {
            tags::TAG_INT => "int",
            tags::TAG_FLOAT => "float",
            tags::TAG_SPECIAL => {
                let payload = self.payload();
                match payload {
                    tags::SPECIAL_NIL => "nil",
                    tags::SPECIAL_TRUE | tags::SPECIAL_FALSE => "bool",
                    _ => "symbol",
                }
            }
            tags::TAG_HEAP => match self.heap_type() {
                Some(HeapObjectType::String) => "string",
                Some(HeapObjectType::Array) => "array",
                Some(HeapObjectType::Dict) => "dict",
                Some(HeapObjectType::Tuple) => "tuple",
                Some(HeapObjectType::Object) => "object",
                Some(HeapObjectType::Closure) => "closure",
                Some(HeapObjectType::Enum) => "enum",
                Some(HeapObjectType::Future) => "future",
                Some(HeapObjectType::Generator) => "generator",
                Some(HeapObjectType::Actor) => "actor",
                Some(HeapObjectType::Unique) => "unique",
                Some(HeapObjectType::Shared) => "shared",
                Some(HeapObjectType::Borrow) => "borrow",
                None => "null",
            },
            _ => "unknown",
        }
    }
}

// ============================================================================
// Heap-allocated structures
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

/// A heap-allocated array
#[repr(C)]
pub struct RuntimeArray {
    pub header: HeapHeader,
    /// Number of elements
    pub len: u64,
    /// Capacity (allocated slots)
    pub capacity: u64,
    // Followed by RuntimeValue elements
}

impl RuntimeArray {
    /// Get the elements as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeArray was properly allocated.
    pub unsafe fn as_slice(&self) -> &[RuntimeValue] {
        let data_ptr = (self as *const Self).add(1) as *const RuntimeValue;
        std::slice::from_raw_parts(data_ptr, self.len as usize)
    }

    /// Get the elements as a mutable slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeArray was properly allocated.
    pub unsafe fn as_mut_slice(&mut self) -> &mut [RuntimeValue] {
        let data_ptr = (self as *mut Self).add(1) as *mut RuntimeValue;
        std::slice::from_raw_parts_mut(data_ptr, self.len as usize)
    }
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

/// A heap-allocated closure
#[repr(C)]
pub struct RuntimeClosure {
    pub header: HeapHeader,
    /// Pointer to the compiled function
    pub func_ptr: *const u8,
    /// Number of captured variables
    pub capture_count: u32,
    /// Reserved for alignment
    pub reserved: u32,
    // Followed by captured RuntimeValue elements
}

impl RuntimeClosure {
    /// Get the captured values as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeClosure was properly allocated.
    pub unsafe fn captures(&self) -> &[RuntimeValue] {
        let data_ptr = (self as *const Self).add(1) as *const RuntimeValue;
        std::slice::from_raw_parts(data_ptr, self.capture_count as usize)
    }
}

/// A heap-allocated object (class/struct instance)
#[repr(C)]
pub struct RuntimeObject {
    pub header: HeapHeader,
    /// Class ID (index into class metadata table)
    pub class_id: u32,
    /// Number of fields
    pub field_count: u32,
    // Followed by field RuntimeValue elements (indexed by field order)
}

impl RuntimeObject {
    /// Get the fields as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeObject was properly allocated.
    pub unsafe fn fields(&self) -> &[RuntimeValue] {
        let data_ptr = (self as *const Self).add(1) as *const RuntimeValue;
        std::slice::from_raw_parts(data_ptr, self.field_count as usize)
    }

    /// Get the fields as a mutable slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeObject was properly allocated.
    pub unsafe fn fields_mut(&mut self) -> &mut [RuntimeValue] {
        let data_ptr = (self as *mut Self).add(1) as *mut RuntimeValue;
        std::slice::from_raw_parts_mut(data_ptr, self.field_count as usize)
    }
}

/// A heap-allocated enum variant
#[repr(C)]
pub struct RuntimeEnum {
    pub header: HeapHeader,
    /// Enum type ID
    pub enum_id: u32,
    /// Variant discriminant
    pub discriminant: u32,
    /// Payload (NIL if no payload)
    pub payload: RuntimeValue,
}

// ============================================================================
// Default implementations
// ============================================================================

impl Default for RuntimeValue {
    fn default() -> Self {
        Self::NIL
    }
}

// ============================================================================
// FFI-safe functions for runtime calls
// ============================================================================

/// Create an integer RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_int(i: i64) -> RuntimeValue {
    RuntimeValue::from_int(i)
}

/// Create a float RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_float(f: f64) -> RuntimeValue {
    RuntimeValue::from_float(f)
}

/// Create a bool RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_bool(b: bool) -> RuntimeValue {
    RuntimeValue::from_bool(b)
}

/// Get the NIL value (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_nil() -> RuntimeValue {
    RuntimeValue::NIL
}

/// Extract integer from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_int(v: RuntimeValue) -> i64 {
    v.as_int()
}

/// Extract float from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_float(v: RuntimeValue) -> f64 {
    v.as_float()
}

/// Extract bool from RuntimeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_as_bool(v: RuntimeValue) -> bool {
    v.as_bool()
}

/// Check if value is truthy (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_truthy(v: RuntimeValue) -> bool {
    v.truthy()
}

/// Check if value is nil (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_nil(v: RuntimeValue) -> bool {
    v.is_nil()
}

/// Check if value is int (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_int(v: RuntimeValue) -> bool {
    v.is_int()
}

/// Check if value is float (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_float(v: RuntimeValue) -> bool {
    v.is_float()
}

/// Check if value is bool (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_bool(v: RuntimeValue) -> bool {
    v.is_bool()
}

/// Check if value is heap pointer (FFI-safe)
#[no_mangle]
pub extern "C" fn rt_value_is_heap(v: RuntimeValue) -> bool {
    v.is_heap()
}

// ============================================================================
// Raw memory allocation (FFI-safe, zero-cost abstraction support)
// ============================================================================

/// Allocate raw memory with 8-byte alignment (like malloc)
/// Returns a pointer to the allocated memory, or null on failure.
/// Used for zero-cost struct allocation in codegen.
#[no_mangle]
pub extern "C" fn rt_alloc(size: u64) -> *mut u8 {
    if size == 0 {
        return std::ptr::null_mut();
    }
    let layout = std::alloc::Layout::from_size_align(size as usize, 8).unwrap();
    unsafe { std::alloc::alloc_zeroed(layout) }
}

/// Free memory allocated by rt_alloc
#[no_mangle]
pub extern "C" fn rt_free(ptr: *mut u8, size: u64) {
    if ptr.is_null() || size == 0 {
        return;
    }
    let layout = std::alloc::Layout::from_size_align(size as usize, 8).unwrap();
    unsafe {
        std::alloc::dealloc(ptr, layout);
    }
}

/// Convert raw pointer to RuntimeValue (for struct pointers)
/// The pointer is stored as a heap-tagged value.
#[no_mangle]
pub extern "C" fn rt_ptr_to_value(ptr: *mut u8) -> RuntimeValue {
    if ptr.is_null() {
        return RuntimeValue::NIL;
    }
    unsafe { RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader) }
}

/// Extract raw pointer from RuntimeValue
#[no_mangle]
pub extern "C" fn rt_value_to_ptr(v: RuntimeValue) -> *mut u8 {
    if !v.is_heap() {
        return std::ptr::null_mut();
    }
    v.as_heap_ptr() as *mut u8
}

// ============================================================================
// Collection allocation and manipulation (FFI-safe)
// ============================================================================

/// Allocate a new array with the given capacity
///
/// # Safety
/// Returns a RuntimeValue with a heap-allocated array. The caller must ensure
/// the value is properly managed by the GC.
#[no_mangle]
pub extern "C" fn rt_array_new(capacity: u64) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeArray>()
        + capacity as usize * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeArray;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Array, size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the length of an array
#[no_mangle]
pub extern "C" fn rt_array_len(array: RuntimeValue) -> i64 {
    if !array.is_heap() {
        return -1;
    }
    let ptr = array.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Array {
            return -1;
        }
        (*(ptr as *const RuntimeArray)).len as i64
    }
}

/// Get an element from an array
#[no_mangle]
pub extern "C" fn rt_array_get(array: RuntimeValue, index: i64) -> RuntimeValue {
    if !array.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = array.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Array {
            return RuntimeValue::NIL;
        }
        let arr = ptr as *const RuntimeArray;
        let len = (*arr).len as i64;

        // Handle negative indices
        let idx = if index < 0 { len + index } else { index };
        if idx < 0 || idx >= len {
            return RuntimeValue::NIL;
        }

        (*arr).as_slice()[idx as usize]
    }
}

/// Set an element in an array
#[no_mangle]
pub extern "C" fn rt_array_set(array: RuntimeValue, index: i64, value: RuntimeValue) -> bool {
    if !array.is_heap() {
        return false;
    }
    let ptr = array.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Array {
            return false;
        }
        let arr = ptr as *mut RuntimeArray;
        let len = (*arr).len as i64;

        // Handle negative indices
        let idx = if index < 0 { len + index } else { index };
        if idx < 0 || idx >= len {
            return false;
        }

        (*arr).as_mut_slice()[idx as usize] = value;
        true
    }
}

/// Push an element to an array
#[no_mangle]
pub extern "C" fn rt_array_push(array: RuntimeValue, value: RuntimeValue) -> bool {
    if !array.is_heap() {
        return false;
    }
    let ptr = array.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Array {
            return false;
        }
        let arr = ptr as *mut RuntimeArray;
        if (*arr).len >= (*arr).capacity {
            // Array is full - would need to reallocate
            return false;
        }

        let data_ptr = (arr.add(1)) as *mut RuntimeValue;
        *data_ptr.add((*arr).len as usize) = value;
        (*arr).len += 1;
        true
    }
}

/// Pop an element from an array
#[no_mangle]
pub extern "C" fn rt_array_pop(array: RuntimeValue) -> RuntimeValue {
    if !array.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = array.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Array {
            return RuntimeValue::NIL;
        }
        let arr = ptr as *mut RuntimeArray;
        if (*arr).len == 0 {
            return RuntimeValue::NIL;
        }

        (*arr).len -= 1;
        let data_ptr = (arr.add(1)) as *const RuntimeValue;
        *data_ptr.add((*arr).len as usize)
    }
}

/// Allocate a new tuple with the given length
#[no_mangle]
pub extern "C" fn rt_tuple_new(len: u64) -> RuntimeValue {
    let size =
        std::mem::size_of::<RuntimeTuple>() + len as usize * std::mem::size_of::<RuntimeValue>();
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
    if !tuple.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = tuple.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Tuple {
            return RuntimeValue::NIL;
        }
        let tup = ptr as *const RuntimeTuple;
        if index >= (*tup).len {
            return RuntimeValue::NIL;
        }

        (*tup).as_slice()[index as usize]
    }
}

/// Set an element in a tuple (used during construction)
#[no_mangle]
pub extern "C" fn rt_tuple_set(tuple: RuntimeValue, index: u64, value: RuntimeValue) -> bool {
    if !tuple.is_heap() {
        return false;
    }
    let ptr = tuple.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Tuple {
            return false;
        }
        let tup = ptr as *mut RuntimeTuple;
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
    if !tuple.is_heap() {
        return -1;
    }
    let ptr = tuple.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Tuple {
            return -1;
        }
        (*(ptr as *const RuntimeTuple)).len as i64
    }
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

    let size = std::mem::size_of::<RuntimeString>() + len as usize;
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc(layout) as *mut RuntimeString;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::String, size as u32);
        (*ptr).len = len;
        (*ptr).hash = 0; // TODO: Compute hash

        // Copy string data
        if len > 0 {
            let data_ptr = ptr.add(1) as *mut u8;
            std::ptr::copy_nonoverlapping(bytes, data_ptr, len as usize);
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the length of a string in bytes
#[no_mangle]
pub extern "C" fn rt_string_len(string: RuntimeValue) -> i64 {
    if !string.is_heap() {
        return -1;
    }
    let ptr = string.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::String {
            return -1;
        }
        (*(ptr as *const RuntimeString)).len as i64
    }
}

/// Get a pointer to the string data
#[no_mangle]
pub extern "C" fn rt_string_data(string: RuntimeValue) -> *const u8 {
    if !string.is_heap() {
        return std::ptr::null();
    }
    let ptr = string.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::String {
            return std::ptr::null();
        }
        let str_ptr = ptr as *const RuntimeString;
        str_ptr.add(1) as *const u8
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
    let size = std::mem::size_of::<RuntimeString>() + total_len as usize;
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc(layout) as *mut RuntimeString;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::String, size as u32);
        (*ptr).len = total_len;
        (*ptr).hash = 0;

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

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Index into a collection (array, tuple, string, dict)
/// Returns NIL if out of bounds or wrong type
#[no_mangle]
pub extern "C" fn rt_index_get(collection: RuntimeValue, index: RuntimeValue) -> RuntimeValue {
    if !collection.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = collection.as_heap_ptr();
    unsafe {
        match (*ptr).object_type {
            HeapObjectType::Array => {
                if index.is_int() {
                    rt_array_get(collection, index.as_int())
                } else {
                    RuntimeValue::NIL
                }
            }
            HeapObjectType::Tuple => {
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
            HeapObjectType::String => {
                // String indexing returns character code
                if index.is_int() {
                    let str_ptr = ptr as *const RuntimeString;
                    let len = (*str_ptr).len as i64;
                    let idx = index.as_int();
                    let idx = if idx < 0 { len + idx } else { idx };
                    if idx < 0 || idx >= len {
                        RuntimeValue::NIL
                    } else {
                        let data = str_ptr.add(1) as *const u8;
                        RuntimeValue::from_int(*data.add(idx as usize) as i64)
                    }
                } else {
                    RuntimeValue::NIL
                }
            }
            // Dict indexing would go here
            _ => RuntimeValue::NIL,
        }
    }
}

/// Set a value in a collection (array, dict)
/// Returns true on success, false on error
#[no_mangle]
pub extern "C" fn rt_index_set(
    collection: RuntimeValue,
    index: RuntimeValue,
    value: RuntimeValue,
) -> bool {
    if !collection.is_heap() {
        return false;
    }

    let ptr = collection.as_heap_ptr();
    unsafe {
        match (*ptr).object_type {
            HeapObjectType::Array => {
                if index.is_int() {
                    rt_array_set(collection, index.as_int(), value)
                } else {
                    false
                }
            }
            // Dict indexing would go here
            _ => false,
        }
    }
}

// ============================================================================
// Object allocation and manipulation (FFI-safe)
// ============================================================================

/// Allocate a new object with the given number of fields
///
/// # Safety
/// Returns a RuntimeValue with a heap-allocated object. The caller must ensure
/// the value is properly managed by the GC.
#[no_mangle]
pub extern "C" fn rt_object_new(class_id: u32, field_count: u32) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeObject>()
        + field_count as usize * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeObject;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Object, size as u32);
        (*ptr).class_id = class_id;
        (*ptr).field_count = field_count;

        // Initialize all fields to NIL
        let fields = (*ptr).fields_mut();
        for field in fields {
            *field = RuntimeValue::NIL;
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get a field from an object by index
#[no_mangle]
pub extern "C" fn rt_object_field_get(object: RuntimeValue, field_index: u32) -> RuntimeValue {
    if !object.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = object.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Object {
            return RuntimeValue::NIL;
        }
        let obj = ptr as *const RuntimeObject;
        if field_index >= (*obj).field_count {
            return RuntimeValue::NIL;
        }

        (*obj).fields()[field_index as usize]
    }
}

/// Set a field on an object by index
#[no_mangle]
pub extern "C" fn rt_object_field_set(
    object: RuntimeValue,
    field_index: u32,
    value: RuntimeValue,
) -> bool {
    if !object.is_heap() {
        return false;
    }
    let ptr = object.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Object {
            return false;
        }
        let obj = ptr as *mut RuntimeObject;
        if field_index >= (*obj).field_count {
            return false;
        }

        (*obj).fields_mut()[field_index as usize] = value;
        true
    }
}

/// Get the class ID of an object
#[no_mangle]
pub extern "C" fn rt_object_class_id(object: RuntimeValue) -> i64 {
    if !object.is_heap() {
        return -1;
    }
    let ptr = object.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Object {
            return -1;
        }
        (*(ptr as *const RuntimeObject)).class_id as i64
    }
}

/// Get the field count of an object
#[no_mangle]
pub extern "C" fn rt_object_field_count(object: RuntimeValue) -> i64 {
    if !object.is_heap() {
        return -1;
    }
    let ptr = object.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Object {
            return -1;
        }
        (*(ptr as *const RuntimeObject)).field_count as i64
    }
}

// ============================================================================
// Closure allocation and manipulation (FFI-safe)
// ============================================================================

/// Allocate a new closure with the given function pointer and captures
#[no_mangle]
pub extern "C" fn rt_closure_new(func_ptr: *const u8, capture_count: u32) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeClosure>()
        + capture_count as usize * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeClosure;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Closure, size as u32);
        (*ptr).func_ptr = func_ptr;
        (*ptr).capture_count = capture_count;
        (*ptr).reserved = 0;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Set a captured variable in a closure
#[no_mangle]
pub extern "C" fn rt_closure_set_capture(
    closure: RuntimeValue,
    index: u32,
    value: RuntimeValue,
) -> bool {
    if !closure.is_heap() {
        return false;
    }
    let ptr = closure.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Closure {
            return false;
        }
        let clos = ptr as *mut RuntimeClosure;
        if index >= (*clos).capture_count {
            return false;
        }

        let data_ptr = (clos.add(1)) as *mut RuntimeValue;
        *data_ptr.add(index as usize) = value;
        true
    }
}

/// Get a captured variable from a closure
#[no_mangle]
pub extern "C" fn rt_closure_get_capture(closure: RuntimeValue, index: u32) -> RuntimeValue {
    if !closure.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = closure.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Closure {
            return RuntimeValue::NIL;
        }
        let clos = ptr as *const RuntimeClosure;
        if index >= (*clos).capture_count {
            return RuntimeValue::NIL;
        }

        (*clos).captures()[index as usize]
    }
}

/// Get the function pointer from a closure
#[no_mangle]
pub extern "C" fn rt_closure_func_ptr(closure: RuntimeValue) -> *const u8 {
    if !closure.is_heap() {
        return std::ptr::null();
    }
    let ptr = closure.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Closure {
            return std::ptr::null();
        }
        (*(ptr as *const RuntimeClosure)).func_ptr
    }
}

// ============================================================================
// Enum allocation (FFI-safe)
// ============================================================================

/// Allocate a new enum value
#[no_mangle]
pub extern "C" fn rt_enum_new(
    enum_id: u32,
    discriminant: u32,
    payload: RuntimeValue,
) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeEnum>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc(layout) as *mut RuntimeEnum;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Enum, size as u32);
        (*ptr).enum_id = enum_id;
        (*ptr).discriminant = discriminant;
        (*ptr).payload = payload;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the discriminant of an enum value
#[no_mangle]
pub extern "C" fn rt_enum_discriminant(value: RuntimeValue) -> i64 {
    if !value.is_heap() {
        return -1;
    }
    let ptr = value.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Enum {
            return -1;
        }
        (*(ptr as *const RuntimeEnum)).discriminant as i64
    }
}

/// Get the payload of an enum value
#[no_mangle]
pub extern "C" fn rt_enum_payload(value: RuntimeValue) -> RuntimeValue {
    if !value.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = value.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Enum {
            return RuntimeValue::NIL;
        }
        (*(ptr as *const RuntimeEnum)).payload
    }
}

// ============================================================================
// Dict/HashMap allocation (FFI-safe)
// ============================================================================

/// A heap-allocated dictionary (hash map)
#[repr(C)]
pub struct RuntimeDict {
    pub header: HeapHeader,
    /// Number of entries
    pub len: u64,
    /// Capacity (number of slots)
    pub capacity: u64,
    // Followed by key-value pairs as (RuntimeValue, RuntimeValue)
}

/// Allocate a new dictionary with the given capacity
#[no_mangle]
pub extern "C" fn rt_dict_new(capacity: u64) -> RuntimeValue {
    let capacity = capacity.max(8); // Minimum capacity
    let size = std::mem::size_of::<RuntimeDict>()
        + capacity as usize * 2 * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeDict;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Dict, size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the length of a dictionary
#[no_mangle]
pub extern "C" fn rt_dict_len(dict: RuntimeValue) -> i64 {
    if !dict.is_heap() {
        return -1;
    }
    let ptr = dict.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Dict {
            return -1;
        }
        (*(ptr as *const RuntimeDict)).len as i64
    }
}

/// Simple hash function for RuntimeValue
fn hash_value(v: RuntimeValue) -> u64 {
    // Use the raw bits for hashing
    let bits = v.to_raw();
    // Simple FNV-1a-like hash
    let mut hash = 0xcbf29ce484222325u64;
    for i in 0..8 {
        hash ^= (bits >> (i * 8)) & 0xff;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

/// Get a value from a dictionary by key
#[no_mangle]
pub extern "C" fn rt_dict_get(dict: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    if !dict.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = dict.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Dict {
            return RuntimeValue::NIL;
        }
        let d = ptr as *const RuntimeDict;
        let capacity = (*d).capacity;
        if capacity == 0 {
            return RuntimeValue::NIL;
        }

        let hash = hash_value(key);
        let data_ptr = (d.add(1)) as *const RuntimeValue;

        // Linear probing
        for i in 0..capacity {
            let idx = ((hash + i) % capacity) as usize;
            let k = *data_ptr.add(idx * 2);
            if k.is_nil() {
                return RuntimeValue::NIL; // Key not found
            }
            if k == key {
                return *data_ptr.add(idx * 2 + 1);
            }
        }
        RuntimeValue::NIL
    }
}

/// Set a value in a dictionary
#[no_mangle]
pub extern "C" fn rt_dict_set(dict: RuntimeValue, key: RuntimeValue, value: RuntimeValue) -> bool {
    if !dict.is_heap() || key.is_nil() {
        return false;
    }
    let ptr = dict.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Dict {
            return false;
        }
        let d = ptr as *mut RuntimeDict;
        let capacity = (*d).capacity;
        if capacity == 0 {
            return false;
        }

        let hash = hash_value(key);
        let data_ptr = (d.add(1)) as *mut RuntimeValue;

        // Linear probing
        for i in 0..capacity {
            let idx = ((hash + i) % capacity) as usize;
            let k = *data_ptr.add(idx * 2);
            if k.is_nil() || k == key {
                if k.is_nil() {
                    (*d).len += 1;
                }
                *data_ptr.add(idx * 2) = key;
                *data_ptr.add(idx * 2 + 1) = value;
                return true;
            }
        }
        false // Dict is full
    }
}

// ============================================================================
// Membership test (FFI-safe)
// ============================================================================

/// Check if a value is contained in a collection (array, dict, string)
/// Returns true (1) if found, false (0) if not
#[no_mangle]
pub extern "C" fn rt_contains(collection: RuntimeValue, value: RuntimeValue) -> u8 {
    if !collection.is_heap() {
        return 0;
    }

    let ptr = collection.as_heap_ptr();
    unsafe {
        match (*ptr).object_type {
            HeapObjectType::Array => {
                let arr = ptr as *const RuntimeArray;
                let slice = (*arr).as_slice();
                for item in slice {
                    if rt_value_eq(*item, value) != 0 {
                        return 1;
                    }
                }
                0
            }
            HeapObjectType::Dict => {
                // For dicts, 'in' checks if the key exists
                let dict = ptr as *const RuntimeDict;
                // Entries are stored after the RuntimeDict header as pairs of RuntimeValue
                let entries_ptr = (dict as *const u8).add(std::mem::size_of::<RuntimeDict>())
                    as *const RuntimeValue;
                for i in 0..(*dict).len as usize {
                    let key = *entries_ptr.add(i * 2);
                    if rt_value_eq(key, value) != 0 {
                        return 1;
                    }
                }
                0
            }
            HeapObjectType::String => {
                // For strings, check if value (as string) is a substring
                // Simplified: only check if value is a single character in the string
                if value.is_int() {
                    let char_code = value.as_int();
                    let str_ptr = ptr as *const RuntimeString;
                    let data = (str_ptr.add(1)) as *const u8;
                    for i in 0..(*str_ptr).len {
                        if *data.add(i as usize) as i64 == char_code {
                            return 1;
                        }
                    }
                }
                0
            }
            _ => 0,
        }
    }
}

/// Compare two RuntimeValues for equality
#[no_mangle]
pub extern "C" fn rt_value_eq(a: RuntimeValue, b: RuntimeValue) -> u8 {
    // Quick check: same raw value
    if a.0 == b.0 {
        return 1;
    }

    // Both must be same type for equality
    if a.is_int() && b.is_int() {
        return if a.as_int() == b.as_int() { 1 } else { 0 };
    }
    if a.is_float() && b.is_float() {
        return if a.as_float() == b.as_float() { 1 } else { 0 };
    }
    if a.is_bool() && b.is_bool() {
        return if a.as_bool() == b.as_bool() { 1 } else { 0 };
    }
    if a.is_nil() && b.is_nil() {
        return 1;
    }

    // For heap objects, compare by content for strings
    if a.is_heap() && b.is_heap() {
        let ptr_a = a.as_heap_ptr();
        let ptr_b = b.as_heap_ptr();
        unsafe {
            if (*ptr_a).object_type == HeapObjectType::String
                && (*ptr_b).object_type == HeapObjectType::String
            {
                let str_a = ptr_a as *const RuntimeString;
                let str_b = ptr_b as *const RuntimeString;
                if (*str_a).len != (*str_b).len {
                    return 0;
                }
                let data_a = (str_a.add(1)) as *const u8;
                let data_b = (str_b.add(1)) as *const u8;
                for i in 0..(*str_a).len {
                    if *data_a.add(i as usize) != *data_b.add(i as usize) {
                        return 0;
                    }
                }
                return 1;
            }
        }
    }

    0
}

// ============================================================================
// Actor operations (FFI-safe)
// ============================================================================

#[repr(C)]
pub struct RuntimeActor {
    pub header: HeapHeader,
    pub handle: ActorHandle,
}

fn alloc_actor(handle: ActorHandle) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeActor>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeActor;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Actor, size as u32);
        (*ptr).handle = handle;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_actor_ptr(value: RuntimeValue) -> Option<*mut RuntimeActor> {
    if !value.is_heap() {
        return None;
    }

    let ptr = value.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Actor {
            return None;
        }
        Some(ptr as *mut RuntimeActor)
    }
}

/// Spawn a new actor. `body_func` is a pointer to the actor body.
/// Returns a heap-allocated actor handle.
#[no_mangle]
pub extern "C" fn rt_actor_spawn(body_func: u64, ctx: RuntimeValue) -> RuntimeValue {
    // Interpret body_func as an extern "C" fn(ctx: *const u8) and run it inside the actor thread.
    // If body_func is 0, spawn a no-op actor that still owns a mailbox.
    let func: Option<extern "C" fn(*const u8)> = if body_func == 0 {
        None
    } else {
        Some(unsafe { std::mem::transmute(body_func as usize) })
    };
    let ctx_ptr: *const u8 = if ctx.is_heap() {
        ctx.as_heap_ptr() as *const u8
    } else {
        std::ptr::null()
    };
    let handle = spawn_actor(move |inbox, outbox| {
        let inbox = Arc::new(Mutex::new(inbox));
        CURRENT_ACTOR_INBOX.with(|cell| *cell.borrow_mut() = Some(inbox.clone()));
        CURRENT_ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = Some(outbox.clone()));

        if let Some(f) = func {
            f(ctx_ptr);
        }

        CURRENT_ACTOR_INBOX.with(|cell| *cell.borrow_mut() = None);
        CURRENT_ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = None);
    });

    alloc_actor(handle)
}

/// Send a runtime value to an actor. Messages are transported as raw bits.
#[no_mangle]
pub extern "C" fn rt_actor_send(actor: RuntimeValue, message: RuntimeValue) {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        unsafe {
            let bits = message.to_raw();
            let payload = Message::Bytes(bits.to_le_bytes().to_vec());
            let _ = (*actor_ptr).handle.send(payload);
        }
    }
}

/// Receive a message from the current actor's inbox (blocking with timeout).
/// Returns NIL on timeout or when no actor inbox is available.
#[no_mangle]
pub extern "C" fn rt_actor_recv() -> RuntimeValue {
    let msg = CURRENT_ACTOR_INBOX.with(|cell| {
        cell.borrow()
            .as_ref()
            .and_then(|rx| rx.lock().ok())
            .and_then(|guard| guard.recv_timeout(Duration::from_secs(5)).ok())
    });

    match msg {
        Some(Message::Bytes(bytes)) if bytes.len() >= 8 => {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&bytes[..8]);
            RuntimeValue::from_raw(u64::from_le_bytes(buf))
        }
        Some(Message::Value(s)) => rt_string_new(s.as_ptr(), s.len() as u64),
        _ => RuntimeValue::NIL,
    }
}

// ============================================================================
// Wait/blocking operations (FFI-safe)
// ============================================================================

/// Wait on a value (for futures/channels). Currently returns the value immediately.
/// In the future, this will block until the value is ready.
#[no_mangle]
pub extern "C" fn rt_wait(target: RuntimeValue) -> RuntimeValue {
    // For now, just return the value - proper async support will implement blocking
    target
}

// ============================================================================
// Future/Generator operations (FFI-safe)
// ============================================================================

/// RuntimeFuture represents a suspended computation
#[repr(C)]
pub struct RuntimeFuture {
    pub header: HeapHeader,
    /// Current state (0 = pending, 1 = ready)
    pub state: u64,
    /// Result value when ready
    pub result: RuntimeValue,
    /// Function pointer to the body (for resuming)
    pub body_func: u64,
}

/// Create a new future. For now, returns a simple future wrapper.
#[no_mangle]
pub extern "C" fn rt_future_new(body_func: u64, ctx: RuntimeValue) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeFuture>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeFuture;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Future, size as u32);
        (*ptr).state = 0; // pending
        (*ptr).result = RuntimeValue::NIL;
        (*ptr).body_func = body_func;

        // Eagerly execute body if provided
        if body_func != 0 {
            let func: extern "C" fn(*const u8) = std::mem::transmute(body_func as usize);
            let ctx_ptr: *const u8 = if ctx.is_heap() {
                ctx.as_heap_ptr() as *const u8
            } else {
                std::ptr::null()
            };
            func(ctx_ptr);
            (*ptr).state = 1;
            (*ptr).result = RuntimeValue::NIL;
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Await a future. For now, immediately returns NIL (stub).
/// Full implementation needs async runtime integration.
#[no_mangle]
pub extern "C" fn rt_future_await(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Future {
            return RuntimeValue::NIL;
        }
        let f = ptr as *const RuntimeFuture;
        if (*f).state == 1 {
            // Already ready
            return (*f).result;
        }
        // Stub: return NIL for pending futures
        RuntimeValue::NIL
    }
}

/// RuntimeGenerator represents an eager generator backed by a collected value list.
#[repr(C)]
pub struct RuntimeGenerator {
    pub header: HeapHeader,
    /// Current iteration position
    pub index: u64,
    /// Pointer to collected yield values
    pub values: *mut Vec<RuntimeValue>,
}

/// Create a new generator by executing the body and collecting yields eagerly.
#[no_mangle]
pub extern "C" fn rt_generator_new(body_func: u64, ctx: RuntimeValue) -> RuntimeValue {
    // Collect yields into a thread-local buffer while the body runs
    GENERATOR_YIELDS.with(|cell| *cell.borrow_mut() = Some(Vec::new()));
    if body_func != 0 {
        let func: extern "C" fn(*const u8) = unsafe { std::mem::transmute(body_func as usize) };
        let ctx_ptr: *const u8 = if ctx.is_heap() {
            ctx.as_heap_ptr() as *const u8
        } else {
            std::ptr::null()
        };
        func(ctx_ptr);
    }
    let collected = GENERATOR_YIELDS.with(|cell| cell.borrow_mut().take().unwrap_or_default());
    let values = Box::new(collected);
    let values_ptr = Box::into_raw(values);

    let size = std::mem::size_of::<RuntimeGenerator>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeGenerator;
        if ptr.is_null() {
            drop(Box::from_raw(values_ptr));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Generator, size as u32);
        (*ptr).index = 0;
        (*ptr).values = values_ptr;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Record a yielded value during generator execution.
#[no_mangle]
pub extern "C" fn rt_generator_yield(value: RuntimeValue) {
    GENERATOR_YIELDS.with(|cell| {
        if let Some(ref mut yields) = *cell.borrow_mut() {
            yields.push(value);
        }
    });
}

/// Get the next value from a generator (returns NIL when exhausted).
#[no_mangle]
pub extern "C" fn rt_generator_next(generator: RuntimeValue) -> RuntimeValue {
    if !generator.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = generator.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Generator {
            return RuntimeValue::NIL;
        }
        let gen = ptr as *mut RuntimeGenerator;
        if (*gen).values.is_null() {
            return RuntimeValue::NIL;
        }
        let values = &mut *(*gen).values;
        let idx = (*gen).index as usize;
        if idx >= values.len() {
            return RuntimeValue::NIL;
        }
        let val = values[idx];
        (*gen).index += 1;
        val
    }
}

// ============================================================================
// Slice operations (FFI-safe)
// ============================================================================

/// Slice a collection (array, tuple, string)
/// Returns a new collection with elements from start to end (exclusive)
#[no_mangle]
pub extern "C" fn rt_slice(
    collection: RuntimeValue,
    start: i64,
    end: i64,
    step: i64,
) -> RuntimeValue {
    if !collection.is_heap() || step == 0 {
        return RuntimeValue::NIL;
    }

    let ptr = collection.as_heap_ptr();
    unsafe {
        match (*ptr).object_type {
            HeapObjectType::Array => {
                let arr = ptr as *const RuntimeArray;
                let len = (*arr).len as i64;

                // Normalize start and end
                let start = if start < 0 {
                    (len + start).max(0)
                } else {
                    start.min(len)
                };
                let end = if end < 0 {
                    (len + end).max(0)
                } else {
                    end.min(len)
                };

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
            HeapObjectType::String => {
                let str_ptr = ptr as *const RuntimeString;
                let len = (*str_ptr).len as i64;

                // Normalize start and end
                let start = if start < 0 {
                    (len + start).max(0)
                } else {
                    start.min(len)
                };
                let end = if end < 0 {
                    (len + end).max(0)
                } else {
                    end.min(len)
                };

                if step != 1 || start >= end {
                    // Only support step=1 for strings for now
                    return rt_string_new(std::ptr::null(), 0);
                }

                let data = str_ptr.add(1) as *const u8;
                rt_string_new(data.add(start as usize), (end - start) as u64)
            }
            _ => RuntimeValue::NIL,
        }
    }
}

// ============================================================================
// Dict helper operations (FFI-safe)
// ============================================================================

/// Clear all entries from a dictionary
#[no_mangle]
pub extern "C" fn rt_dict_clear(dict: RuntimeValue) -> bool {
    if !dict.is_heap() {
        return false;
    }
    let ptr = dict.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Dict {
            return false;
        }
        let d = ptr as *mut RuntimeDict;
        let capacity = (*d).capacity;

        // Zero out all entries
        let data_ptr = (d.add(1)) as *mut RuntimeValue;
        for i in 0..(capacity * 2) {
            *data_ptr.add(i as usize) = RuntimeValue::NIL;
        }
        (*d).len = 0;
        true
    }
}

/// Get all keys from a dictionary as an array
#[no_mangle]
pub extern "C" fn rt_dict_keys(dict: RuntimeValue) -> RuntimeValue {
    if !dict.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = dict.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Dict {
            return RuntimeValue::NIL;
        }
        let d = ptr as *const RuntimeDict;
        let capacity = (*d).capacity;
        let len = (*d).len;

        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }

        let data_ptr = (d.add(1)) as *const RuntimeValue;
        for i in 0..capacity {
            let k = *data_ptr.add((i * 2) as usize);
            if !k.is_nil() {
                rt_array_push(result, k);
            }
        }
        result
    }
}

/// Get all values from a dictionary as an array
#[no_mangle]
pub extern "C" fn rt_dict_values(dict: RuntimeValue) -> RuntimeValue {
    if !dict.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = dict.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Dict {
            return RuntimeValue::NIL;
        }
        let d = ptr as *const RuntimeDict;
        let capacity = (*d).capacity;
        let len = (*d).len;

        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }

        let data_ptr = (d.add(1)) as *const RuntimeValue;
        for i in 0..capacity {
            let k = *data_ptr.add((i * 2) as usize);
            if !k.is_nil() {
                let v = *data_ptr.add((i * 2 + 1) as usize);
                rt_array_push(result, v);
            }
        }
        result
    }
}

/// Clear all elements from an array
#[no_mangle]
pub extern "C" fn rt_array_clear(array: RuntimeValue) -> bool {
    if !array.is_heap() {
        return false;
    }
    let ptr = array.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Array {
            return false;
        }
        let arr = ptr as *mut RuntimeArray;
        (*arr).len = 0;
        true
    }
}

// ============================================================================
// Interpreter bridge FFI (for hybrid execution)
// ============================================================================

/// Call an interpreted function by name with RuntimeValue arguments.
/// This is a simpler FFI wrapper that avoids BridgeValue complexity.
///
/// # Arguments
/// * `name_ptr` - Pointer to function name string (UTF-8)
/// * `name_len` - Length of function name
/// * `args` - RuntimeValue array containing arguments
///
/// # Returns
/// RuntimeValue result (NIL if function not found or error)
///
/// # Safety
/// name_ptr must be a valid pointer to name_len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_interp_call(
    name_ptr: *const u8,
    name_len: u64,
    args: RuntimeValue,
) -> RuntimeValue {
    // This is a stub implementation - the actual interpreter bridge
    // is in the compiler crate (interpreter_ffi.rs).
    // For now, return NIL to indicate interpreter not available.
    // The compiled code should call simple_interp_call directly
    // when proper interpreter integration is needed.
    let _ = (name_ptr, name_len, args);
    RuntimeValue::NIL
}

/// Evaluate an expression by index (stub).
/// The actual expression storage and evaluation is handled
/// by the compiler's interpreter_ffi module.
///
/// # Arguments
/// * `expr_index` - Index of the stored expression
///
/// # Returns
/// RuntimeValue result (NIL if expression not found or error)
#[no_mangle]
pub extern "C" fn rt_interp_eval(expr_index: u64) -> RuntimeValue {
    // Stub - actual implementation in compiler crate
    let _ = expr_index;
    RuntimeValue::NIL
}

// ============================================================================
// Error handling (FFI-safe)
// ============================================================================

/// Called when a function is not found at runtime.
/// Prints an error message and returns NIL (caller should handle the error).
///
/// # Safety
/// name_ptr must be a valid pointer to name_len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_function_not_found(name_ptr: *const u8, name_len: u64) -> RuntimeValue {
    if name_ptr.is_null() {
        eprintln!("Runtime error: Function not found (unknown name)");
    } else {
        let name_slice = std::slice::from_raw_parts(name_ptr, name_len as usize);
        if let Ok(name_str) = std::str::from_utf8(name_slice) {
            eprintln!("Runtime error: Function '{}' not found", name_str);
        } else {
            eprintln!("Runtime error: Function not found (invalid UTF-8 name)");
        }
    }
    RuntimeValue::NIL
}

/// Called when a method is not found at runtime.
/// Prints an error message and returns NIL.
///
/// # Safety
/// type_ptr and method_ptr must be valid pointers to UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_method_not_found(
    type_ptr: *const u8,
    type_len: u64,
    method_ptr: *const u8,
    method_len: u64,
) -> RuntimeValue {
    let type_name = if type_ptr.is_null() {
        "<unknown type>"
    } else {
        let slice = std::slice::from_raw_parts(type_ptr, type_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    let method_name = if method_ptr.is_null() {
        "<unknown method>"
    } else {
        let slice = std::slice::from_raw_parts(method_ptr, method_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    eprintln!(
        "Runtime error: Method '{}' not found on type '{}'",
        method_name, type_name
    );
    RuntimeValue::NIL
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_roundtrip() {
        for i in [0i64, 1, -1, 42, -42, i64::MAX >> 3, i64::MIN >> 3] {
            let v = RuntimeValue::from_int(i);
            assert!(v.is_int());
            assert_eq!(v.as_int(), i);
        }
    }

    #[test]
    fn test_float_roundtrip() {
        for f in [0.0f64, 1.0, -1.0, 3.14159, f64::MAX, f64::MIN] {
            let v = RuntimeValue::from_float(f);
            assert!(v.is_float());
            // Note: We lose some precision due to 3-bit shift
            let diff = (v.as_float() - f).abs();
            assert!(diff < 1e-10 || diff / f.abs() < 1e-10);
        }
    }

    #[test]
    fn test_bool_roundtrip() {
        let t = RuntimeValue::from_bool(true);
        let f = RuntimeValue::from_bool(false);

        assert!(t.is_bool());
        assert!(f.is_bool());
        assert_eq!(t.as_bool(), true);
        assert_eq!(f.as_bool(), false);
        assert_eq!(t, RuntimeValue::TRUE);
        assert_eq!(f, RuntimeValue::FALSE);
    }

    #[test]
    fn test_nil() {
        let n = RuntimeValue::NIL;
        assert!(n.is_nil());
        assert!(!n.is_int());
        assert!(!n.is_float());
        assert!(!n.is_bool());
    }

    #[test]
    fn test_truthy() {
        assert!(RuntimeValue::from_int(1).truthy());
        assert!(RuntimeValue::from_int(-1).truthy());
        assert!(!RuntimeValue::from_int(0).truthy());

        assert!(RuntimeValue::from_float(1.0).truthy());
        assert!(!RuntimeValue::from_float(0.0).truthy());

        assert!(RuntimeValue::TRUE.truthy());
        assert!(!RuntimeValue::FALSE.truthy());

        assert!(!RuntimeValue::NIL.truthy());
    }

    #[test]
    fn test_type_name() {
        assert_eq!(RuntimeValue::from_int(0).type_name(), "int");
        assert_eq!(RuntimeValue::from_float(0.0).type_name(), "float");
        assert_eq!(RuntimeValue::TRUE.type_name(), "bool");
        assert_eq!(RuntimeValue::NIL.type_name(), "nil");
    }

    #[test]
    fn test_equality() {
        assert_eq!(RuntimeValue::from_int(42), RuntimeValue::from_int(42));
        assert_ne!(RuntimeValue::from_int(42), RuntimeValue::from_int(43));
        assert_eq!(RuntimeValue::NIL, RuntimeValue::NIL);
        assert_ne!(RuntimeValue::TRUE, RuntimeValue::FALSE);
    }

    #[test]
    fn test_debug_format() {
        assert!(format!("{:?}", RuntimeValue::from_int(42)).contains("Int(42)"));
        assert!(format!("{:?}", RuntimeValue::NIL).contains("Nil"));
        assert!(format!("{:?}", RuntimeValue::TRUE).contains("Bool(true)"));
    }

    #[test]
    fn test_default() {
        assert_eq!(RuntimeValue::default(), RuntimeValue::NIL);
    }

    #[test]
    fn test_ffi_functions() {
        assert_eq!(rt_value_as_int(rt_value_int(42)), 42);
        assert!((rt_value_as_float(rt_value_float(3.14)) - 3.14).abs() < 1e-10);
        assert_eq!(rt_value_as_bool(rt_value_bool(true)), true);
        assert!(rt_value_is_nil(rt_value_nil()));
        assert!(rt_value_truthy(rt_value_int(1)));
        assert!(!rt_value_truthy(rt_value_int(0)));
    }

    // ========================================================================
    // Collection tests
    // ========================================================================

    #[test]
    fn test_array_create_and_push() {
        let arr = rt_array_new(10);
        assert!(!arr.is_nil());
        assert!(arr.is_heap());
        assert_eq!(rt_array_len(arr), 0);

        // Push some values
        assert!(rt_array_push(arr, RuntimeValue::from_int(10)));
        assert!(rt_array_push(arr, RuntimeValue::from_int(20)));
        assert!(rt_array_push(arr, RuntimeValue::from_int(30)));
        assert_eq!(rt_array_len(arr), 3);

        // Get values
        assert_eq!(rt_array_get(arr, 0).as_int(), 10);
        assert_eq!(rt_array_get(arr, 1).as_int(), 20);
        assert_eq!(rt_array_get(arr, 2).as_int(), 30);

        // Negative indices
        assert_eq!(rt_array_get(arr, -1).as_int(), 30);
        assert_eq!(rt_array_get(arr, -2).as_int(), 20);
    }

    #[test]
    fn test_array_set() {
        let arr = rt_array_new(5);
        rt_array_push(arr, RuntimeValue::from_int(1));
        rt_array_push(arr, RuntimeValue::from_int(2));
        rt_array_push(arr, RuntimeValue::from_int(3));

        assert!(rt_array_set(arr, 1, RuntimeValue::from_int(42)));
        assert_eq!(rt_array_get(arr, 1).as_int(), 42);

        // Set with negative index
        assert!(rt_array_set(arr, -1, RuntimeValue::from_int(99)));
        assert_eq!(rt_array_get(arr, 2).as_int(), 99);
    }

    #[test]
    fn test_array_pop() {
        let arr = rt_array_new(5);
        rt_array_push(arr, RuntimeValue::from_int(10));
        rt_array_push(arr, RuntimeValue::from_int(20));

        let popped = rt_array_pop(arr);
        assert_eq!(popped.as_int(), 20);
        assert_eq!(rt_array_len(arr), 1);

        let popped = rt_array_pop(arr);
        assert_eq!(popped.as_int(), 10);
        assert_eq!(rt_array_len(arr), 0);

        // Pop from empty array
        let popped = rt_array_pop(arr);
        assert!(popped.is_nil());
    }

    #[test]
    fn test_tuple_create() {
        let tup = rt_tuple_new(3);
        assert!(!tup.is_nil());
        assert_eq!(rt_tuple_len(tup), 3);

        // Set values
        assert!(rt_tuple_set(tup, 0, RuntimeValue::from_int(1)));
        assert!(rt_tuple_set(tup, 1, RuntimeValue::from_int(2)));
        assert!(rt_tuple_set(tup, 2, RuntimeValue::from_int(3)));

        // Get values
        assert_eq!(rt_tuple_get(tup, 0).as_int(), 1);
        assert_eq!(rt_tuple_get(tup, 1).as_int(), 2);
        assert_eq!(rt_tuple_get(tup, 2).as_int(), 3);

        // Out of bounds
        assert!(rt_tuple_get(tup, 3).is_nil());
    }

    #[test]
    fn test_string_create() {
        let s = b"Hello, World!";
        let str_val = rt_string_new(s.as_ptr(), s.len() as u64);
        assert!(!str_val.is_nil());
        assert_eq!(rt_string_len(str_val), 13);

        // Check data
        let data = rt_string_data(str_val);
        assert!(!data.is_null());
        unsafe {
            for (i, &byte) in s.iter().enumerate() {
                assert_eq!(*data.add(i), byte);
            }
        }
    }

    #[test]
    fn test_string_concat() {
        let a = b"Hello, ";
        let b = b"World!";
        let str_a = rt_string_new(a.as_ptr(), a.len() as u64);
        let str_b = rt_string_new(b.as_ptr(), b.len() as u64);

        let result = rt_string_concat(str_a, str_b);
        assert!(!result.is_nil());
        assert_eq!(rt_string_len(result), 13);

        let data = rt_string_data(result);
        let expected = b"Hello, World!";
        unsafe {
            for (i, &byte) in expected.iter().enumerate() {
                assert_eq!(*data.add(i), byte);
            }
        }
    }

    #[test]
    fn test_index_get() {
        // Array indexing
        let arr = rt_array_new(5);
        rt_array_push(arr, RuntimeValue::from_int(10));
        rt_array_push(arr, RuntimeValue::from_int(20));

        let val = rt_index_get(arr, RuntimeValue::from_int(0));
        assert_eq!(val.as_int(), 10);

        // String indexing (returns char code)
        let s = b"ABC";
        let str_val = rt_string_new(s.as_ptr(), s.len() as u64);
        let char_val = rt_index_get(str_val, RuntimeValue::from_int(0));
        assert_eq!(char_val.as_int(), 65); // 'A'
    }

    #[test]
    fn test_slice() {
        // Array slicing
        let arr = rt_array_new(5);
        for i in 0..5 {
            rt_array_push(arr, RuntimeValue::from_int(i * 10));
        }

        let sliced = rt_slice(arr, 1, 4, 1);
        assert!(!sliced.is_nil());
        assert_eq!(rt_array_len(sliced), 3);
        assert_eq!(rt_array_get(sliced, 0).as_int(), 10);
        assert_eq!(rt_array_get(sliced, 1).as_int(), 20);
        assert_eq!(rt_array_get(sliced, 2).as_int(), 30);
    }

    #[test]
    fn test_empty_string() {
        let str_val = rt_string_new(std::ptr::null(), 0);
        assert!(!str_val.is_nil());
        assert_eq!(rt_string_len(str_val), 0);
    }
}
