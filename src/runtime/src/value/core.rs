//! Core RuntimeValue type and operations.

use super::heap::{HeapHeader, HeapObjectType};
use super::tags;

/// A 64-bit tagged runtime value.
///
/// This is the primary value type used in compiled code. It can represent
/// all Simple Language values in a single 64-bit word, with heap-allocated
/// objects stored as tagged pointers.
///
/// # Architecture Support
///
/// RuntimeValue always uses 64 bits regardless of the target architecture.
/// This design choice ensures:
/// - Consistent semantics across 32-bit and 64-bit platforms
/// - Full 61-bit integer range on all architectures
/// - Simpler codegen (no architecture-specific value representations)
///
/// On 32-bit platforms, this means:
/// - Values are 8 bytes (two 32-bit words)
/// - Heap pointers only use the lower 32 bits (upper 32 bits are zero)
/// - Slightly higher memory usage, but consistent behavior
///
/// # Value Layout
///
/// ```text
/// 64-bit word:
/// ┌─────────────────────────────────────────────────────────────┬─────┐
/// │                       Payload (61 bits)                     │ Tag │
/// │                                                             │(3b) │
/// └─────────────────────────────────────────────────────────────┴─────┘
///
/// Tags:
/// - 0b000 (TAG_INT):     Integer (payload is signed 61-bit value)
/// - 0b001 (TAG_HEAP):    Heap pointer (payload is 61-bit aligned pointer)
/// - 0b010 (TAG_FLOAT):   Float (payload is upper 61 bits of f64)
/// - 0b011 (TAG_SPECIAL): Special values (nil, bool, symbols)
/// ```
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct RuntimeValue(pub(crate) u64);

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

impl Default for RuntimeValue {
    fn default() -> Self {
        Self::NIL
    }
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
    pub(crate) const fn from_tag_payload(tag: u64, payload: u64) -> Self {
        Self((payload << 3) | tag)
    }

    /// Create a special value (nil, bool, symbol)
    #[inline]
    pub(crate) const fn from_special(payload: u64) -> Self {
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

    /// Convert a pointer to u64 (works on both 32-bit and 64-bit platforms).
    #[inline]
    fn ptr_to_u64<T>(ptr: *const T) -> u64 {
        // On 32-bit: usize is 4 bytes, so this zero-extends to 64 bits
        // On 64-bit: usize is 8 bytes, direct conversion
        ptr as usize as u64
    }

    /// Convert u64 to pointer (works on both 32-bit and 64-bit platforms).
    #[inline]
    fn u64_to_ptr<T>(value: u64) -> *mut T {
        // On 32-bit: truncates to lower 32 bits (which is correct since
        //            upper 32 bits should be zero for valid 32-bit pointers)
        // On 64-bit: direct conversion
        value as usize as *mut T
    }

    /// Create a heap pointer value
    ///
    /// # Safety
    /// The pointer must be valid and properly aligned (8-byte alignment).
    /// On 32-bit systems, only the lower 32 bits of the pointer are used.
    #[inline]
    pub unsafe fn from_heap_ptr(ptr: *mut HeapHeader) -> Self {
        debug_assert!(!ptr.is_null());
        let ptr_bits = Self::ptr_to_u64(ptr);
        debug_assert!(ptr_bits & tags::TAG_MASK == 0, "pointer not aligned");
        Self(ptr_bits | tags::TAG_HEAP)
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
            Self::u64_to_ptr(self.0 & !tags::TAG_MASK)
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
                Some(HeapObjectType::ContractViolation) => "contract_violation",
                None => "null",
            },
            _ => "unknown",
        }
    }
}
