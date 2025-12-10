//! Core RuntimeValue type and operations.

use super::heap::{HeapHeader, HeapObjectType};
use super::tags;

/// A 64-bit tagged runtime value.
///
/// This is the primary value type used in compiled code. It can represent
/// all Simple Language values in a single 64-bit word, with heap-allocated
/// objects stored as tagged pointers.
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
