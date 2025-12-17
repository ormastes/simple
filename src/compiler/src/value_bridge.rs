//! Bridge between interpreter Values and runtime RuntimeValues.
//!
//! This module provides conversion functions for passing values between
//! compiled code (using RuntimeValue) and the interpreter (using Value).
//! It enables the hybrid execution model where compiled code can fall back
//! to the interpreter for unsupported features.

use std::collections::HashMap;
use std::ffi::{c_char, CStr, CString};

use simple_runtime::RuntimeValue;

use crate::value::Value;

/// A C-compatible value representation for FFI.
///
/// This is used when we need to pass values through the FFI boundary
/// in a format that's easy to marshal from both Rust and generated code.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct BridgeValue {
    /// Type tag
    pub tag: u8,
    /// Primary payload (meaning depends on tag)
    pub payload: u64,
    /// Extended payload for complex types (pointer to heap data)
    pub extended: *mut u8,
}

// Tag constants for BridgeValue
pub mod bridge_tags {
    pub const NIL: u8 = 0;
    pub const INT: u8 = 1;
    pub const FLOAT: u8 = 2;
    pub const BOOL: u8 = 3;
    pub const STRING: u8 = 4;
    pub const SYMBOL: u8 = 5;
    pub const ARRAY: u8 = 6;
    pub const TUPLE: u8 = 7;
    pub const DICT: u8 = 8;
    pub const OBJECT: u8 = 9;
    pub const ENUM: u8 = 10;
    pub const LAMBDA: u8 = 11;
    pub const FUNCTION: u8 = 12;
    pub const CONSTRUCTOR: u8 = 13;
    pub const ACTOR: u8 = 14;
    pub const FUTURE: u8 = 15;
    pub const GENERATOR: u8 = 16;
    pub const UNIQUE: u8 = 17;
    pub const SHARED: u8 = 18;
    pub const WEAK: u8 = 19;
    pub const HANDLE: u8 = 20;
    pub const BORROW: u8 = 21;
    pub const BORROW_MUT: u8 = 22;
    pub const ERROR: u8 = 255;
}

impl Default for BridgeValue {
    fn default() -> Self {
        Self::nil()
    }
}

impl std::fmt::Debug for BridgeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.tag {
            bridge_tags::NIL => write!(f, "BridgeValue::Nil"),
            bridge_tags::INT => write!(f, "BridgeValue::Int({})", self.payload as i64),
            bridge_tags::FLOAT => write!(f, "BridgeValue::Float({})", f64::from_bits(self.payload)),
            bridge_tags::BOOL => write!(f, "BridgeValue::Bool({})", self.payload != 0),
            bridge_tags::STRING => write!(f, "BridgeValue::String(...)"),
            bridge_tags::SYMBOL => write!(f, "BridgeValue::Symbol(...)"),
            bridge_tags::ARRAY => write!(f, "BridgeValue::Array(len={})", self.payload),
            bridge_tags::TUPLE => write!(f, "BridgeValue::Tuple(len={})", self.payload),
            bridge_tags::DICT => write!(f, "BridgeValue::Dict(len={})", self.payload),
            bridge_tags::OBJECT => write!(f, "BridgeValue::Object(...)"),
            bridge_tags::ENUM => write!(f, "BridgeValue::Enum(...)"),
            bridge_tags::LAMBDA => write!(f, "BridgeValue::Lambda(...)"),
            bridge_tags::FUNCTION => write!(f, "BridgeValue::Function(...)"),
            bridge_tags::CONSTRUCTOR => write!(f, "BridgeValue::Constructor(...)"),
            bridge_tags::ACTOR => write!(f, "BridgeValue::Actor(...)"),
            bridge_tags::FUTURE => write!(f, "BridgeValue::Future(...)"),
            bridge_tags::GENERATOR => write!(f, "BridgeValue::Generator(...)"),
            bridge_tags::UNIQUE => write!(f, "BridgeValue::Unique(...)"),
            bridge_tags::SHARED => write!(f, "BridgeValue::Shared(...)"),
            bridge_tags::WEAK => write!(f, "BridgeValue::Weak(...)"),
            bridge_tags::HANDLE => write!(f, "BridgeValue::Handle(...)"),
            bridge_tags::BORROW => write!(f, "BridgeValue::Borrow(...)"),
            bridge_tags::BORROW_MUT => write!(f, "BridgeValue::BorrowMut(...)"),
            bridge_tags::ERROR => write!(f, "BridgeValue::Error"),
            _ => write!(f, "BridgeValue::Unknown(tag={})", self.tag),
        }
    }
}

impl BridgeValue {
    /// Helper to create a BridgeValue from a Vec of Values with a specific tag
    fn from_vec_with_tag(items: &[Value], tag: u8) -> Self {
        let len = items.len();
        let mut bridge_items: Vec<BridgeValue> =
            items.iter().map(BridgeValue::from).collect();
        let ptr = bridge_items.as_mut_ptr();
        std::mem::forget(bridge_items);
        Self {
            tag,
            payload: len as u64,
            extended: ptr as *mut u8,
        }
    }

    /// Create a nil BridgeValue
    #[inline]
    pub const fn nil() -> Self {
        Self {
            tag: bridge_tags::NIL,
            payload: 0,
            extended: std::ptr::null_mut(),
        }
    }

    /// Create an integer BridgeValue
    #[inline]
    pub const fn int(i: i64) -> Self {
        Self {
            tag: bridge_tags::INT,
            payload: i as u64,
            extended: std::ptr::null_mut(),
        }
    }

    /// Create a float BridgeValue
    #[inline]
    pub fn float(f: f64) -> Self {
        Self {
            tag: bridge_tags::FLOAT,
            payload: f.to_bits(),
            extended: std::ptr::null_mut(),
        }
    }

    /// Create a boolean BridgeValue
    #[inline]
    pub const fn bool(b: bool) -> Self {
        Self {
            tag: bridge_tags::BOOL,
            payload: if b { 1 } else { 0 },
            extended: std::ptr::null_mut(),
        }
    }

    /// Create a string BridgeValue
    ///
    /// Note: This allocates a new CString that must be freed.
    pub fn string(s: &str) -> Self {
        let cstring = CString::new(s).unwrap_or_else(|_| CString::new("").unwrap());
        let ptr = cstring.into_raw();
        Self {
            tag: bridge_tags::STRING,
            payload: s.len() as u64,
            extended: ptr as *mut u8,
        }
    }

    /// Create a symbol BridgeValue
    pub fn symbol(s: &str) -> Self {
        let cstring = CString::new(s).unwrap_or_else(|_| CString::new("").unwrap());
        let ptr = cstring.into_raw();
        Self {
            tag: bridge_tags::SYMBOL,
            payload: s.len() as u64,
            extended: ptr as *mut u8,
        }
    }

    /// Create an error BridgeValue
    pub fn error(msg: &str) -> Self {
        let cstring = CString::new(msg).unwrap_or_else(|_| CString::new("error").unwrap());
        let ptr = cstring.into_raw();
        Self {
            tag: bridge_tags::ERROR,
            payload: msg.len() as u64,
            extended: ptr as *mut u8,
        }
    }

    /// Check if this is nil
    #[inline]
    pub const fn is_nil(&self) -> bool {
        self.tag == bridge_tags::NIL
    }

    /// Check if this is an error
    #[inline]
    pub const fn is_error(&self) -> bool {
        self.tag == bridge_tags::ERROR
    }

    /// Get as integer (returns 0 if not an int)
    #[inline]
    pub const fn as_int(&self) -> i64 {
        self.payload as i64
    }

    /// Get as float (returns 0.0 if not a float)
    #[inline]
    pub fn as_float(&self) -> f64 {
        f64::from_bits(self.payload)
    }

    /// Get as bool (returns false if not a bool)
    #[inline]
    pub const fn as_bool(&self) -> bool {
        self.payload != 0
    }

    /// Get as string (returns empty string if not a string)
    ///
    /// # Safety
    /// The extended pointer must be a valid CString if tag is STRING.
    pub unsafe fn as_str(&self) -> &str {
        if self.tag == bridge_tags::STRING || self.tag == bridge_tags::SYMBOL {
            if self.extended.is_null() {
                ""
            } else {
                CStr::from_ptr(self.extended as *const c_char)
                    .to_str()
                    .unwrap_or("")
            }
        } else {
            ""
        }
    }

    /// Free any heap-allocated data
    ///
    /// # Safety
    /// This must only be called once, and only if the BridgeValue owns its data.
    pub unsafe fn free(&mut self) {
        match self.tag {
            bridge_tags::STRING | bridge_tags::SYMBOL | bridge_tags::ERROR => {
                if !self.extended.is_null() {
                    let _ = CString::from_raw(self.extended as *mut c_char);
                    self.extended = std::ptr::null_mut();
                }
            }
            bridge_tags::ARRAY | bridge_tags::TUPLE => {
                if !self.extended.is_null() {
                    // Extended points to a Vec<BridgeValue>
                    let len = self.payload as usize;
                    let slice =
                        std::slice::from_raw_parts_mut(self.extended as *mut BridgeValue, len);
                    for item in slice {
                        item.free();
                    }
                    // Free the array itself
                    let _ = Vec::from_raw_parts(self.extended as *mut BridgeValue, len, len);
                    self.extended = std::ptr::null_mut();
                }
            }
            _ => {
                // Other types may have complex cleanup needs
                // For now, just null the pointer
                self.extended = std::ptr::null_mut();
            }
        }
    }
}

// ============================================================================
// Conversion: Value -> BridgeValue
// ============================================================================

impl From<&Value> for BridgeValue {
    fn from(v: &Value) -> Self {
        match v {
            Value::Nil => BridgeValue::nil(),
            Value::Int(i) => BridgeValue::int(*i),
            Value::Float(f) => BridgeValue::float(*f),
            Value::Bool(b) => BridgeValue::bool(*b),
            Value::Str(s) => BridgeValue::string(s),
            Value::Symbol(s) => BridgeValue::symbol(s),
            Value::Array(items) => Self::from_vec_with_tag(items, bridge_tags::ARRAY),
            Value::Tuple(items) => Self::from_vec_with_tag(items, bridge_tags::TUPLE),
            Value::Dict(_) => {
                // For now, store dict as a serialized form
                // Full implementation would need proper serialization
                BridgeValue {
                    tag: bridge_tags::DICT,
                    payload: 0,
                    extended: std::ptr::null_mut(),
                }
            }
            Value::Object { class, .. } => BridgeValue {
                tag: bridge_tags::OBJECT,
                payload: 0,
                extended: CString::new(class.as_str()).unwrap().into_raw() as *mut u8,
            },
            Value::Enum {
                enum_name, variant, ..
            } => {
                // Store enum_name::variant as extended
                let full_name = format!("{}::{}", enum_name, variant);
                BridgeValue {
                    tag: bridge_tags::ENUM,
                    payload: 0,
                    extended: CString::new(full_name).unwrap().into_raw() as *mut u8,
                }
            }
            Value::Lambda { .. } => BridgeValue {
                tag: bridge_tags::LAMBDA,
                payload: 0,
                extended: std::ptr::null_mut(),
            },
            Value::BlockClosure { .. } => BridgeValue {
                tag: bridge_tags::LAMBDA,  // BlockClosures are lambda-like
                payload: 0,
                extended: std::ptr::null_mut(),
            },
            Value::Function { name, .. } => BridgeValue {
                tag: bridge_tags::FUNCTION,
                payload: 0,
                extended: CString::new(name.as_str()).unwrap().into_raw() as *mut u8,
            },
            Value::Constructor { class_name } => BridgeValue {
                tag: bridge_tags::CONSTRUCTOR,
                payload: 0,
                extended: CString::new(class_name.as_str()).unwrap().into_raw() as *mut u8,
            },
            Value::Actor(_) => BridgeValue {
                tag: bridge_tags::ACTOR,
                payload: 0,
                extended: std::ptr::null_mut(),
            },
            Value::Future(_) => BridgeValue {
                tag: bridge_tags::FUTURE,
                payload: 0,
                extended: std::ptr::null_mut(),
            },
            Value::Generator(_) => BridgeValue {
                tag: bridge_tags::GENERATOR,
                payload: 0,
                extended: std::ptr::null_mut(),
            },
            Value::Unique(u) => {
                // Recursively convert inner value
                let inner = BridgeValue::from(u.inner());
                let boxed = Box::new(inner);
                BridgeValue {
                    tag: bridge_tags::UNIQUE,
                    payload: 0,
                    extended: Box::into_raw(boxed) as *mut u8,
                }
            }
            Value::Shared(s) => {
                let inner = BridgeValue::from(s.inner());
                let boxed = Box::new(inner);
                BridgeValue {
                    tag: bridge_tags::SHARED,
                    payload: 0,
                    extended: Box::into_raw(boxed) as *mut u8,
                }
            }
            Value::Weak(_) => BridgeValue {
                tag: bridge_tags::WEAK,
                payload: 0,
                extended: std::ptr::null_mut(),
            },
            Value::Handle(_) => BridgeValue {
                tag: bridge_tags::HANDLE,
                payload: 0,
                extended: std::ptr::null_mut(),
            },
            Value::Borrow(b) => {
                let inner = BridgeValue::from(&*b.inner());
                let boxed = Box::new(inner);
                BridgeValue {
                    tag: bridge_tags::BORROW,
                    payload: 0,
                    extended: Box::into_raw(boxed) as *mut u8,
                }
            }
            Value::BorrowMut(b) => {
                let inner = BridgeValue::from(&*b.inner());
                let boxed = Box::new(inner);
                BridgeValue {
                    tag: bridge_tags::BORROW_MUT,
                    payload: 0,
                    extended: Box::into_raw(boxed) as *mut u8,
                }
            }
            Value::Channel(_) => {
                // Channels cannot be bridged across FFI - use nil
                BridgeValue::nil()
            }
            Value::ThreadPool(_) => {
                // ThreadPools cannot be bridged across FFI - use nil
                BridgeValue::nil()
            }
            Value::Mock(_) => {
                // Mocks cannot be bridged across FFI - use nil
                BridgeValue::nil()
            }
            Value::Matcher(_) => {
                // Matchers cannot be bridged across FFI - use nil
                BridgeValue::nil()
            }
            Value::TraitObject { inner, .. } => {
                // Bridge the inner value - trait info is lost in FFI
                BridgeValue::from(inner.as_ref())
            }
            Value::Unit { value, .. } => {
                // Bridge the inner value - unit suffix is lost in FFI
                BridgeValue::from(value.as_ref())
            }
            Value::Union { inner, .. } => {
                // Bridge the inner value - union type info is lost in FFI
                BridgeValue::from(inner.as_ref())
            }
        }
    }
}

// ============================================================================
// Conversion: BridgeValue -> Value
// ============================================================================

impl BridgeValue {
    /// Helper to convert vector-like BridgeValue to Value
    unsafe fn to_vec_value<F>(&self, wrapper: F) -> Value
    where
        F: FnOnce(Vec<Value>) -> Value,
    {
        let len = self.payload as usize;
        if self.extended.is_null() || len == 0 {
            wrapper(vec![])
        } else {
            let slice =
                std::slice::from_raw_parts(self.extended as *const BridgeValue, len);
            let items: Vec<Value> = slice.iter().map(|bv| bv.to_value()).collect();
            wrapper(items)
        }
    }

    /// Convert to interpreter Value
    ///
    /// # Safety
    /// The BridgeValue must have been created properly with valid pointers.
    pub unsafe fn to_value(&self) -> Value {
        match self.tag {
            bridge_tags::NIL => Value::Nil,
            bridge_tags::INT => Value::Int(self.payload as i64),
            bridge_tags::FLOAT => Value::Float(f64::from_bits(self.payload)),
            bridge_tags::BOOL => Value::Bool(self.payload != 0),
            bridge_tags::STRING => {
                if self.extended.is_null() {
                    Value::Str(String::new())
                } else {
                    let cstr = CStr::from_ptr(self.extended as *const c_char);
                    Value::Str(cstr.to_string_lossy().into_owned())
                }
            }
            bridge_tags::SYMBOL => {
                if self.extended.is_null() {
                    Value::Symbol(String::new())
                } else {
                    let cstr = CStr::from_ptr(self.extended as *const c_char);
                    Value::Symbol(cstr.to_string_lossy().into_owned())
                }
            }
            bridge_tags::ARRAY => self.to_vec_value(Value::Array),
            bridge_tags::TUPLE => self.to_vec_value(Value::Tuple),
            bridge_tags::DICT => {
                // Return empty dict for now
                Value::Dict(HashMap::new())
            }
            bridge_tags::OBJECT => {
                let class = if self.extended.is_null() {
                    String::new()
                } else {
                    let cstr = CStr::from_ptr(self.extended as *const c_char);
                    cstr.to_string_lossy().into_owned()
                };
                Value::Object {
                    class,
                    fields: HashMap::new(),
                }
            }
            bridge_tags::ENUM => {
                let full_name = if self.extended.is_null() {
                    String::new()
                } else {
                    let cstr = CStr::from_ptr(self.extended as *const c_char);
                    cstr.to_string_lossy().into_owned()
                };
                // Parse "EnumName::Variant"
                let parts: Vec<&str> = full_name.split("::").collect();
                let (enum_name, variant) = if parts.len() >= 2 {
                    (parts[0].to_string(), parts[1].to_string())
                } else {
                    (full_name.clone(), String::new())
                };
                Value::Enum {
                    enum_name,
                    variant,
                    payload: None,
                }
            }
            bridge_tags::CONSTRUCTOR => {
                let class_name = if self.extended.is_null() {
                    String::new()
                } else {
                    let cstr = CStr::from_ptr(self.extended as *const c_char);
                    cstr.to_string_lossy().into_owned()
                };
                Value::Constructor { class_name }
            }
            // For complex types that we can't fully reconstruct, return Nil
            bridge_tags::LAMBDA
            | bridge_tags::FUNCTION
            | bridge_tags::ACTOR
            | bridge_tags::FUTURE
            | bridge_tags::GENERATOR
            | bridge_tags::UNIQUE
            | bridge_tags::SHARED
            | bridge_tags::WEAK
            | bridge_tags::HANDLE
            | bridge_tags::BORROW
            | bridge_tags::BORROW_MUT
            | bridge_tags::ERROR
            | _ => Value::Nil,
        }
    }
}

// ============================================================================
// Conversion: RuntimeValue <-> BridgeValue
// ============================================================================

impl From<RuntimeValue> for BridgeValue {
    fn from(rv: RuntimeValue) -> Self {
        use simple_runtime::value::tags as rt_tags;

        match rv.tag() {
            rt_tags::TAG_INT => BridgeValue::int(rv.as_int()),
            rt_tags::TAG_FLOAT => BridgeValue::float(rv.as_float()),
            rt_tags::TAG_SPECIAL => {
                let payload = rv.payload();
                match payload {
                    rt_tags::SPECIAL_NIL => BridgeValue::nil(),
                    rt_tags::SPECIAL_TRUE => BridgeValue::bool(true),
                    rt_tags::SPECIAL_FALSE => BridgeValue::bool(false),
                    _ => BridgeValue::symbol(&format!("symbol_{}", payload)),
                }
            }
            rt_tags::TAG_HEAP => {
                // For heap objects, we'd need to decode the actual type
                // For now, return a placeholder
                BridgeValue {
                    tag: bridge_tags::OBJECT,
                    payload: rv.to_raw(),
                    extended: std::ptr::null_mut(),
                }
            }
            _ => BridgeValue::nil(),
        }
    }
}

impl From<BridgeValue> for RuntimeValue {
    fn from(bv: BridgeValue) -> Self {
        match bv.tag {
            bridge_tags::NIL => RuntimeValue::NIL,
            bridge_tags::INT => RuntimeValue::from_int(bv.payload as i64),
            bridge_tags::FLOAT => RuntimeValue::from_float(f64::from_bits(bv.payload)),
            bridge_tags::BOOL => RuntimeValue::from_bool(bv.payload != 0),
            // Complex types can't be directly converted to RuntimeValue
            // They need heap allocation which we don't do here
            _ => RuntimeValue::NIL,
        }
    }
}

// ============================================================================
// Direct Value <-> RuntimeValue conversion (for simple types)
// ============================================================================

/// Convert an interpreter Value to a RuntimeValue (simple types only)
pub fn value_to_runtime(v: &Value) -> RuntimeValue {
    match v {
        Value::Nil => RuntimeValue::NIL,
        Value::Int(i) => RuntimeValue::from_int(*i),
        Value::Float(f) => RuntimeValue::from_float(*f),
        Value::Bool(b) => RuntimeValue::from_bool(*b),
        // Complex types need heap allocation - return NIL for now
        _ => RuntimeValue::NIL,
    }
}

/// Convert a RuntimeValue to an interpreter Value (simple types only)
pub fn runtime_to_value(rv: RuntimeValue) -> Value {
    use simple_runtime::value::tags as rt_tags;

    match rv.tag() {
        rt_tags::TAG_INT => Value::Int(rv.as_int()),
        rt_tags::TAG_FLOAT => Value::Float(rv.as_float()),
        rt_tags::TAG_SPECIAL => {
            let payload = rv.payload();
            match payload {
                rt_tags::SPECIAL_NIL => Value::Nil,
                rt_tags::SPECIAL_TRUE => Value::Bool(true),
                rt_tags::SPECIAL_FALSE => Value::Bool(false),
                _ => Value::Symbol(format!("symbol_{}", payload)),
            }
        }
        rt_tags::TAG_HEAP => {
            // Complex types need decoding - return Nil for now
            Value::Nil
        }
        _ => Value::Nil,
    }
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Create a BridgeValue from an integer (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_int(i: i64) -> BridgeValue {
    BridgeValue::int(i)
}

/// Create a BridgeValue from a float (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_float(f: f64) -> BridgeValue {
    BridgeValue::float(f)
}

/// Create a BridgeValue from a bool (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_bool(b: bool) -> BridgeValue {
    BridgeValue::bool(b)
}

/// Create a nil BridgeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_nil() -> BridgeValue {
    BridgeValue::nil()
}

/// Extract integer from BridgeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_as_int(bv: BridgeValue) -> i64 {
    bv.as_int()
}

/// Extract float from BridgeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_as_float(bv: BridgeValue) -> f64 {
    bv.as_float()
}

/// Extract bool from BridgeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_as_bool(bv: BridgeValue) -> bool {
    bv.as_bool()
}

/// Check if BridgeValue is nil (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_is_nil(bv: BridgeValue) -> bool {
    bv.is_nil()
}

/// Get the tag of a BridgeValue (FFI-safe)
#[no_mangle]
pub extern "C" fn bridge_value_tag(bv: BridgeValue) -> u8 {
    bv.tag
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bridge_value_nil() {
        let bv = BridgeValue::nil();
        assert!(bv.is_nil());
        assert_eq!(bv.tag, bridge_tags::NIL);
    }

    #[test]
    fn test_bridge_value_int() {
        let bv = BridgeValue::int(42);
        assert_eq!(bv.tag, bridge_tags::INT);
        assert_eq!(bv.as_int(), 42);
    }

    #[test]
    fn test_bridge_value_float() {
        let bv = BridgeValue::float(3.14);
        assert_eq!(bv.tag, bridge_tags::FLOAT);
        assert!((bv.as_float() - 3.14).abs() < 1e-10);
    }

    #[test]
    fn test_bridge_value_bool() {
        let bv_true = BridgeValue::bool(true);
        let bv_false = BridgeValue::bool(false);
        assert_eq!(bv_true.as_bool(), true);
        assert_eq!(bv_false.as_bool(), false);
    }

    #[test]
    fn test_bridge_value_string() {
        let bv = BridgeValue::string("hello");
        assert_eq!(bv.tag, bridge_tags::STRING);
        unsafe {
            assert_eq!(bv.as_str(), "hello");
        }
        // Clean up
        let mut bv = bv;
        unsafe {
            bv.free();
        }
    }

    #[test]
    fn test_value_to_bridge_int() {
        let v = Value::Int(42);
        let bv = BridgeValue::from(&v);
        assert_eq!(bv.tag, bridge_tags::INT);
        assert_eq!(bv.as_int(), 42);
    }

    #[test]
    fn test_value_to_bridge_float() {
        let v = Value::Float(3.14);
        let bv = BridgeValue::from(&v);
        assert_eq!(bv.tag, bridge_tags::FLOAT);
        assert!((bv.as_float() - 3.14).abs() < 1e-10);
    }

    #[test]
    fn test_value_to_bridge_nil() {
        let v = Value::Nil;
        let bv = BridgeValue::from(&v);
        assert!(bv.is_nil());
    }

    #[test]
    fn test_value_to_bridge_str() {
        let v = Value::Str("hello".to_string());
        let bv = BridgeValue::from(&v);
        assert_eq!(bv.tag, bridge_tags::STRING);
        unsafe {
            assert_eq!(bv.as_str(), "hello");
        }
        let mut bv = bv;
        unsafe {
            bv.free();
        }
    }

    #[test]
    fn test_bridge_to_value_int() {
        let bv = BridgeValue::int(42);
        let v = unsafe { bv.to_value() };
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_bridge_to_value_float() {
        let bv = BridgeValue::float(3.14);
        let v = unsafe { bv.to_value() };
        if let Value::Float(f) = v {
            assert!((f - 3.14).abs() < 1e-10);
        } else {
            panic!("Expected Float");
        }
    }

    #[test]
    fn test_runtime_to_bridge_int() {
        let rv = RuntimeValue::from_int(42);
        let bv = BridgeValue::from(rv);
        assert_eq!(bv.as_int(), 42);
    }

    #[test]
    fn test_bridge_to_runtime_int() {
        let bv = BridgeValue::int(42);
        let rv = RuntimeValue::from(bv);
        assert_eq!(rv.as_int(), 42);
    }

    #[test]
    fn test_value_to_runtime_simple() {
        assert_eq!(value_to_runtime(&Value::Nil), RuntimeValue::NIL);
        assert_eq!(value_to_runtime(&Value::Int(42)).as_int(), 42);
        assert_eq!(value_to_runtime(&Value::Bool(true)), RuntimeValue::TRUE);
    }

    #[test]
    fn test_runtime_to_value_simple() {
        assert_eq!(runtime_to_value(RuntimeValue::NIL), Value::Nil);
        assert_eq!(runtime_to_value(RuntimeValue::from_int(42)), Value::Int(42));
        assert_eq!(runtime_to_value(RuntimeValue::TRUE), Value::Bool(true));
    }

    #[test]
    fn test_debug_format() {
        assert!(format!("{:?}", BridgeValue::nil()).contains("Nil"));
        assert!(format!("{:?}", BridgeValue::int(42)).contains("Int(42)"));
    }

    #[test]
    fn test_default() {
        let bv = BridgeValue::default();
        assert!(bv.is_nil());
    }
}
