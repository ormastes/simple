//! FFI Wrapper Generation Macros.
//!
//! This module provides macros for easily wrapping Rust types for FFI.
//!
//! # Usage
//!
//! ```rust,ignore
//! use simple_runtime::ffi_wrap_type;
//!
//! // Define a Rust struct
//! struct Database {
//!     url: String,
//!     connected: bool,
//! }
//!
//! impl Database {
//!     fn new(url: &str) -> Self { ... }
//!     fn query(&self, sql: &str) -> Vec<Row> { ... }
//!     fn execute(&mut self, sql: &str) -> usize { ... }
//!     fn close(&mut self) { ... }
//! }
//!
//! // Generate FFI wrapper
//! ffi_wrap_type! {
//!     Database as Database {
//!         static fn open(url: text) -> Database;
//!         fn query(sql: text) -> Array;
//!         me execute(sql: text) -> Int;
//!         fn close();
//!     }
//! }
//! ```
//!
//! This generates:
//! - A vtable with method entries
//! - FFI functions for each method
//! - Type registration function
//! - Object creation/destruction functions

use super::core::RuntimeValue;
use super::ffi_object::{fnv1a_hash_str, method_flags, FfiMethodEntry, FfiVtable};
use super::ffi_registry::{get_registry, FfiObjectStorage};

// ============================================================================
// Trait Definitions for Type Conversion
// ============================================================================

/// Trait for converting Rust types to RuntimeValue.
pub trait IntoRuntimeValue {
    /// Convert self into a RuntimeValue.
    fn into_runtime_value(self) -> RuntimeValue;
}

/// Trait for converting RuntimeValue to Rust types.
pub trait FromRuntimeValue: Sized {
    /// Try to convert a RuntimeValue into Self.
    /// Returns None if the conversion fails.
    fn from_runtime_value(value: RuntimeValue) -> Option<Self>;
}

// ============================================================================
// Built-in Type Conversions
// ============================================================================

impl IntoRuntimeValue for () {
    fn into_runtime_value(self) -> RuntimeValue {
        RuntimeValue::NIL
    }
}

impl FromRuntimeValue for () {
    fn from_runtime_value(_value: RuntimeValue) -> Option<Self> {
        Some(())
    }
}

impl IntoRuntimeValue for bool {
    fn into_runtime_value(self) -> RuntimeValue {
        RuntimeValue::from_bool(self)
    }
}

impl FromRuntimeValue for bool {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if value.is_bool() {
            Some(value.as_bool())
        } else {
            None
        }
    }
}

impl IntoRuntimeValue for i64 {
    fn into_runtime_value(self) -> RuntimeValue {
        RuntimeValue::from_int(self)
    }
}

impl FromRuntimeValue for i64 {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if value.is_int() {
            Some(value.as_int())
        } else {
            None
        }
    }
}

impl IntoRuntimeValue for i32 {
    fn into_runtime_value(self) -> RuntimeValue {
        RuntimeValue::from_int(self as i64)
    }
}

impl FromRuntimeValue for i32 {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if value.is_int() {
            let i = value.as_int();
            if i >= i32::MIN as i64 && i <= i32::MAX as i64 {
                Some(i as i32)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl IntoRuntimeValue for u32 {
    fn into_runtime_value(self) -> RuntimeValue {
        RuntimeValue::from_int(self as i64)
    }
}

impl FromRuntimeValue for u32 {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if value.is_int() {
            let i = value.as_int();
            if i >= 0 && i <= u32::MAX as i64 {
                Some(i as u32)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl IntoRuntimeValue for u64 {
    fn into_runtime_value(self) -> RuntimeValue {
        // Note: May lose precision for large values
        RuntimeValue::from_int(self as i64)
    }
}

impl FromRuntimeValue for u64 {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if value.is_int() {
            let i = value.as_int();
            if i >= 0 {
                Some(i as u64)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl IntoRuntimeValue for usize {
    fn into_runtime_value(self) -> RuntimeValue {
        RuntimeValue::from_int(self as i64)
    }
}

impl FromRuntimeValue for usize {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if value.is_int() {
            let i = value.as_int();
            if i >= 0 {
                Some(i as usize)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl IntoRuntimeValue for f64 {
    fn into_runtime_value(self) -> RuntimeValue {
        RuntimeValue::from_float(self)
    }
}

impl FromRuntimeValue for f64 {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if value.is_float() {
            Some(value.as_float())
        } else if value.is_int() {
            Some(value.as_int() as f64)
        } else {
            None
        }
    }
}

impl IntoRuntimeValue for RuntimeValue {
    fn into_runtime_value(self) -> RuntimeValue {
        self
    }
}

impl FromRuntimeValue for RuntimeValue {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        Some(value)
    }
}

impl IntoRuntimeValue for String {
    fn into_runtime_value(self) -> RuntimeValue {
        unsafe { super::collections::rt_string_new(self.as_ptr(), self.len() as u64) }
    }
}

impl FromRuntimeValue for String {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if !value.is_heap() {
            return None;
        }
        let ptr = value.as_heap_ptr();
        if ptr.is_null() {
            return None;
        }
        unsafe {
            if (*ptr).object_type != super::heap::HeapObjectType::String {
                return None;
            }
            let str_ptr = ptr as *const super::collections::RuntimeString;
            let data = (*str_ptr).as_bytes();
            Some(std::str::from_utf8_unchecked(data).to_string())
        }
    }
}

impl<T: IntoRuntimeValue> IntoRuntimeValue for Option<T> {
    fn into_runtime_value(self) -> RuntimeValue {
        match self {
            Some(v) => v.into_runtime_value(),
            None => RuntimeValue::NIL,
        }
    }
}

impl<T: FromRuntimeValue> FromRuntimeValue for Option<T> {
    fn from_runtime_value(value: RuntimeValue) -> Option<Self> {
        if value.is_nil() {
            Some(None)
        } else {
            T::from_runtime_value(value).map(Some)
        }
    }
}

// ============================================================================
// Helper Functions for Method Table Construction
// ============================================================================

/// Sort method entries by name_hash (for binary search lookup).
pub fn sort_method_entries(entries: &mut [FfiMethodEntry]) {
    entries.sort_by_key(|e| e.name_hash);
}

/// Build a vtable from method entries.
///
/// # Safety
/// - `type_name` must point to valid UTF-8 data that lives as long as the vtable
/// - `methods` must point to valid sorted method entries
pub const unsafe fn build_vtable(
    type_name: *const u8,
    type_name_len: u32,
    method_count: u32,
    methods: *const FfiMethodEntry,
    drop_fn: Option<unsafe extern "C" fn(handle: u32)>,
    clone_fn: Option<unsafe extern "C" fn(handle: u32) -> u32>,
) -> FfiVtable {
    FfiVtable::new(type_name, type_name_len, method_count, methods, drop_fn, clone_fn)
}

// ============================================================================
// Macro for Generating FFI Wrappers
// ============================================================================

/// Build a method entry for use in vtables.
///
/// This is a helper function that can be used in const contexts.
#[macro_export]
macro_rules! ffi_method_entry {
    ($name:literal, $flags:expr, $func:expr) => {{
        $crate::value::ffi_object::FfiMethodEntry::new(
            $crate::value::ffi_object::fnv1a_hash($name.as_bytes()),
            $name.as_ptr(),
            $name.len() as u32,
            $flags,
            $func as *const (),
        )
    }};
}

/// Declare an FFI type with its methods.
///
/// This macro generates:
/// - A vtable for the type
/// - FFI-compatible method wrappers
/// - Type registration function
///
/// # Example
///
/// ```rust,ignore
/// ffi_declare_type! {
///     type_name: "Counter",
///     rust_type: Counter,
///     methods: [
///         ("increment", MUTABLE, counter_increment),
///         ("get", IMMUTABLE, counter_get),
///         ("reset", MUTABLE, counter_reset),
///     ],
///     drop_fn: Some(counter_drop),
///     clone_fn: None,
/// }
/// ```
#[macro_export]
macro_rules! ffi_declare_type {
    (
        type_name: $type_name:literal,
        rust_type: $rust_type:ty,
        methods: [
            $(($method_name:literal, $flags:ident, $func:expr)),* $(,)?
        ],
        drop_fn: $drop_fn:expr,
        clone_fn: $clone_fn:expr $(,)?
    ) => {
        paste::paste! {
            // Static type name bytes
            static [<$rust_type:upper _TYPE_NAME>]: &[u8] = $type_name.as_bytes();

            // Static method entries (will be sorted at runtime during init)
            static mut [<$rust_type:upper _METHODS>]: [
                $crate::value::ffi_object::FfiMethodEntry;
                {
                    let mut count = 0usize;
                    $(let _ = $method_name; count += 1;)*
                    count
                }
            ] = [
                $(
                    $crate::value::ffi_object::FfiMethodEntry::new(
                        $crate::value::ffi_object::fnv1a_hash($method_name.as_bytes()),
                        $method_name.as_ptr(),
                        $method_name.len() as u32,
                        $crate::value::ffi_object::method_flags::$flags,
                        $func as *const (),
                    ),
                )*
            ];

            // Static vtable (initialized lazily)
            static mut [<$rust_type:upper _VTABLE>]: $crate::value::ffi_object::FfiVtable =
                $crate::value::ffi_object::FfiVtable {
                    type_name: std::ptr::null(),
                    type_name_len: 0,
                    method_count: 0,
                    methods: std::ptr::null(),
                    drop_fn: None,
                    clone_fn: None,
                };

            static [<$rust_type:upper _INIT>]: std::sync::Once = std::sync::Once::new();

            /// Initialize the FFI type (call once before use).
            fn [<init_ $rust_type:lower _ffi>]() {
                [<$rust_type:upper _INIT>].call_once(|| {
                    unsafe {
                        // Sort methods by hash
                        $crate::value::ffi_macros::sort_method_entries(
                            &mut [<$rust_type:upper _METHODS>]
                        );

                        // Initialize vtable
                        [<$rust_type:upper _VTABLE>] = $crate::value::ffi_object::FfiVtable::new(
                            [<$rust_type:upper _TYPE_NAME>].as_ptr(),
                            [<$rust_type:upper _TYPE_NAME>].len() as u32,
                            [<$rust_type:upper _METHODS>].len() as u32,
                            [<$rust_type:upper _METHODS>].as_ptr(),
                            $drop_fn,
                            $clone_fn,
                        );
                    }
                });
            }

            /// Register the FFI type with the global registry.
            /// Returns the type ID (or 0 if already registered).
            pub fn [<register_ $rust_type:lower _type>]() -> u32 {
                [<init_ $rust_type:lower _ffi>]();
                unsafe {
                    $crate::value::ffi_registry::get_registry()
                        .register_type($type_name, &[<$rust_type:upper _VTABLE>])
                }
            }

            /// Get the vtable for this type.
            pub fn [<get_ $rust_type:lower _vtable>]() -> *const $crate::value::ffi_object::FfiVtable {
                [<init_ $rust_type:lower _ffi>]();
                unsafe { &[<$rust_type:upper _VTABLE>] }
            }
        }
    };
}

// ============================================================================
// Convenience Functions
// ============================================================================

/// Get an argument from the argument array.
///
/// # Safety
/// - `argv` must be valid for `argc` elements
/// - `index` must be less than `argc`
#[inline]
pub unsafe fn get_arg(argv: *const RuntimeValue, argc: u32, index: u32) -> Option<RuntimeValue> {
    if index < argc && !argv.is_null() {
        Some(*argv.add(index as usize))
    } else {
        None
    }
}

/// Get an argument and convert it to a Rust type.
///
/// # Safety
/// - `argv` must be valid for `argc` elements
#[inline]
pub unsafe fn get_arg_as<T: FromRuntimeValue>(
    argv: *const RuntimeValue,
    argc: u32,
    index: u32,
) -> Option<T> {
    get_arg(argv, argc, index).and_then(T::from_runtime_value)
}

/// Get a string argument from the argument array.
///
/// # Safety
/// - `argv` must be valid for `argc` elements
pub unsafe fn get_string_arg(argv: *const RuntimeValue, argc: u32, index: u32) -> Option<String> {
    get_arg_as::<String>(argv, argc, index)
}

/// Get an integer argument from the argument array.
///
/// # Safety
/// - `argv` must be valid for `argc` elements
pub unsafe fn get_int_arg(argv: *const RuntimeValue, argc: u32, index: u32) -> Option<i64> {
    get_arg_as::<i64>(argv, argc, index)
}

/// Get a float argument from the argument array.
///
/// # Safety
/// - `argv` must be valid for `argc` elements
pub unsafe fn get_float_arg(argv: *const RuntimeValue, argc: u32, index: u32) -> Option<f64> {
    get_arg_as::<f64>(argv, argc, index)
}

/// Get a bool argument from the argument array.
///
/// # Safety
/// - `argv` must be valid for `argc` elements
pub unsafe fn get_bool_arg(argv: *const RuntimeValue, argc: u32, index: u32) -> Option<bool> {
    get_arg_as::<bool>(argv, argc, index)
}

// ============================================================================
// Error Handling
// ============================================================================

/// Result type for FFI operations.
pub type FfiResult<T> = Result<T, FfiError>;

/// Error type for FFI operations.
#[derive(Debug, Clone)]
pub enum FfiError {
    /// Invalid argument type
    InvalidArgument { index: u32, expected: &'static str },
    /// Missing required argument
    MissingArgument { index: u32 },
    /// Invalid handle
    InvalidHandle { handle: u32 },
    /// Type not registered
    TypeNotRegistered { type_name: String },
    /// Method not found
    MethodNotFound { method_name: String },
    /// Operation failed
    OperationFailed { message: String },
}

impl std::fmt::Display for FfiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FfiError::InvalidArgument { index, expected } => {
                write!(f, "Invalid argument at index {}: expected {}", index, expected)
            }
            FfiError::MissingArgument { index } => {
                write!(f, "Missing required argument at index {}", index)
            }
            FfiError::InvalidHandle { handle } => {
                write!(f, "Invalid handle: {}", handle)
            }
            FfiError::TypeNotRegistered { type_name } => {
                write!(f, "Type not registered: {}", type_name)
            }
            FfiError::MethodNotFound { method_name } => {
                write!(f, "Method not found: {}", method_name)
            }
            FfiError::OperationFailed { message } => {
                write!(f, "Operation failed: {}", message)
            }
        }
    }
}

impl std::error::Error for FfiError {}

impl IntoRuntimeValue for FfiError {
    fn into_runtime_value(self) -> RuntimeValue {
        // For now, return NIL for errors
        // In the future, we could create an error object
        RuntimeValue::NIL
    }
}

impl<T: IntoRuntimeValue> IntoRuntimeValue for FfiResult<T> {
    fn into_runtime_value(self) -> RuntimeValue {
        match self {
            Ok(v) => v.into_runtime_value(),
            Err(_) => RuntimeValue::NIL,
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_into_runtime_value_primitives() {
        // Unit
        let v = ().into_runtime_value();
        assert!(v.is_nil());

        // Bool
        let v = true.into_runtime_value();
        assert!(v.is_bool());
        assert!(v.as_bool());

        let v = false.into_runtime_value();
        assert!(v.is_bool());
        assert!(!v.as_bool());

        // Integer
        let v = 42i64.into_runtime_value();
        assert!(v.is_int());
        assert_eq!(v.as_int(), 42);

        // Float
        let v = 3.14f64.into_runtime_value();
        assert!(v.is_float());
        assert!((v.as_float() - 3.14).abs() < 0.001);
    }

    #[test]
    fn test_from_runtime_value_primitives() {
        // Bool
        let v = RuntimeValue::TRUE;
        assert_eq!(bool::from_runtime_value(v), Some(true));

        let v = RuntimeValue::FALSE;
        assert_eq!(bool::from_runtime_value(v), Some(false));

        // Integer
        let v = RuntimeValue::from_int(42);
        assert_eq!(i64::from_runtime_value(v), Some(42));
        assert_eq!(i32::from_runtime_value(v), Some(42));
        assert_eq!(u32::from_runtime_value(v), Some(42));

        // Float
        let v = RuntimeValue::from_float(3.14);
        let f = f64::from_runtime_value(v).unwrap();
        assert!((f - 3.14).abs() < 0.001);
    }

    #[test]
    fn test_option_conversion() {
        // Some value
        let v = Some(42i64).into_runtime_value();
        assert!(v.is_int());
        assert_eq!(v.as_int(), 42);

        // None
        let v = Option::<i64>::None.into_runtime_value();
        assert!(v.is_nil());

        // From NIL
        let v = RuntimeValue::NIL;
        let opt = Option::<i64>::from_runtime_value(v);
        assert_eq!(opt, Some(None));

        // From value
        let v = RuntimeValue::from_int(42);
        let opt = Option::<i64>::from_runtime_value(v);
        assert_eq!(opt, Some(Some(42)));
    }

    #[test]
    fn test_get_arg() {
        let args = [
            RuntimeValue::from_int(1),
            RuntimeValue::from_int(2),
            RuntimeValue::from_int(3),
        ];

        unsafe {
            // Valid indices
            assert_eq!(get_arg(args.as_ptr(), 3, 0).map(|v| v.as_int()), Some(1));
            assert_eq!(get_arg(args.as_ptr(), 3, 1).map(|v| v.as_int()), Some(2));
            assert_eq!(get_arg(args.as_ptr(), 3, 2).map(|v| v.as_int()), Some(3));

            // Invalid index
            assert!(get_arg(args.as_ptr(), 3, 3).is_none());

            // Typed access
            assert_eq!(get_int_arg(args.as_ptr(), 3, 0), Some(1));
        }
    }
}
