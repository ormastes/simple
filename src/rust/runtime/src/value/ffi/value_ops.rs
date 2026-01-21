//! Value creation, extraction, and type checking FFI functions.
//!
//! This module provides the fundamental FFI interface for working with RuntimeValue,
//! including creation, extraction, and type checking operations.

use crate::value::core::RuntimeValue;

// ============================================================================
// Value creation FFI functions
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

// ============================================================================
// Value extraction FFI functions
// ============================================================================

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

// ============================================================================
// Value type checking FFI functions
// ============================================================================

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_creation_and_extraction() {
        let val = rt_value_int(42);
        assert!(rt_value_is_int(val));
        assert_eq!(rt_value_as_int(val), 42);
        assert!(rt_value_truthy(val));
    }

    #[test]
    fn test_float_creation_and_extraction() {
        let val = rt_value_float(3.25);
        assert!(rt_value_is_float(val));
        // Use approximate equality for floating point
        let extracted = rt_value_as_float(val);
        assert!((extracted - 3.25).abs() < 1e-10, "Expected ~3.25, got {}", extracted);
        assert!(rt_value_truthy(val));
    }

    #[test]
    fn test_bool_creation_and_extraction() {
        let val_true = rt_value_bool(true);
        assert!(rt_value_is_bool(val_true));
        assert_eq!(rt_value_as_bool(val_true), true);
        assert!(rt_value_truthy(val_true));

        let val_false = rt_value_bool(false);
        assert!(rt_value_is_bool(val_false));
        assert_eq!(rt_value_as_bool(val_false), false);
        assert!(!rt_value_truthy(val_false));
    }

    #[test]
    fn test_nil_value() {
        let val = rt_value_nil();
        assert!(rt_value_is_nil(val));
        assert!(!rt_value_truthy(val));
    }

    #[test]
    fn test_type_checking_exclusivity() {
        let int_val = rt_value_int(42);
        assert!(rt_value_is_int(int_val));
        assert!(!rt_value_is_float(int_val));
        assert!(!rt_value_is_bool(int_val));
        assert!(!rt_value_is_nil(int_val));

        let float_val = rt_value_float(3.25);
        assert!(!rt_value_is_int(float_val));
        assert!(rt_value_is_float(float_val));
        assert!(!rt_value_is_bool(float_val));
        assert!(!rt_value_is_nil(float_val));

        let bool_val = rt_value_bool(true);
        assert!(!rt_value_is_int(bool_val));
        assert!(!rt_value_is_float(bool_val));
        assert!(rt_value_is_bool(bool_val));
        assert!(!rt_value_is_nil(bool_val));

        let nil_val = rt_value_nil();
        assert!(!rt_value_is_int(nil_val));
        assert!(!rt_value_is_float(nil_val));
        assert!(!rt_value_is_bool(nil_val));
        assert!(rt_value_is_nil(nil_val));
    }

    #[test]
    fn test_zero_and_special_values() {
        // Zero integer is falsy (follows JavaScript/Ruby semantics: 0 is falsy)
        let zero_int = rt_value_int(0);
        assert!(!rt_value_truthy(zero_int));
        assert_eq!(rt_value_as_int(zero_int), 0);

        // Zero float is also falsy
        let zero_float = rt_value_float(0.0);
        assert!(!rt_value_truthy(zero_float));
        assert_eq!(rt_value_as_float(zero_float), 0.0);

        // Negative values are truthy (non-zero)
        let neg_int = rt_value_int(-42);
        assert!(rt_value_truthy(neg_int));
        assert_eq!(rt_value_as_int(neg_int), -42);

        let neg_float = rt_value_float(-3.25);
        assert!(rt_value_truthy(neg_float));
        let extracted = rt_value_as_float(neg_float);
        assert!((extracted - (-3.25)).abs() < 1e-10);
    }
}
