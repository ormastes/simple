//! FFI bridge between Simple's RuntimeValue and WebAssembly values
//!
//! This module provides bidirectional conversion between Simple's RuntimeValue
//! (64-bit tagged pointer) and WebAssembly's value types (i32, i64, f32, f64).

use crate::error::{WasmError, WasmResult};
use simple_runtime::RuntimeValue;

#[cfg(feature = "wasm")]
use wasmer::Value as WasmValue;

/// Convert a RuntimeValue to a WASM value
///
/// # Conversions
///
/// - Integer → i64 (WASM i64)
/// - Float → f64 (WASM f64)
/// - Bool → i32 (0 or 1)
/// - Nil → i64 (0)
/// - Heap pointer → i64 (pointer address)
#[cfg(feature = "wasm")]
pub fn to_wasm_value(value: RuntimeValue) -> WasmResult<WasmValue> {
    use simple_runtime::value::tags;

    match value.tag() {
        tags::TAG_INT => Ok(WasmValue::I64(value.as_int())),

        tags::TAG_FLOAT => Ok(WasmValue::F64(value.as_float())),

        tags::TAG_SPECIAL => {
            let payload = value.payload();
            match payload {
                tags::SPECIAL_NIL => Ok(WasmValue::I64(0)),
                tags::SPECIAL_TRUE => Ok(WasmValue::I32(1)),
                tags::SPECIAL_FALSE => Ok(WasmValue::I32(0)),
                _ => {
                    // Symbol - convert to i64
                    Ok(WasmValue::I64(payload as i64))
                }
            }
        }

        tags::TAG_HEAP => {
            // Heap pointer - convert address to i64
            let ptr = value.as_heap_ptr() as u64;
            Ok(WasmValue::I64(ptr as i64))
        }

        _ => Err(WasmError::ConversionError(format!(
            "Unknown RuntimeValue tag: {}",
            value.tag()
        ))),
    }
}

/// Convert a WASM value to a RuntimeValue
///
/// # Conversions
///
/// - i32 → Integer (sign-extended to i64)
/// - i64 → Integer or Heap pointer (if in heap range)
/// - f32 → Float (converted to f64)
/// - f64 → Float
/// - v128 → Not supported (error)
#[cfg(feature = "wasm")]
pub fn from_wasm_value(value: WasmValue) -> WasmResult<RuntimeValue> {
    match value {
        WasmValue::I32(v) => Ok(RuntimeValue::from_int(v as i64)),

        WasmValue::I64(v) => {
            // Check if this looks like a heap pointer (high bit clear, non-zero)
            // For now, treat all i64 as integers
            Ok(RuntimeValue::from_int(v))
        }

        WasmValue::F32(v) => Ok(RuntimeValue::from_float(v as f64)),

        WasmValue::F64(v) => Ok(RuntimeValue::from_float(v)),

        WasmValue::V128(_) => Err(WasmError::ConversionError(
            "v128 values not supported".to_string(),
        )),

        WasmValue::FuncRef(_) => Err(WasmError::ConversionError(
            "Function references not supported".to_string(),
        )),

        WasmValue::ExternRef(_) => Err(WasmError::ConversionError(
            "External references not supported".to_string(),
        )),
    }
}

/// Convert a slice of RuntimeValues to WASM values
#[cfg(feature = "wasm")]
pub fn to_wasm_values(values: &[RuntimeValue]) -> WasmResult<Vec<WasmValue>> {
    values.iter().map(|v| to_wasm_value(*v)).collect()
}

/// Convert a slice of WASM values to RuntimeValues
#[cfg(feature = "wasm")]
pub fn from_wasm_values(values: &[WasmValue]) -> WasmResult<Vec<RuntimeValue>> {
    values.iter().map(|v| from_wasm_value(v.clone())).collect()
}

/// Extract a single RuntimeValue from WASM function results
#[cfg(feature = "wasm")]
pub fn extract_result(results: &[WasmValue]) -> WasmResult<RuntimeValue> {
    match results.len() {
        0 => Ok(RuntimeValue::NIL),
        1 => from_wasm_value(results[0].clone()),
        _ => Err(WasmError::ConversionError(
            "Multiple return values not supported".to_string(),
        )),
    }
}

/// Convert RuntimeValue to i32 (for boolean/small integer values)
#[cfg(feature = "wasm")]
pub fn to_i32(value: RuntimeValue) -> WasmResult<i32> {
    use simple_runtime::value::tags;

    match value.tag() {
        tags::TAG_INT => {
            let i = value.as_int();
            if i >= i32::MIN as i64 && i <= i32::MAX as i64 {
                Ok(i as i32)
            } else {
                Err(WasmError::ConversionError(format!(
                    "Integer {} out of i32 range",
                    i
                )))
            }
        }
        tags::TAG_SPECIAL => {
            let payload = value.payload();
            match payload {
                tags::SPECIAL_NIL => Ok(0),
                tags::SPECIAL_TRUE => Ok(1),
                tags::SPECIAL_FALSE => Ok(0),
                _ => Ok(payload as i32),
            }
        }
        _ => Err(WasmError::ConversionError(format!(
            "Cannot convert {:?} to i32",
            value
        ))),
    }
}

/// Convert RuntimeValue to i64
#[cfg(feature = "wasm")]
pub fn to_i64(value: RuntimeValue) -> WasmResult<i64> {
    use simple_runtime::value::tags;

    match value.tag() {
        tags::TAG_INT => Ok(value.as_int()),
        tags::TAG_SPECIAL => {
            let payload = value.payload();
            match payload {
                tags::SPECIAL_NIL => Ok(0),
                tags::SPECIAL_TRUE => Ok(1),
                tags::SPECIAL_FALSE => Ok(0),
                _ => Ok(payload as i64),
            }
        }
        tags::TAG_HEAP => Ok(value.as_heap_ptr() as i64),
        _ => Err(WasmError::ConversionError(format!(
            "Cannot convert {:?} to i64",
            value
        ))),
    }
}

/// Convert RuntimeValue to f64
#[cfg(feature = "wasm")]
pub fn to_f64(value: RuntimeValue) -> WasmResult<f64> {
    use simple_runtime::value::tags;

    match value.tag() {
        tags::TAG_FLOAT => Ok(value.as_float()),
        tags::TAG_INT => Ok(value.as_int() as f64),
        _ => Err(WasmError::ConversionError(format!(
            "Cannot convert {:?} to f64",
            value
        ))),
    }
}

// Stub implementations when wasm feature is disabled
#[cfg(not(feature = "wasm"))]
pub fn to_wasm_value(_value: RuntimeValue) -> WasmResult<()> {
    Err(WasmError::FeatureNotEnabled)
}

#[cfg(not(feature = "wasm"))]
pub fn from_wasm_value(_value: ()) -> WasmResult<RuntimeValue> {
    Err(WasmError::FeatureNotEnabled)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runtime_value_integer() {
        let value = RuntimeValue::from_int(42);
        assert_eq!(value.as_int(), 42);
    }

    #[test]
    fn test_runtime_value_float() {
        let value = RuntimeValue::from_float(3.15);
        assert!((value.as_float() - 3.15).abs() < 0.0001);
    }

    #[test]
    fn test_runtime_value_bool() {
        assert!(RuntimeValue::TRUE.as_bool());
        assert!(!RuntimeValue::FALSE.as_bool());
    }

    #[test]
    fn test_runtime_value_nil() {
        let nil = RuntimeValue::NIL;
        assert!(nil.is_nil());
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_to_wasm_value_integer() {
        let value = RuntimeValue::from_int(42);
        let wasm = to_wasm_value(value).unwrap();
        match wasm {
            WasmValue::I64(v) => assert_eq!(v, 42),
            _ => panic!("Expected I64"),
        }
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_to_wasm_value_float() {
        let value = RuntimeValue::from_float(3.15);
        let wasm = to_wasm_value(value).unwrap();
        match wasm {
            WasmValue::F64(v) => assert!((v - 3.15).abs() < 0.0001),
            _ => panic!("Expected F64"),
        }
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_to_wasm_value_bool() {
        let true_val = to_wasm_value(RuntimeValue::TRUE).unwrap();
        let false_val = to_wasm_value(RuntimeValue::FALSE).unwrap();

        match true_val {
            WasmValue::I32(v) => assert_eq!(v, 1),
            _ => panic!("Expected I32"),
        }

        match false_val {
            WasmValue::I32(v) => assert_eq!(v, 0),
            _ => panic!("Expected I32"),
        }
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_to_wasm_value_nil() {
        let wasm = to_wasm_value(RuntimeValue::NIL).unwrap();
        match wasm {
            WasmValue::I64(v) => assert_eq!(v, 0),
            _ => panic!("Expected I64"),
        }
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_from_wasm_value_i32() {
        let wasm = WasmValue::I32(42);
        let value = from_wasm_value(wasm).unwrap();
        assert_eq!(value.as_int(), 42);
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_from_wasm_value_i64() {
        let wasm = WasmValue::I64(12345);
        let value = from_wasm_value(wasm).unwrap();
        assert_eq!(value.as_int(), 12345);
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_from_wasm_value_f64() {
        let wasm = WasmValue::F64(2.718);
        let value = from_wasm_value(wasm).unwrap();
        assert!((value.as_float() - 2.718).abs() < 0.0001);
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_roundtrip_integer() {
        let original = RuntimeValue::from_int(999);
        let wasm = to_wasm_value(original).unwrap();
        let back = from_wasm_value(wasm).unwrap();
        assert_eq!(original, back);
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_roundtrip_float() {
        let original = RuntimeValue::from_float(1.414);
        let wasm = to_wasm_value(original).unwrap();
        let back = from_wasm_value(wasm).unwrap();
        assert!((original.as_float() - back.as_float()).abs() < 0.0001);
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_to_i32() {
        assert_eq!(to_i32(RuntimeValue::from_int(42)).unwrap(), 42);
        assert_eq!(to_i32(RuntimeValue::TRUE).unwrap(), 1);
        assert_eq!(to_i32(RuntimeValue::FALSE).unwrap(), 0);
        assert_eq!(to_i32(RuntimeValue::NIL).unwrap(), 0);
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_to_i64() {
        assert_eq!(to_i64(RuntimeValue::from_int(12345)).unwrap(), 12345);
        assert_eq!(to_i64(RuntimeValue::TRUE).unwrap(), 1);
        assert_eq!(to_i64(RuntimeValue::NIL).unwrap(), 0);
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_to_f64() {
        let float_val = RuntimeValue::from_float(3.15159);
        assert!((to_f64(float_val).unwrap() - 3.15159).abs() < 0.00001);

        // Integer to float conversion
        let int_val = RuntimeValue::from_int(42);
        assert_eq!(to_f64(int_val).unwrap(), 42.0);
    }
}
