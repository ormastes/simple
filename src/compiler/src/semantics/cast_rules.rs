//! Unified cast rules for interpreter and codegen.
//!
//! This module provides a single source of truth for type casting semantics
//! that must be consistent between the interpreter and compiled code.

/// Numeric type categories for casting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericType {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

impl NumericType {
    /// Parse a type name into a NumericType.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "i8" => Some(Self::I8),
            "i16" => Some(Self::I16),
            "i32" => Some(Self::I32),
            "i64" | "int" => Some(Self::I64),
            "u8" => Some(Self::U8),
            "u16" => Some(Self::U16),
            "u32" => Some(Self::U32),
            "u64" => Some(Self::U64),
            "f32" => Some(Self::F32),
            "f64" | "float" => Some(Self::F64),
            _ => None,
        }
    }

    /// Get the type name.
    pub fn name(&self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }

    /// Check if this is a floating point type.
    pub fn is_float(&self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }

    /// Check if this is a signed integer type.
    pub fn is_signed(&self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }

    /// Check if this is an unsigned integer type.
    pub fn is_unsigned(&self) -> bool {
        matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::U64)
    }

    /// Check if this is any integer type.
    pub fn is_integer(&self) -> bool {
        !self.is_float()
    }
}

/// Cast an i64 to a target numeric type, returning the result as i64.
///
/// This handles truncation and sign extension according to Simple's semantics.
pub fn cast_int_to_numeric(value: i64, target: NumericType) -> CastNumericResult {
    match target {
        NumericType::I8 => CastNumericResult::Int(value as i8 as i64),
        NumericType::I16 => CastNumericResult::Int(value as i16 as i64),
        NumericType::I32 => CastNumericResult::Int(value as i32 as i64),
        NumericType::I64 => CastNumericResult::Int(value),
        NumericType::U8 => CastNumericResult::Int(value as u8 as i64),
        NumericType::U16 => CastNumericResult::Int(value as u16 as i64),
        NumericType::U32 => CastNumericResult::Int(value as u32 as i64),
        NumericType::U64 => CastNumericResult::Int(value as u64 as i64),
        NumericType::F32 => CastNumericResult::Float(value as f32 as f64),
        NumericType::F64 => CastNumericResult::Float(value as f64),
    }
}

/// Cast an f64 to a target numeric type.
pub fn cast_float_to_numeric(value: f64, target: NumericType) -> CastNumericResult {
    match target {
        NumericType::I8 => CastNumericResult::Int(value as i8 as i64),
        NumericType::I16 => CastNumericResult::Int(value as i16 as i64),
        NumericType::I32 => CastNumericResult::Int(value as i32 as i64),
        NumericType::I64 => CastNumericResult::Int(value as i64),
        NumericType::U8 => CastNumericResult::Int(value as u8 as i64),
        NumericType::U16 => CastNumericResult::Int(value as u16 as i64),
        NumericType::U32 => CastNumericResult::Int(value as u32 as i64),
        NumericType::U64 => CastNumericResult::Int(value as u64 as i64),
        NumericType::F32 => CastNumericResult::Float(value as f32 as f64),
        NumericType::F64 => CastNumericResult::Float(value),
    }
}

/// Cast a bool to a target numeric type.
pub fn cast_bool_to_numeric(value: bool, target: NumericType) -> CastNumericResult {
    if target.is_float() {
        CastNumericResult::Float(if value { 1.0 } else { 0.0 })
    } else {
        CastNumericResult::Int(if value { 1 } else { 0 })
    }
}

/// Result of a numeric cast operation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CastNumericResult {
    Int(i64),
    Float(f64),
}

/// Cast rules for bool conversion.
pub mod bool_cast {
    /// Convert an integer to bool: non-zero is true.
    pub fn from_int(i: i64) -> bool {
        i != 0
    }

    /// Convert a float to bool: non-zero is true.
    pub fn from_float(f: f64) -> bool {
        f != 0.0
    }

    /// Convert a string to bool: non-empty is true.
    pub fn from_str(s: &str) -> bool {
        !s.is_empty()
    }
}

/// Cast rules for string conversion.
pub mod string_cast {
    /// Convert an integer to string.
    pub fn from_int(i: i64) -> String {
        i.to_string()
    }

    /// Convert a float to string.
    pub fn from_float(f: f64) -> String {
        f.to_string()
    }

    /// Convert a bool to string.
    pub fn from_bool(b: bool) -> String {
        b.to_string()
    }
}

/// Macro to generate cast functions for interpreter Value type.
///
/// This eliminates the need for 12 nearly-identical cast_to_* functions.
#[macro_export]
macro_rules! impl_value_casts {
    () => {
        use $crate::semantics::cast_rules::{
            cast_bool_to_numeric, cast_float_to_numeric, cast_int_to_numeric, CastNumericResult, NumericType,
        };

        fn cast_to_numeric(val: Value, target: NumericType) -> Result<Value, CompileError> {
            match val {
                Value::Int(i) => match cast_int_to_numeric(i, target) {
                    CastNumericResult::Int(v) => Ok(Value::Int(v)),
                    CastNumericResult::Float(v) => Ok(Value::Float(v)),
                },
                Value::Float(f) => match cast_float_to_numeric(f, target) {
                    CastNumericResult::Int(v) => Ok(Value::Int(v)),
                    CastNumericResult::Float(v) => Ok(Value::Float(v)),
                },
                Value::Bool(b) => match cast_bool_to_numeric(b, target) {
                    CastNumericResult::Int(v) => Ok(Value::Int(v)),
                    CastNumericResult::Float(v) => Ok(Value::Float(v)),
                },
                _ => Err(CompileError::Semantic(format!(
                    "cannot cast {} to {}",
                    val.type_name(),
                    target.name()
                ))),
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_numeric_type_from_name() {
        assert_eq!(NumericType::from_name("i8"), Some(NumericType::I8));
        assert_eq!(NumericType::from_name("i64"), Some(NumericType::I64));
        assert_eq!(NumericType::from_name("int"), Some(NumericType::I64));
        assert_eq!(NumericType::from_name("f64"), Some(NumericType::F64));
        assert_eq!(NumericType::from_name("float"), Some(NumericType::F64));
        assert_eq!(NumericType::from_name("unknown"), None);
    }

    #[test]
    fn test_cast_int_to_numeric() {
        // i64 -> i8 truncation
        assert_eq!(
            cast_int_to_numeric(300, NumericType::I8),
            CastNumericResult::Int(44) // 300 as i8 = 44
        );

        // i64 -> f64
        assert_eq!(
            cast_int_to_numeric(42, NumericType::F64),
            CastNumericResult::Float(42.0)
        );

        // i64 -> u8 (negative becomes positive due to wrap)
        assert_eq!(cast_int_to_numeric(-1, NumericType::U8), CastNumericResult::Int(255));
    }

    #[test]
    fn test_cast_float_to_numeric() {
        // f64 -> i64 truncation
        assert_eq!(cast_float_to_numeric(3.7, NumericType::I64), CastNumericResult::Int(3));

        // f64 -> f32 precision loss
        let result = cast_float_to_numeric(1.1, NumericType::F32);
        if let CastNumericResult::Float(f) = result {
            assert!((f - 1.1).abs() < 0.001);
        }
    }

    #[test]
    fn test_cast_bool_to_numeric() {
        assert_eq!(cast_bool_to_numeric(true, NumericType::I64), CastNumericResult::Int(1));
        assert_eq!(
            cast_bool_to_numeric(false, NumericType::F64),
            CastNumericResult::Float(0.0)
        );
    }

    #[test]
    fn test_bool_cast() {
        assert!(bool_cast::from_int(1));
        assert!(!bool_cast::from_int(0));
        assert!(bool_cast::from_float(0.1));
        assert!(!bool_cast::from_float(0.0));
        assert!(bool_cast::from_str("hello"));
        assert!(!bool_cast::from_str(""));
    }

    #[test]
    fn test_string_cast() {
        assert_eq!(string_cast::from_int(42), "42");
        assert_eq!(string_cast::from_float(2.75), "2.75");
        assert_eq!(string_cast::from_bool(true), "true");
    }
}
