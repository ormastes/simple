//! Unified type coercion rules for Simple language.
//!
//! These rules define how values are converted between types.
//! Both interpreter evaluation and codegen must follow these rules.

/// Result of a type coercion operation.
#[derive(Debug, Clone, PartialEq)]
pub enum CoercionResult<T> {
    /// Coercion succeeded with the given value.
    Ok(T),
    /// Coercion not possible between these types.
    Incompatible { from: &'static str, to: &'static str },
    /// Coercion would lose precision.
    PrecisionLoss { from: &'static str, to: &'static str },
}

impl<T> CoercionResult<T> {
    pub fn ok(value: T) -> Self {
        CoercionResult::Ok(value)
    }

    pub fn incompatible(from: &'static str, to: &'static str) -> Self {
        CoercionResult::Incompatible { from, to }
    }

    pub fn is_ok(&self) -> bool {
        matches!(self, CoercionResult::Ok(_))
    }

    pub fn unwrap(self) -> T {
        match self {
            CoercionResult::Ok(v) => v,
            _ => panic!("called unwrap on non-Ok CoercionResult"),
        }
    }
}

/// Type coercion rules.
///
/// These rules must be identical for interpreter and codegen.
pub struct TypeCoercion;

impl TypeCoercion {
    //==========================================================================
    // Integer coercions
    //==========================================================================

    /// Coerce any numeric value to i64.
    ///
    /// Rules:
    /// - Int(i) -> i (identity)
    /// - Float(f) -> truncate to i64
    /// - Bool(b) -> 1 if true, 0 if false
    /// - Nil -> 0
    pub fn to_int_i64(
        from_int: Option<i64>,
        from_float: Option<f64>,
        from_bool: Option<bool>,
        is_nil: bool,
    ) -> CoercionResult<i64> {
        if let Some(i) = from_int {
            return CoercionResult::ok(i);
        }
        if let Some(f) = from_float {
            return CoercionResult::ok(f as i64);
        }
        if let Some(b) = from_bool {
            return CoercionResult::ok(if b { 1 } else { 0 });
        }
        if is_nil {
            return CoercionResult::ok(0);
        }
        CoercionResult::incompatible("unknown", "i64")
    }

    /// Coerce numeric to specific integer type with overflow check.
    pub fn to_int_with_width(value: i64, target_bits: u8, signed: bool) -> CoercionResult<i64> {
        let (min, max) = if signed {
            match target_bits {
                8 => (i8::MIN as i64, i8::MAX as i64),
                16 => (i16::MIN as i64, i16::MAX as i64),
                32 => (i32::MIN as i64, i32::MAX as i64),
                64 => (i64::MIN, i64::MAX),
                _ => return CoercionResult::incompatible("i64", "int"),
            }
        } else {
            match target_bits {
                8 => (0, u8::MAX as i64),
                16 => (0, u16::MAX as i64),
                32 => (0, u32::MAX as i64),
                64 => (0, i64::MAX), // u64::MAX can't fit in i64
                _ => return CoercionResult::incompatible("i64", "uint"),
            }
        };

        if value >= min && value <= max {
            CoercionResult::ok(value)
        } else {
            CoercionResult::PrecisionLoss { from: "i64", to: "int" }
        }
    }

    //==========================================================================
    // Float coercions
    //==========================================================================

    /// Coerce any numeric value to f64.
    ///
    /// Rules:
    /// - Float(f) -> f (identity)
    /// - Int(i) -> i as f64
    /// - Bool(b) -> 1.0 if true, 0.0 if false
    /// - Nil -> 0.0
    pub fn to_float_f64(
        from_float: Option<f64>,
        from_int: Option<i64>,
        from_bool: Option<bool>,
        is_nil: bool,
    ) -> CoercionResult<f64> {
        if let Some(f) = from_float {
            return CoercionResult::ok(f);
        }
        if let Some(i) = from_int {
            return CoercionResult::ok(i as f64);
        }
        if let Some(b) = from_bool {
            return CoercionResult::ok(if b { 1.0 } else { 0.0 });
        }
        if is_nil {
            return CoercionResult::ok(0.0);
        }
        CoercionResult::incompatible("unknown", "f64")
    }

    /// Coerce f64 to f32 (with potential precision loss).
    pub fn f64_to_f32(value: f64) -> CoercionResult<f32> {
        let as_f32 = value as f32;
        // Check if we lost too much precision
        if (as_f32 as f64 - value).abs() > f64::EPSILON * 1000.0 {
            CoercionResult::PrecisionLoss { from: "f64", to: "f32" }
        } else {
            CoercionResult::ok(as_f32)
        }
    }

    //==========================================================================
    // Bool coercions
    //==========================================================================

    /// Coerce any value to bool using truthiness rules.
    ///
    /// This delegates to TruthinessRules for consistency.
    pub fn to_bool(
        from_bool: Option<bool>,
        from_int: Option<i64>,
        from_float: Option<f64>,
        is_empty_collection: Option<bool>,
        is_nil: bool,
    ) -> bool {
        use super::TruthinessRules;
        TruthinessRules::is_truthy(from_bool, from_int, from_float, is_empty_collection, is_nil)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_coercion() {
        // Int identity
        assert_eq!(TypeCoercion::to_int_i64(Some(42), None, None, false).unwrap(), 42);

        // Float truncation
        assert_eq!(TypeCoercion::to_int_i64(None, Some(3.7), None, false).unwrap(), 3);
        assert_eq!(TypeCoercion::to_int_i64(None, Some(-3.7), None, false).unwrap(), -3);

        // Bool to int
        assert_eq!(TypeCoercion::to_int_i64(None, None, Some(true), false).unwrap(), 1);
        assert_eq!(TypeCoercion::to_int_i64(None, None, Some(false), false).unwrap(), 0);

        // Nil to int
        assert_eq!(TypeCoercion::to_int_i64(None, None, None, true).unwrap(), 0);
    }

    #[test]
    fn test_float_coercion() {
        // Float identity
        assert_eq!(TypeCoercion::to_float_f64(Some(3.25), None, None, false).unwrap(), 3.25);

        // Int to float
        assert_eq!(TypeCoercion::to_float_f64(None, Some(42), None, false).unwrap(), 42.0);

        // Bool to float
        assert_eq!(TypeCoercion::to_float_f64(None, None, Some(true), false).unwrap(), 1.0);
        assert_eq!(TypeCoercion::to_float_f64(None, None, Some(false), false).unwrap(), 0.0);
    }

    #[test]
    fn test_int_width() {
        // i8 range
        assert!(TypeCoercion::to_int_with_width(127, 8, true).is_ok());
        assert!(!TypeCoercion::to_int_with_width(128, 8, true).is_ok());

        // u8 range
        assert!(TypeCoercion::to_int_with_width(255, 8, false).is_ok());
        assert!(!TypeCoercion::to_int_with_width(256, 8, false).is_ok());
    }
}
