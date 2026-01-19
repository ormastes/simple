//! Unified binary operation semantics for Simple language.
//!
//! This module defines the semantic rules for all binary operations.
//! Both interpreter and codegen must follow these rules for consistency.

use simple_parser::BinOp;

/// Result of a binary operation.
#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOpResult {
    /// Integer result
    Int(i64),
    /// Float result
    Float(f64),
    /// Boolean result
    Bool(bool),
    /// String result (for concatenation)
    String(String),
    /// Error occurred
    Error(String),
}

impl BinaryOpResult {
    pub fn int(v: i64) -> Self {
        BinaryOpResult::Int(v)
    }

    pub fn float(v: f64) -> Self {
        BinaryOpResult::Float(v)
    }

    pub fn bool(v: bool) -> Self {
        BinaryOpResult::Bool(v)
    }

    pub fn string(v: String) -> Self {
        BinaryOpResult::String(v)
    }

    pub fn error(msg: impl Into<String>) -> Self {
        BinaryOpResult::Error(msg.into())
    }

    pub fn is_error(&self) -> bool {
        matches!(self, BinaryOpResult::Error(_))
    }
}

/// Binary operation semantics.
///
/// These are the canonical semantic rules for all binary operations.
/// The interpreter evaluates these directly; codegen emits instructions
/// that produce equivalent results.
pub struct BinaryOpSemantics;

impl BinaryOpSemantics {
    //==========================================================================
    // Integer operations
    //==========================================================================

    /// Perform binary operation on two integers.
    pub fn eval_int_int(op: &BinOp, left: i64, right: i64) -> BinaryOpResult {
        match op {
            // Arithmetic
            BinOp::Add => BinaryOpResult::int(left.wrapping_add(right)),
            BinOp::Sub => BinaryOpResult::int(left.wrapping_sub(right)),
            BinOp::Mul => BinaryOpResult::int(left.wrapping_mul(right)),
            BinOp::Div => {
                if right == 0 {
                    BinaryOpResult::error("division by zero")
                } else {
                    BinaryOpResult::int(left / right)
                }
            }
            BinOp::Mod => {
                if right == 0 {
                    BinaryOpResult::error("modulo by zero")
                } else {
                    BinaryOpResult::int(left % right)
                }
            }
            BinOp::FloorDiv => {
                if right == 0 {
                    BinaryOpResult::error("floor division by zero")
                } else {
                    // Python-style floor division
                    let result = left / right;
                    let remainder = left % right;
                    if (remainder != 0) && ((left < 0) != (right < 0)) {
                        BinaryOpResult::int(result - 1)
                    } else {
                        BinaryOpResult::int(result)
                    }
                }
            }
            BinOp::Pow => BinaryOpResult::int(Self::int_pow(left, right)),

            // Comparison
            BinOp::Eq => BinaryOpResult::bool(left == right),
            BinOp::NotEq => BinaryOpResult::bool(left != right),
            BinOp::Lt => BinaryOpResult::bool(left < right),
            BinOp::LtEq => BinaryOpResult::bool(left <= right),
            BinOp::Gt => BinaryOpResult::bool(left > right),
            BinOp::GtEq => BinaryOpResult::bool(left >= right),

            // Bitwise
            BinOp::BitAnd => BinaryOpResult::int(left & right),
            BinOp::BitOr => BinaryOpResult::int(left | right),
            BinOp::BitXor => BinaryOpResult::int(left ^ right),
            BinOp::ShiftLeft => BinaryOpResult::int(left << (right as u32)),
            BinOp::ShiftRight => BinaryOpResult::int(left >> (right as u32)),

            // Logical (short-circuit handled at call site)
            BinOp::And | BinOp::AndSuspend => BinaryOpResult::bool(left != 0 && right != 0),
            BinOp::Or | BinOp::OrSuspend => BinaryOpResult::bool(left != 0 || right != 0),

            _ => BinaryOpResult::error(format!("unsupported int operation: {:?}", op)),
        }
    }

    /// Integer power (iterative to avoid float precision issues).
    fn int_pow(base: i64, exp: i64) -> i64 {
        if exp < 0 {
            return 0; // Integer division rounds down for negative exponents
        }
        let mut result: i64 = 1;
        let mut base = base;
        let mut exp = exp as u64;
        while exp > 0 {
            if exp & 1 == 1 {
                result = result.wrapping_mul(base);
            }
            exp >>= 1;
            base = base.wrapping_mul(base);
        }
        result
    }

    //==========================================================================
    // Float operations
    //==========================================================================

    /// Perform binary operation on two floats.
    pub fn eval_float_float(op: &BinOp, left: f64, right: f64) -> BinaryOpResult {
        match op {
            // Arithmetic
            BinOp::Add => BinaryOpResult::float(left + right),
            BinOp::Sub => BinaryOpResult::float(left - right),
            BinOp::Mul => BinaryOpResult::float(left * right),
            BinOp::Div => BinaryOpResult::float(left / right), // Float div allows 0 (produces inf/nan)
            BinOp::Mod => BinaryOpResult::float(left % right),
            BinOp::FloorDiv => BinaryOpResult::float((left / right).floor()),
            BinOp::Pow => BinaryOpResult::float(left.powf(right)),

            // Comparison
            BinOp::Eq => BinaryOpResult::bool(left == right),
            BinOp::NotEq => BinaryOpResult::bool(left != right),
            BinOp::Lt => BinaryOpResult::bool(left < right),
            BinOp::LtEq => BinaryOpResult::bool(left <= right),
            BinOp::Gt => BinaryOpResult::bool(left > right),
            BinOp::GtEq => BinaryOpResult::bool(left >= right),

            // Logical
            BinOp::And | BinOp::AndSuspend => BinaryOpResult::bool(left != 0.0 && right != 0.0),
            BinOp::Or | BinOp::OrSuspend => BinaryOpResult::bool(left != 0.0 || right != 0.0),

            _ => BinaryOpResult::error(format!("unsupported float operation: {:?}", op)),
        }
    }

    //==========================================================================
    // Mixed type operations (int/float promotion)
    //==========================================================================

    /// Perform operation with int left, float right.
    /// Promotes int to float.
    pub fn eval_int_float(op: &BinOp, left: i64, right: f64) -> BinaryOpResult {
        Self::eval_float_float(op, left as f64, right)
    }

    /// Perform operation with float left, int right.
    /// Promotes int to float.
    pub fn eval_float_int(op: &BinOp, left: f64, right: i64) -> BinaryOpResult {
        Self::eval_float_float(op, left, right as f64)
    }

    //==========================================================================
    // String operations
    //==========================================================================

    /// Perform binary operation on strings.
    pub fn eval_string_string(op: &BinOp, left: &str, right: &str) -> BinaryOpResult {
        match op {
            BinOp::Add => BinaryOpResult::string(format!("{}{}", left, right)),
            BinOp::Eq => BinaryOpResult::bool(left == right),
            BinOp::NotEq => BinaryOpResult::bool(left != right),
            BinOp::Lt => BinaryOpResult::bool(left < right),
            BinOp::LtEq => BinaryOpResult::bool(left <= right),
            BinOp::Gt => BinaryOpResult::bool(left > right),
            BinOp::GtEq => BinaryOpResult::bool(left >= right),
            _ => BinaryOpResult::error(format!("unsupported string operation: {:?}", op)),
        }
    }

    /// String repetition: "ab" * 3 = "ababab"
    pub fn eval_string_int(op: &BinOp, left: &str, right: i64) -> BinaryOpResult {
        match op {
            BinOp::Mul => {
                if right < 0 {
                    BinaryOpResult::string(String::new())
                } else {
                    BinaryOpResult::string(left.repeat(right as usize))
                }
            }
            _ => BinaryOpResult::error(format!("unsupported string*int operation: {:?}", op)),
        }
    }

    //==========================================================================
    // Boolean operations
    //==========================================================================

    /// Perform binary operation on booleans.
    pub fn eval_bool_bool(op: &BinOp, left: bool, right: bool) -> BinaryOpResult {
        match op {
            BinOp::And | BinOp::AndSuspend => BinaryOpResult::bool(left && right),
            BinOp::Or | BinOp::OrSuspend => BinaryOpResult::bool(left || right),
            BinOp::Eq => BinaryOpResult::bool(left == right),
            BinOp::NotEq => BinaryOpResult::bool(left != right),
            // Bool comparison: false < true
            BinOp::Lt => BinaryOpResult::bool(!left && right),
            BinOp::LtEq => BinaryOpResult::bool(!left || right),
            BinOp::Gt => BinaryOpResult::bool(left && !right),
            BinOp::GtEq => BinaryOpResult::bool(left || !right),
            _ => BinaryOpResult::error(format!("unsupported bool operation: {:?}", op)),
        }
    }

    //==========================================================================
    // Short-circuit evaluation helpers
    //==========================================================================

    /// Check if an operation is short-circuit.
    pub fn is_short_circuit(op: &BinOp) -> bool {
        matches!(op, BinOp::And | BinOp::AndSuspend | BinOp::Or | BinOp::OrSuspend)
    }

    /// For short-circuit AND: if left is falsy, result is left (don't eval right).
    pub fn short_circuit_and_result(left_truthy: bool) -> Option<bool> {
        if !left_truthy {
            Some(false)
        } else {
            None // Need to evaluate right
        }
    }

    /// For short-circuit OR: if left is truthy, result is left (don't eval right).
    pub fn short_circuit_or_result(left_truthy: bool) -> Option<bool> {
        if left_truthy {
            Some(true)
        } else {
            None // Need to evaluate right
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_arithmetic() {
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Add, 3, 5),
            BinaryOpResult::int(8)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Sub, 10, 3),
            BinaryOpResult::int(7)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Mul, 4, 5),
            BinaryOpResult::int(20)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Div, 17, 5),
            BinaryOpResult::int(3)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Mod, 17, 5),
            BinaryOpResult::int(2)
        );
    }

    #[test]
    fn test_int_pow() {
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Pow, 2, 10),
            BinaryOpResult::int(1024)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Pow, 3, 4),
            BinaryOpResult::int(81)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Pow, 5, 0),
            BinaryOpResult::int(1)
        );
    }

    #[test]
    fn test_floor_div() {
        // Python-style floor division
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::FloorDiv, 7, 3),
            BinaryOpResult::int(2)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::FloorDiv, -7, 3),
            BinaryOpResult::int(-3)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::FloorDiv, 7, -3),
            BinaryOpResult::int(-3)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::FloorDiv, -7, -3),
            BinaryOpResult::int(2)
        );
    }

    #[test]
    fn test_int_comparison() {
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Eq, 5, 5),
            BinaryOpResult::bool(true)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Eq, 5, 3),
            BinaryOpResult::bool(false)
        );
        assert_eq!(
            BinaryOpSemantics::eval_int_int(&BinOp::Lt, 3, 5),
            BinaryOpResult::bool(true)
        );
    }

    #[test]
    fn test_float_arithmetic() {
        assert_eq!(
            BinaryOpSemantics::eval_float_float(&BinOp::Add, 1.5, 2.5),
            BinaryOpResult::float(4.0)
        );
        assert_eq!(
            BinaryOpSemantics::eval_float_float(&BinOp::Mul, 2.0, 3.0),
            BinaryOpResult::float(6.0)
        );
    }

    #[test]
    fn test_string_ops() {
        assert_eq!(
            BinaryOpSemantics::eval_string_string(&BinOp::Add, "hello", " world"),
            BinaryOpResult::string("hello world".to_string())
        );
        assert_eq!(
            BinaryOpSemantics::eval_string_int(&BinOp::Mul, "ab", 3),
            BinaryOpResult::string("ababab".to_string())
        );
    }

    #[test]
    fn test_division_by_zero() {
        assert!(BinaryOpSemantics::eval_int_int(&BinOp::Div, 5, 0).is_error());
        assert!(BinaryOpSemantics::eval_int_int(&BinOp::Mod, 5, 0).is_error());
    }

    #[test]
    fn test_short_circuit() {
        assert!(BinaryOpSemantics::is_short_circuit(&BinOp::And));
        assert!(BinaryOpSemantics::is_short_circuit(&BinOp::Or));
        assert!(!BinaryOpSemantics::is_short_circuit(&BinOp::Add));

        assert_eq!(BinaryOpSemantics::short_circuit_and_result(false), Some(false));
        assert_eq!(BinaryOpSemantics::short_circuit_and_result(true), None);
        assert_eq!(BinaryOpSemantics::short_circuit_or_result(true), Some(true));
        assert_eq!(BinaryOpSemantics::short_circuit_or_result(false), None);
    }
}
