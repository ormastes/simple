//! Safety Infrastructure - Common safe wrappers and utilities
//!
//! This module provides safe alternatives to common unsafe patterns:
//! - Checked arithmetic (no silent overflow)
//! - Safe array indexing (bounds checking with good errors)
//! - Safe mutex operations (better error messages)
//! - Safe string operations (UTF-8 aware)
//! - Safe type conversions (explicit overflow handling)

use std::fmt;
use std::ops::{Add, Sub, Mul, Div};
use std::sync::{Mutex, MutexGuard, PoisonError};

// ============================================
// Safe Arithmetic Operations
// ============================================

/// Error type for arithmetic operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArithmeticError {
    Overflow { op: &'static str, a: String, b: String },
    Underflow { op: &'static str, a: String, b: String },
    DivisionByZero { dividend: String },
}

impl fmt::Display for ArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArithmeticError::Overflow { op, a, b } => {
                write!(f, "arithmetic overflow: {} {} {}", a, op, b)
            }
            ArithmeticError::Underflow { op, a, b } => {
                write!(f, "arithmetic underflow: {} {} {}", a, op, b)
            }
            ArithmeticError::DivisionByZero { dividend } => {
                write!(f, "division by zero: {} / 0", dividend)
            }
        }
    }
}

impl std::error::Error for ArithmeticError {}

/// Safe addition with overflow checking
pub fn safe_add<T>(a: T, b: T) -> Result<T, ArithmeticError>
where
    T: Add<Output = T> + fmt::Display + CheckedAdd + Copy,
{
    let a_str = a.to_string();
    let b_str = b.to_string();
    a.checked_add(b).ok_or_else(|| ArithmeticError::Overflow {
        op: "+",
        a: a_str,
        b: b_str,
    })
}

/// Safe subtraction with underflow checking
pub fn safe_sub<T>(a: T, b: T) -> Result<T, ArithmeticError>
where
    T: Sub<Output = T> + fmt::Display + CheckedSub + Copy,
{
    let a_str = a.to_string();
    let b_str = b.to_string();
    a.checked_sub(b).ok_or_else(|| ArithmeticError::Underflow {
        op: "-",
        a: a_str,
        b: b_str,
    })
}

/// Safe multiplication with overflow checking
pub fn safe_mul<T>(a: T, b: T) -> Result<T, ArithmeticError>
where
    T: Mul<Output = T> + fmt::Display + CheckedMul + Copy,
{
    let a_str = a.to_string();
    let b_str = b.to_string();
    a.checked_mul(b).ok_or_else(|| ArithmeticError::Overflow {
        op: "*",
        a: a_str,
        b: b_str,
    })
}

/// Safe division with zero checking
pub fn safe_div<T>(a: T, b: T) -> Result<T, ArithmeticError>
where
    T: Div<Output = T> + fmt::Display + CheckedDiv + PartialEq + Default + Copy,
{
    if b == T::default() {
        return Err(ArithmeticError::DivisionByZero {
            dividend: a.to_string(),
        });
    }
    let a_str = a.to_string();
    let b_str = b.to_string();
    a.checked_div(b).ok_or_else(|| ArithmeticError::Overflow {
        op: "/",
        a: a_str,
        b: b_str,
    })
}

// Trait definitions for checked operations
pub trait CheckedAdd: Sized {
    fn checked_add(self, rhs: Self) -> Option<Self>;
}

pub trait CheckedSub: Sized {
    fn checked_sub(self, rhs: Self) -> Option<Self>;
}

pub trait CheckedMul: Sized {
    fn checked_mul(self, rhs: Self) -> Option<Self>;
}

pub trait CheckedDiv: Sized {
    fn checked_div(self, rhs: Self) -> Option<Self>;
}

// Implementations for standard integer types
macro_rules! impl_checked_ops {
    ($($t:ty),*) => {
        $(
            impl CheckedAdd for $t {
                fn checked_add(self, rhs: Self) -> Option<Self> {
                    <$t>::checked_add(self, rhs)
                }
            }
            impl CheckedSub for $t {
                fn checked_sub(self, rhs: Self) -> Option<Self> {
                    <$t>::checked_sub(self, rhs)
                }
            }
            impl CheckedMul for $t {
                fn checked_mul(self, rhs: Self) -> Option<Self> {
                    <$t>::checked_mul(self, rhs)
                }
            }
            impl CheckedDiv for $t {
                fn checked_div(self, rhs: Self) -> Option<Self> {
                    <$t>::checked_div(self, rhs)
                }
            }
        )*
    };
}

impl_checked_ops!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

// ============================================
// Safe Type Conversions
// ============================================

/// Error type for type conversions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConversionError {
    Overflow { from: String, to: &'static str, value: String },
    NegativeToUnsigned { value: String },
}

impl fmt::Display for ConversionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConversionError::Overflow { from, to, value } => {
                write!(f, "conversion overflow: {} ({}) does not fit in {}", value, from, to)
            }
            ConversionError::NegativeToUnsigned { value } => {
                write!(f, "cannot convert negative value {} to unsigned type", value)
            }
        }
    }
}

impl std::error::Error for ConversionError {}

/// Safe conversion to usize
pub fn to_usize<T>(value: T) -> Result<usize, ConversionError>
where
    T: TryInto<usize> + fmt::Display + Copy,
{
    value.try_into().map_err(|_| ConversionError::Overflow {
        from: std::any::type_name::<T>().to_string(),
        to: "usize",
        value: value.to_string(),
    })
}

/// Safe conversion to i64
pub fn to_i64<T>(value: T) -> Result<i64, ConversionError>
where
    T: TryInto<i64> + fmt::Display + Copy,
{
    value.try_into().map_err(|_| ConversionError::Overflow {
        from: std::any::type_name::<T>().to_string(),
        to: "i64",
        value: value.to_string(),
    })
}

/// Safe conversion to u64
pub fn to_u64<T>(value: T) -> Result<u64, ConversionError>
where
    T: TryInto<u64> + fmt::Display + Copy,
{
    value.try_into().map_err(|_| ConversionError::Overflow {
        from: std::any::type_name::<T>().to_string(),
        to: "u64",
        value: value.to_string(),
    })
}

/// Safe conversion to i32
pub fn to_i32<T>(value: T) -> Result<i32, ConversionError>
where
    T: TryInto<i32> + fmt::Display + Copy,
{
    value.try_into().map_err(|_| ConversionError::Overflow {
        from: std::any::type_name::<T>().to_string(),
        to: "i32",
        value: value.to_string(),
    })
}

/// Safe conversion to u32
pub fn to_u32<T>(value: T) -> Result<u32, ConversionError>
where
    T: TryInto<u32> + fmt::Display + Copy,
{
    value.try_into().map_err(|_| ConversionError::Overflow {
        from: std::any::type_name::<T>().to_string(),
        to: "u32",
        value: value.to_string(),
    })
}

// ============================================
// Safe Array Indexing
// ============================================

/// Error type for indexing operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndexError {
    OutOfBounds { index: usize, len: usize },
    NegativeIndex { index: i64, len: usize },
}

impl fmt::Display for IndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IndexError::OutOfBounds { index, len } => {
                write!(f, "index out of bounds: index is {} but length is {}", index, len)
            }
            IndexError::NegativeIndex { index, len } => {
                write!(f, "negative index out of bounds: index is {} but length is {}", index, len)
            }
        }
    }
}

impl std::error::Error for IndexError {}

/// Safe array indexing with bounds checking
pub fn safe_index<T>(slice: &[T], index: usize) -> Result<&T, IndexError> {
    slice.get(index).ok_or_else(|| IndexError::OutOfBounds {
        index,
        len: slice.len(),
    })
}

/// Safe mutable array indexing with bounds checking
pub fn safe_index_mut<T>(slice: &mut [T], index: usize) -> Result<&mut T, IndexError> {
    let len = slice.len();
    slice.get_mut(index).ok_or_else(|| IndexError::OutOfBounds {
        index,
        len,
    })
}

/// Safe indexing with negative index support (Python-style)
pub fn safe_index_signed<T>(slice: &[T], index: i64) -> Result<&T, IndexError> {
    let len = slice.len();
    let actual_index = if index < 0 {
        let abs_index = (-index) as usize;
        if abs_index > len {
            return Err(IndexError::NegativeIndex { index, len });
        }
        len - abs_index
    } else {
        index as usize
    };

    safe_index(slice, actual_index)
}

/// Safe mutable indexing with negative index support
pub fn safe_index_mut_signed<T>(slice: &mut [T], index: i64) -> Result<&mut T, IndexError> {
    let len = slice.len();
    let actual_index = if index < 0 {
        let abs_index = (-index) as usize;
        if abs_index > len {
            return Err(IndexError::NegativeIndex { index, len });
        }
        len - abs_index
    } else {
        index as usize
    };

    safe_index_mut(slice, actual_index)
}

// ============================================
// Safe Mutex Operations
// ============================================

/// Safe mutex lock with descriptive error message
pub fn safe_lock<'a, T>(mutex: &'a Mutex<T>, context: &str) -> MutexGuard<'a, T> {
    mutex.lock().unwrap_or_else(|e| {
        panic!("Mutex poisoned in context '{}': {}", context, e)
    })
}

/// Try to lock mutex with custom error handling
pub fn try_lock<'a, T, E>(
    mutex: &'a Mutex<T>,
    context: &str,
    error_fn: impl FnOnce(String) -> E,
) -> Result<MutexGuard<'a, T>, E> {
    mutex.lock().map_err(|e| {
        error_fn(format!("Mutex poisoned in context '{}': {}", context, e))
    })
}

// ============================================
// Safe String Operations
// ============================================

/// Error type for string operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringError {
    InvalidUtf8Boundary { byte_index: usize },
    IndexOutOfBounds { char_index: usize, char_count: usize },
}

impl fmt::Display for StringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StringError::InvalidUtf8Boundary { byte_index } => {
                write!(f, "invalid UTF-8 boundary at byte index {}", byte_index)
            }
            StringError::IndexOutOfBounds { char_index, char_count } => {
                write!(f, "character index {} out of bounds (length: {})", char_index, char_count)
            }
        }
    }
}

impl std::error::Error for StringError {}

/// Safe character indexing (UTF-8 aware)
pub fn safe_char_at(s: &str, char_index: usize) -> Result<char, StringError> {
    s.chars()
        .nth(char_index)
        .ok_or_else(|| StringError::IndexOutOfBounds {
            char_index,
            char_count: s.chars().count(),
        })
}

/// Safe substring extraction (UTF-8 aware, by character indices)
pub fn safe_substring(s: &str, start: usize, end: usize) -> Result<String, StringError> {
    let char_count = s.chars().count();

    if start > char_count || end > char_count || start > end {
        return Err(StringError::IndexOutOfBounds {
            char_index: start.max(end),
            char_count,
        });
    }

    Ok(s.chars().skip(start).take(end - start).collect())
}

/// Safe byte slice to str conversion
pub fn safe_str_from_bytes(bytes: &[u8]) -> Result<&str, StringError> {
    std::str::from_utf8(bytes).map_err(|e| StringError::InvalidUtf8Boundary {
        byte_index: e.valid_up_to(),
    })
}

// ============================================
// Tests
// ============================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_add_overflow() {
        let result = safe_add(i32::MAX, 1);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ArithmeticError::Overflow { .. }));
    }

    #[test]
    fn test_safe_add_success() {
        assert_eq!(safe_add(5, 10).unwrap(), 15);
        assert_eq!(safe_add(0, 0).unwrap(), 0);
    }

    #[test]
    fn test_safe_sub_underflow() {
        let result = safe_sub(0u32, 1u32);
        assert!(result.is_err());
    }

    #[test]
    fn test_safe_div_zero() {
        let result = safe_div(10, 0);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ArithmeticError::DivisionByZero { .. }));
    }

    #[test]
    fn test_safe_index_success() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(*safe_index(&arr, 2).unwrap(), 3);
    }

    #[test]
    fn test_safe_index_out_of_bounds() {
        let arr = [1, 2, 3];
        let result = safe_index(&arr, 5);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), IndexError::OutOfBounds { index: 5, len: 3 }));
    }

    #[test]
    fn test_safe_index_signed_negative() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(*safe_index_signed(&arr, -1).unwrap(), 5);
        assert_eq!(*safe_index_signed(&arr, -2).unwrap(), 4);
    }

    #[test]
    fn test_safe_index_signed_out_of_bounds() {
        let arr = [1, 2, 3];
        let result = safe_index_signed(&arr, -5);
        assert!(result.is_err());
    }

    #[test]
    fn test_safe_char_at() {
        let s = "Hello 🌍 World";
        assert_eq!(safe_char_at(s, 0).unwrap(), 'H');
        assert_eq!(safe_char_at(s, 6).unwrap(), '🌍');
    }

    #[test]
    fn test_safe_char_at_out_of_bounds() {
        let s = "Hello";
        let result = safe_char_at(s, 10);
        assert!(result.is_err());
    }

    #[test]
    fn test_safe_substring() {
        let s = "Hello 🌍 World";
        assert_eq!(safe_substring(s, 0, 5).unwrap(), "Hello");
        assert_eq!(safe_substring(s, 6, 7).unwrap(), "🌍");
    }

    #[test]
    fn test_to_usize_overflow() {
        let result = to_usize(-1i32);
        assert!(result.is_err());
    }

    #[test]
    fn test_to_usize_success() {
        assert_eq!(to_usize(42u32).unwrap(), 42usize);
        assert_eq!(to_usize(100i32).unwrap(), 100usize);
    }
}
