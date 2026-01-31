//! Safety Macros - Convenient macros for safe operations
//!
//! This module provides convenient macros that wrap the safety infrastructure.

/// Safe arithmetic operation macro
///
/// # Examples
///
/// ```
/// use simple_common::safe_add;
///
/// let result = safe_add(5, 10);
/// assert_eq!(result.unwrap(), 15);
///
/// let overflow = safe_add(i32::MAX, 1);
/// assert!(overflow.is_err());
/// ```
///
/// Note: Use the functions directly (safe_add, safe_sub, safe_mul, safe_div)
/// instead of macros for better type inference and error messages.

/// Safe array indexing macro
///
/// # Examples
///
/// ```
/// use simple_common::safe_idx;
///
/// let arr = [1, 2, 3, 4, 5];
/// let val = safe_idx!(arr, 2);
/// assert_eq!(*val.unwrap(), 3);
///
/// let out_of_bounds = safe_idx!(arr, 10);
/// assert!(out_of_bounds.is_err());
/// ```
#[macro_export]
macro_rules! safe_idx {
    ($slice:expr, $index:expr) => {
        $crate::safety::safe_index(&$slice, $index)
    };
}

/// Safe mutable array indexing macro
#[macro_export]
macro_rules! safe_idx_mut {
    ($slice:expr, $index:expr) => {
        $crate::safety::safe_index_mut(&mut $slice, $index)
    };
}

/// Safe mutex lock macro with context
///
/// # Examples
///
/// ```
/// use simple_common::safe_mutex_lock;
/// use std::sync::Mutex;
///
/// let data = Mutex::new(42);
/// let guard = safe_mutex_lock!(data, "accessing counter");
/// assert_eq!(*guard, 42);
/// ```
#[macro_export]
macro_rules! safe_mutex_lock {
    ($mutex:expr, $context:expr) => {
        $crate::safety::safe_lock(&$mutex, $context)
    };
}

/// Checked unwrap with custom error message
///
/// Like unwrap() but with a better error message that includes the location
///
/// # Examples
///
/// ```should_panic
/// use simple_common::checked_unwrap;
///
/// let opt: Option<i32> = None;
/// checked_unwrap!(opt, "expected value to be present");
/// ```
#[macro_export]
macro_rules! checked_unwrap {
    ($expr:expr, $msg:expr) => {
        $expr.unwrap_or_else(|| {
            panic!(
                "{}:{}: {} - {}",
                file!(),
                line!(),
                $msg,
                stringify!($expr)
            )
        })
    };
}

/// Checked expect - like expect() but with file/line info
#[macro_export]
macro_rules! checked_expect {
    ($expr:expr, $msg:expr) => {
        $expr.expect(&format!("{}:{}: {}", file!(), line!(), $msg))
    };
}

/// Assert with safe arithmetic
///
/// # Examples
///
/// ```
/// use simple_common::safe_add;
///
/// assert_eq!(safe_add(10, 20).unwrap(), 30);
/// ```
///
/// Note: Use the functions directly with assert_eq! for better error messages.

#[cfg(test)]
mod tests {
    use crate::safety::{safe_add, safe_sub, safe_mul, safe_div};

    #[test]
    fn test_safe_arithmetic_functions() {
        assert_eq!(safe_add(5, 10).unwrap(), 15);
        assert_eq!(safe_sub(20, 5).unwrap(), 15);
        assert_eq!(safe_mul(3, 5).unwrap(), 15);
        assert_eq!(safe_div(30, 2).unwrap(), 15);
    }

    #[test]
    fn test_safe_idx_macro() {
        let arr = [1, 2, 3, 4, 5];
        let val = safe_idx!(arr, 2);
        assert_eq!(*val.unwrap(), 3);
    }
}
