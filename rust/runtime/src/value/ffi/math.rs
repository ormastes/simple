//! Math functions FFI for numerical operations.
//!
//! Provides C-compatible wrappers around Rust's f64 mathematical functions.
//! All functions operate on f64 values for maximum precision.
//!
//! ## Function Categories
//!
//! - **Power & Logarithm**: pow, exp, log, log10, log2
//! - **Roots**: sqrt, cbrt
//! - **Trigonometric**: sin, cos, tan, asin, acos, atan, atan2
//! - **Hyperbolic**: sinh, cosh, tanh
//! - **Rounding**: floor, ceil, round, trunc
//! - **Basic**: abs, hypot, gcd, min, max, clamp
//!
//! ## Usage Pattern
//!
//! All functions are simple f64 → f64 transformations:
//! ```
//! use simple_runtime::value::ffi::math::*;
//!
//! // Basic operations
//! assert_eq!(rt_math_sqrt(4.0), 2.0);
//! assert_eq!(rt_math_pow(2.0, 3.0), 8.0);
//!
//! // Trigonometric (with floating-point tolerance)
//! assert!((rt_math_sin(0.0) - 0.0).abs() < 1e-10);
//! assert!((rt_math_cos(0.0) - 1.0).abs() < 1e-10);
//! ```
//!
//! ## Special Values
//!
//! These functions preserve IEEE 754 special values:
//! - NaN inputs produce NaN outputs
//! - Infinity is handled according to mathematical definitions
//! - Domain errors (e.g., sqrt of negative) produce NaN

// ============================================================================
// Power & Logarithm Functions
// ============================================================================

/// Power function: base^exp
///
/// Computes base raised to the power of exp.
///
/// # Examples
/// - pow(2.0, 3.0) = 8.0
/// - pow(10.0, 2.0) = 100.0
/// - pow(2.0, -1.0) = 0.5
#[no_mangle]
pub extern "C" fn rt_math_pow(base: f64, exp: f64) -> f64 {
    base.powf(exp)
}

/// Natural logarithm (base e)
///
/// Returns NaN for x < 0, -infinity for x = 0.
///
/// # Examples
/// - log(e) = 1.0
/// - log(1.0) = 0.0
/// - log(e^2) = 2.0
#[no_mangle]
pub extern "C" fn rt_math_log(x: f64) -> f64 {
    x.ln()
}

/// Base-10 logarithm
///
/// Returns NaN for x < 0, -infinity for x = 0.
///
/// # Examples
/// - log10(10.0) = 1.0
/// - log10(100.0) = 2.0
/// - log10(1.0) = 0.0
#[no_mangle]
pub extern "C" fn rt_math_log10(x: f64) -> f64 {
    x.log10()
}

/// Base-2 logarithm
///
/// Returns NaN for x < 0, -infinity for x = 0.
///
/// # Examples
/// - log2(2.0) = 1.0
/// - log2(8.0) = 3.0
/// - log2(1.0) = 0.0
#[no_mangle]
pub extern "C" fn rt_math_log2(x: f64) -> f64 {
    x.log2()
}

/// Exponential function: e^x
///
/// # Examples
/// - exp(0.0) = 1.0
/// - exp(1.0) = e ≈ 2.718
/// - exp(2.0) = e^2 ≈ 7.389
#[no_mangle]
pub extern "C" fn rt_math_exp(x: f64) -> f64 {
    x.exp()
}

// ============================================================================
// Root Functions
// ============================================================================

/// Square root
///
/// Returns NaN for x < 0.
///
/// # Examples
/// - sqrt(4.0) = 2.0
/// - sqrt(9.0) = 3.0
/// - sqrt(0.0) = 0.0
#[no_mangle]
pub extern "C" fn rt_math_sqrt(x: f64) -> f64 {
    x.sqrt()
}

/// Cube root
///
/// Works for negative numbers (returns negative cube root).
///
/// # Examples
/// - cbrt(8.0) = 2.0
/// - cbrt(27.0) = 3.0
/// - cbrt(-8.0) = -2.0
#[no_mangle]
pub extern "C" fn rt_math_cbrt(x: f64) -> f64 {
    x.cbrt()
}

// ============================================================================
// Trigonometric Functions
// ============================================================================

/// Sine (radians)
///
/// # Examples
/// - sin(0.0) = 0.0
/// - sin(π/2) ≈ 1.0
/// - sin(π) ≈ 0.0
#[no_mangle]
pub extern "C" fn rt_math_sin(x: f64) -> f64 {
    x.sin()
}

/// Cosine (radians)
///
/// # Examples
/// - cos(0.0) = 1.0
/// - cos(π/2) ≈ 0.0
/// - cos(π) ≈ -1.0
#[no_mangle]
pub extern "C" fn rt_math_cos(x: f64) -> f64 {
    x.cos()
}

/// Tangent (radians)
///
/// # Examples
/// - tan(0.0) = 0.0
/// - tan(π/4) ≈ 1.0
#[no_mangle]
pub extern "C" fn rt_math_tan(x: f64) -> f64 {
    x.tan()
}

/// Arcsine (returns radians)
///
/// Returns NaN for |x| > 1.
/// Range: [-π/2, π/2]
///
/// # Examples
/// - asin(0.0) = 0.0
/// - asin(1.0) = π/2
/// - asin(-1.0) = -π/2
#[no_mangle]
pub extern "C" fn rt_math_asin(x: f64) -> f64 {
    x.asin()
}

/// Arccosine (returns radians)
///
/// Returns NaN for |x| > 1.
/// Range: [0, π]
///
/// # Examples
/// - acos(1.0) = 0.0
/// - acos(0.0) = π/2
/// - acos(-1.0) = π
#[no_mangle]
pub extern "C" fn rt_math_acos(x: f64) -> f64 {
    x.acos()
}

/// Arctangent (returns radians)
///
/// Range: (-π/2, π/2)
///
/// # Examples
/// - atan(0.0) = 0.0
/// - atan(1.0) = π/4
/// - atan(-1.0) = -π/4
#[no_mangle]
pub extern "C" fn rt_math_atan(x: f64) -> f64 {
    x.atan()
}

/// Two-argument arctangent (returns radians)
///
/// Computes atan(y/x) with proper quadrant handling.
/// Range: (-π, π]
///
/// # Examples
/// - atan2(0.0, 1.0) = 0.0 (positive x-axis)
/// - atan2(1.0, 0.0) = π/2 (positive y-axis)
/// - atan2(0.0, -1.0) = π (negative x-axis)
/// - atan2(-1.0, 0.0) = -π/2 (negative y-axis)
#[no_mangle]
pub extern "C" fn rt_math_atan2(y: f64, x: f64) -> f64 {
    y.atan2(x)
}

// ============================================================================
// Hyperbolic Functions
// ============================================================================

/// Hyperbolic sine
///
/// sinh(x) = (e^x - e^(-x)) / 2
///
/// # Examples
/// - sinh(0.0) = 0.0
/// - sinh(ln(2)) ≈ 0.75
#[no_mangle]
pub extern "C" fn rt_math_sinh(x: f64) -> f64 {
    x.sinh()
}

/// Hyperbolic cosine
///
/// cosh(x) = (e^x + e^(-x)) / 2
///
/// # Examples
/// - cosh(0.0) = 1.0
/// - cosh(ln(2)) ≈ 1.25
#[no_mangle]
pub extern "C" fn rt_math_cosh(x: f64) -> f64 {
    x.cosh()
}

/// Hyperbolic tangent
///
/// tanh(x) = sinh(x) / cosh(x)
///
/// # Examples
/// - tanh(0.0) = 0.0
/// - tanh(∞) = 1.0
/// - tanh(-∞) = -1.0
#[no_mangle]
pub extern "C" fn rt_math_tanh(x: f64) -> f64 {
    x.tanh()
}

// ============================================================================
// Rounding Functions
// ============================================================================

/// Floor (round down to nearest integer)
///
/// # Examples
/// - floor(3.7) = 3.0
/// - floor(-3.7) = -4.0
/// - floor(5.0) = 5.0
#[no_mangle]
pub extern "C" fn rt_math_floor(x: f64) -> f64 {
    x.floor()
}

/// Ceiling (round up to nearest integer)
///
/// # Examples
/// - ceil(3.2) = 4.0
/// - ceil(-3.2) = -3.0
/// - ceil(5.0) = 5.0
#[no_mangle]
pub extern "C" fn rt_math_ceil(x: f64) -> f64 {
    x.ceil()
}

/// Round to nearest integer (half away from zero)
///
/// # Examples
/// - round(3.5) = 4.0
/// - round(3.4) = 3.0
/// - round(-3.5) = -4.0
/// - round(-3.4) = -3.0
#[no_mangle]
pub extern "C" fn rt_math_round(x: f64) -> f64 {
    x.round()
}

/// Truncate toward zero (remove fractional part)
///
/// # Examples
/// - trunc(3.7) = 3.0
/// - trunc(-3.7) = -3.0
/// - trunc(5.0) = 5.0
#[no_mangle]
pub extern "C" fn rt_math_trunc(x: f64) -> f64 {
    x.trunc()
}

// ============================================================================
// Basic Functions
// ============================================================================

/// Absolute value
///
/// Returns the magnitude of x (always non-negative).
///
/// # Examples
/// - abs(5.0) = 5.0
/// - abs(-5.0) = 5.0
/// - abs(0.0) = 0.0
#[no_mangle]
pub extern "C" fn rt_math_abs(x: f64) -> f64 {
    x.abs()
}

/// Hypotenuse: sqrt(x² + y²)
///
/// Computes the length of the hypotenuse of a right triangle
/// with sides x and y. Handles overflow/underflow better than
/// computing sqrt(x*x + y*y) directly.
///
/// # Examples
/// - hypot(3.0, 4.0) = 5.0
/// - hypot(5.0, 12.0) = 13.0
/// - hypot(1.0, 1.0) ≈ 1.414
#[no_mangle]
pub extern "C" fn rt_math_hypot(x: f64, y: f64) -> f64 {
    x.hypot(y)
}

/// Greatest common divisor (GCD) using Euclidean algorithm
///
/// Returns the largest positive integer that divides both a and b.
/// Works with negative numbers (returns positive GCD).
/// Returns 0 if both inputs are 0.
///
/// # Examples
/// - gcd(12, 8) = 4
/// - gcd(54, 24) = 6
/// - gcd(17, 13) = 1 (coprime)
/// - gcd(-12, 8) = 4
#[no_mangle]
pub extern "C" fn rt_math_gcd(a: i64, b: i64) -> i64 {
    let mut a = a.abs();
    let mut b = b.abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Least common multiple (LCM)
///
/// Returns the smallest positive integer that is divisible by both a and b.
/// Returns 0 if either input is 0.
///
/// # Examples
/// - lcm(4, 6) = 12
/// - lcm(3, 5) = 15
/// - lcm(12, 8) = 24
#[no_mangle]
pub extern "C" fn rt_math_lcm(a: i64, b: i64) -> i64 {
    if a == 0 || b == 0 {
        return 0;
    }
    let gcd = rt_math_gcd(a, b);
    (a.abs() / gcd) * b.abs()
}

/// Minimum of two values
///
/// Returns the smaller of x and y.
/// If either value is NaN, returns NaN.
///
/// # Examples
/// - min(3.0, 5.0) = 3.0
/// - min(-2.0, 1.0) = -2.0
/// - min(4.0, 4.0) = 4.0
#[no_mangle]
pub extern "C" fn rt_math_min(x: f64, y: f64) -> f64 {
    x.min(y)
}

/// Maximum of two values
///
/// Returns the larger of x and y.
/// If either value is NaN, returns NaN.
///
/// # Examples
/// - max(3.0, 5.0) = 5.0
/// - max(-2.0, 1.0) = 1.0
/// - max(4.0, 4.0) = 4.0
#[no_mangle]
pub extern "C" fn rt_math_max(x: f64, y: f64) -> f64 {
    x.max(y)
}

/// Clamp value to range [min, max]
///
/// Returns min if x < min, max if x > max, otherwise x.
///
/// # Examples
/// - clamp(5.0, 0.0, 10.0) = 5.0
/// - clamp(-5.0, 0.0, 10.0) = 0.0
/// - clamp(15.0, 0.0, 10.0) = 10.0
#[no_mangle]
pub extern "C" fn rt_math_clamp(x: f64, min: f64, max: f64) -> f64 {
    x.clamp(min, max)
}

/// Sign function
///
/// Returns 1.0 if x > 0, -1.0 if x < 0, 0.0 if x == 0.
/// Returns NaN if x is NaN.
///
/// # Examples
/// - sign(5.0) = 1.0
/// - sign(-5.0) = -1.0
/// - sign(0.0) = 0.0
#[no_mangle]
pub extern "C" fn rt_math_sign(x: f64) -> f64 {
    if x.is_nan() {
        f64::NAN
    } else if x > 0.0 {
        1.0
    } else if x < 0.0 {
        -1.0
    } else {
        0.0
    }
}

/// Fractional part of x
///
/// Returns the fractional (decimal) part of x.
/// fract(x) = x - trunc(x)
///
/// # Examples
/// - fract(3.7) = 0.7
/// - fract(-3.7) = -0.7
/// - fract(5.0) = 0.0
#[no_mangle]
pub extern "C" fn rt_math_fract(x: f64) -> f64 {
    x.fract()
}

/// Modulo (remainder) operation
///
/// Returns the remainder of x / y.
/// The result has the same sign as x.
///
/// # Examples
/// - rem(7.0, 3.0) = 1.0
/// - rem(-7.0, 3.0) = -1.0
/// - rem(7.0, -3.0) = 1.0
#[no_mangle]
pub extern "C" fn rt_math_rem(x: f64, y: f64) -> f64 {
    x % y
}

// ============================================================================
// Special Values
// ============================================================================

/// Returns IEEE 754 NaN (Not a Number)
///
/// # Examples
/// - rt_math_nan() returns NaN
/// - is_nan(rt_math_nan()) returns true
#[no_mangle]
pub extern "C" fn rt_math_nan() -> f64 {
    f64::NAN
}

/// Returns IEEE 754 positive infinity
///
/// # Examples
/// - rt_math_inf() returns +∞
/// - is_inf(rt_math_inf()) returns true
#[no_mangle]
pub extern "C" fn rt_math_inf() -> f64 {
    f64::INFINITY
}

/// Check if value is NaN
///
/// # Examples
/// - is_nan(NaN) returns true
/// - is_nan(1.0) returns false
#[no_mangle]
pub extern "C" fn rt_math_is_nan(x: f64) -> bool {
    x.is_nan()
}

/// Check if value is infinite (positive or negative)
///
/// # Examples
/// - is_inf(∞) returns true
/// - is_inf(-∞) returns true
/// - is_inf(1.0) returns false
#[no_mangle]
pub extern "C" fn rt_math_is_inf(x: f64) -> bool {
    x.is_infinite()
}

/// Check if value is finite (not NaN or infinite)
///
/// # Examples
/// - is_finite(1.0) returns true
/// - is_finite(NaN) returns false
/// - is_finite(∞) returns false
#[no_mangle]
pub extern "C" fn rt_math_is_finite(x: f64) -> bool {
    x.is_finite()
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPSILON: f64 = 1e-10;

    fn assert_close(a: f64, b: f64, epsilon: f64) {
        assert!(
            (a - b).abs() < epsilon,
            "Expected {} to be close to {}, diff: {}",
            a,
            b,
            (a - b).abs()
        );
    }

    // ========================================================================
    // Power & Logarithm Tests
    // ========================================================================

    #[test]
    fn test_pow() {
        assert_eq!(rt_math_pow(2.0, 3.0), 8.0);
        assert_eq!(rt_math_pow(10.0, 2.0), 100.0);
        assert_eq!(rt_math_pow(2.0, -1.0), 0.5);
        assert_eq!(rt_math_pow(5.0, 0.0), 1.0); // x^0 = 1
    }

    #[test]
    fn test_log() {
        assert_close(rt_math_log(std::f64::consts::E), 1.0, EPSILON);
        assert_eq!(rt_math_log(1.0), 0.0);
        assert_close(rt_math_log(std::f64::consts::E.powi(2)), 2.0, EPSILON);
    }

    #[test]
    fn test_log10() {
        assert_eq!(rt_math_log10(10.0), 1.0);
        assert_eq!(rt_math_log10(100.0), 2.0);
        assert_eq!(rt_math_log10(1.0), 0.0);
        assert_eq!(rt_math_log10(1000.0), 3.0);
    }

    #[test]
    fn test_log2() {
        assert_eq!(rt_math_log2(2.0), 1.0);
        assert_eq!(rt_math_log2(8.0), 3.0);
        assert_eq!(rt_math_log2(1.0), 0.0);
        assert_eq!(rt_math_log2(1024.0), 10.0);
    }

    #[test]
    fn test_exp() {
        assert_eq!(rt_math_exp(0.0), 1.0);
        assert_close(rt_math_exp(1.0), std::f64::consts::E, EPSILON);
        assert_close(rt_math_exp(2.0), std::f64::consts::E.powi(2), EPSILON);
    }

    // ========================================================================
    // Root Tests
    // ========================================================================

    #[test]
    fn test_sqrt() {
        assert_eq!(rt_math_sqrt(4.0), 2.0);
        assert_eq!(rt_math_sqrt(9.0), 3.0);
        assert_eq!(rt_math_sqrt(0.0), 0.0);
        assert_eq!(rt_math_sqrt(1.0), 1.0);
    }

    #[test]
    fn test_sqrt_nan() {
        assert!(rt_math_sqrt(-1.0).is_nan());
    }

    #[test]
    fn test_cbrt() {
        assert_close(rt_math_cbrt(8.0), 2.0, EPSILON);
        assert_close(rt_math_cbrt(27.0), 3.0, EPSILON);
        assert_close(rt_math_cbrt(-8.0), -2.0, EPSILON); // Cube root of negative works
    }

    // ========================================================================
    // Trigonometric Tests
    // ========================================================================

    #[test]
    fn test_sin() {
        assert_eq!(rt_math_sin(0.0), 0.0);
        assert_close(rt_math_sin(std::f64::consts::PI / 2.0), 1.0, EPSILON);
        assert_close(rt_math_sin(std::f64::consts::PI), 0.0, EPSILON);
        assert_close(rt_math_sin(3.0 * std::f64::consts::PI / 2.0), -1.0, EPSILON);
    }

    #[test]
    fn test_cos() {
        assert_eq!(rt_math_cos(0.0), 1.0);
        assert_close(rt_math_cos(std::f64::consts::PI / 2.0), 0.0, EPSILON);
        assert_close(rt_math_cos(std::f64::consts::PI), -1.0, EPSILON);
    }

    #[test]
    fn test_tan() {
        assert_eq!(rt_math_tan(0.0), 0.0);
        assert_close(rt_math_tan(std::f64::consts::PI / 4.0), 1.0, EPSILON);
        assert_close(rt_math_tan(-std::f64::consts::PI / 4.0), -1.0, EPSILON);
    }

    #[test]
    fn test_asin() {
        assert_eq!(rt_math_asin(0.0), 0.0);
        assert_close(rt_math_asin(1.0), std::f64::consts::PI / 2.0, EPSILON);
        assert_close(rt_math_asin(-1.0), -std::f64::consts::PI / 2.0, EPSILON);
    }

    #[test]
    fn test_asin_nan() {
        assert!(rt_math_asin(2.0).is_nan()); // |x| > 1
        assert!(rt_math_asin(-2.0).is_nan());
    }

    #[test]
    fn test_acos() {
        assert_close(rt_math_acos(1.0), 0.0, EPSILON);
        assert_close(rt_math_acos(0.0), std::f64::consts::PI / 2.0, EPSILON);
        assert_close(rt_math_acos(-1.0), std::f64::consts::PI, EPSILON);
    }

    #[test]
    fn test_acos_nan() {
        assert!(rt_math_acos(2.0).is_nan()); // |x| > 1
        assert!(rt_math_acos(-2.0).is_nan());
    }

    #[test]
    fn test_atan() {
        assert_eq!(rt_math_atan(0.0), 0.0);
        assert_close(rt_math_atan(1.0), std::f64::consts::PI / 4.0, EPSILON);
        assert_close(rt_math_atan(-1.0), -std::f64::consts::PI / 4.0, EPSILON);
    }

    #[test]
    fn test_atan2() {
        assert_eq!(rt_math_atan2(0.0, 1.0), 0.0); // Positive x-axis
        assert_close(rt_math_atan2(1.0, 0.0), std::f64::consts::PI / 2.0, EPSILON); // Positive y-axis
        assert_close(rt_math_atan2(0.0, -1.0), std::f64::consts::PI, EPSILON); // Negative x-axis
        assert_close(rt_math_atan2(-1.0, 0.0), -std::f64::consts::PI / 2.0, EPSILON); // Negative y-axis

        // Quadrants
        assert_close(rt_math_atan2(1.0, 1.0), std::f64::consts::PI / 4.0, EPSILON); // Q1
        assert_close(rt_math_atan2(1.0, -1.0), 3.0 * std::f64::consts::PI / 4.0, EPSILON);
        // Q2
    }

    // ========================================================================
    // Hyperbolic Tests
    // ========================================================================

    #[test]
    fn test_sinh() {
        assert_eq!(rt_math_sinh(0.0), 0.0);
        assert_close(
            rt_math_sinh(1.0),
            (std::f64::consts::E - 1.0 / std::f64::consts::E) / 2.0,
            EPSILON,
        );
    }

    #[test]
    fn test_cosh() {
        assert_eq!(rt_math_cosh(0.0), 1.0);
        assert_close(
            rt_math_cosh(1.0),
            (std::f64::consts::E + 1.0 / std::f64::consts::E) / 2.0,
            EPSILON,
        );
    }

    #[test]
    fn test_tanh() {
        assert_eq!(rt_math_tanh(0.0), 0.0);
        assert_close(rt_math_tanh(f64::INFINITY), 1.0, EPSILON);
        assert_close(rt_math_tanh(f64::NEG_INFINITY), -1.0, EPSILON);
    }

    // ========================================================================
    // Rounding Tests
    // ========================================================================

    #[test]
    fn test_floor() {
        assert_eq!(rt_math_floor(3.7), 3.0);
        assert_eq!(rt_math_floor(-3.7), -4.0);
        assert_eq!(rt_math_floor(5.0), 5.0);
        assert_eq!(rt_math_floor(0.1), 0.0);
    }

    #[test]
    fn test_ceil() {
        assert_eq!(rt_math_ceil(3.2), 4.0);
        assert_eq!(rt_math_ceil(-3.2), -3.0);
        assert_eq!(rt_math_ceil(5.0), 5.0);
        assert_eq!(rt_math_ceil(0.1), 1.0);
    }

    #[test]
    fn test_round() {
        assert_eq!(rt_math_round(3.5), 4.0);
        assert_eq!(rt_math_round(3.4), 3.0);
        assert_eq!(rt_math_round(-3.5), -4.0);
        assert_eq!(rt_math_round(-3.4), -3.0);
        assert_eq!(rt_math_round(5.0), 5.0);
        assert_eq!(rt_math_round(2.5), 3.0); // Round half away from zero
    }

    #[test]
    fn test_trunc() {
        assert_eq!(rt_math_trunc(3.7), 3.0);
        assert_eq!(rt_math_trunc(-3.7), -3.0);
        assert_eq!(rt_math_trunc(5.0), 5.0);
        assert_eq!(rt_math_trunc(0.9), 0.0);
        assert_eq!(rt_math_trunc(-0.9), 0.0);
    }

    // ========================================================================
    // Basic Function Tests
    // ========================================================================

    #[test]
    fn test_abs() {
        assert_eq!(rt_math_abs(5.0), 5.0);
        assert_eq!(rt_math_abs(-5.0), 5.0);
        assert_eq!(rt_math_abs(0.0), 0.0);
        assert_eq!(rt_math_abs(-0.0), 0.0);
        assert_eq!(rt_math_abs(f64::INFINITY), f64::INFINITY);
        assert_eq!(rt_math_abs(f64::NEG_INFINITY), f64::INFINITY);
    }

    #[test]
    fn test_hypot() {
        assert_eq!(rt_math_hypot(3.0, 4.0), 5.0);
        assert_eq!(rt_math_hypot(5.0, 12.0), 13.0);
        assert_close(rt_math_hypot(1.0, 1.0), std::f64::consts::SQRT_2, EPSILON);
        assert_eq!(rt_math_hypot(0.0, 5.0), 5.0);
        assert_eq!(rt_math_hypot(5.0, 0.0), 5.0);
    }

    #[test]
    fn test_gcd() {
        assert_eq!(rt_math_gcd(12, 8), 4);
        assert_eq!(rt_math_gcd(54, 24), 6);
        assert_eq!(rt_math_gcd(17, 13), 1); // Coprime
        assert_eq!(rt_math_gcd(100, 10), 10);
        assert_eq!(rt_math_gcd(0, 5), 5);
        assert_eq!(rt_math_gcd(5, 0), 5);
        assert_eq!(rt_math_gcd(0, 0), 0);
        // Negative numbers
        assert_eq!(rt_math_gcd(-12, 8), 4);
        assert_eq!(rt_math_gcd(12, -8), 4);
        assert_eq!(rt_math_gcd(-12, -8), 4);
    }

    #[test]
    fn test_lcm() {
        assert_eq!(rt_math_lcm(4, 6), 12);
        assert_eq!(rt_math_lcm(3, 5), 15);
        assert_eq!(rt_math_lcm(12, 8), 24);
        assert_eq!(rt_math_lcm(7, 1), 7);
        assert_eq!(rt_math_lcm(0, 5), 0);
        assert_eq!(rt_math_lcm(5, 0), 0);
        // Negative numbers
        assert_eq!(rt_math_lcm(-4, 6), 12);
        assert_eq!(rt_math_lcm(4, -6), 12);
    }

    #[test]
    fn test_min() {
        assert_eq!(rt_math_min(3.0, 5.0), 3.0);
        assert_eq!(rt_math_min(5.0, 3.0), 3.0);
        assert_eq!(rt_math_min(-2.0, 1.0), -2.0);
        assert_eq!(rt_math_min(4.0, 4.0), 4.0);
        assert_eq!(rt_math_min(f64::NEG_INFINITY, 0.0), f64::NEG_INFINITY);
    }

    #[test]
    fn test_max() {
        assert_eq!(rt_math_max(3.0, 5.0), 5.0);
        assert_eq!(rt_math_max(5.0, 3.0), 5.0);
        assert_eq!(rt_math_max(-2.0, 1.0), 1.0);
        assert_eq!(rt_math_max(4.0, 4.0), 4.0);
        assert_eq!(rt_math_max(f64::INFINITY, 0.0), f64::INFINITY);
    }

    #[test]
    fn test_clamp() {
        assert_eq!(rt_math_clamp(5.0, 0.0, 10.0), 5.0);
        assert_eq!(rt_math_clamp(-5.0, 0.0, 10.0), 0.0);
        assert_eq!(rt_math_clamp(15.0, 0.0, 10.0), 10.0);
        assert_eq!(rt_math_clamp(0.0, 0.0, 10.0), 0.0);
        assert_eq!(rt_math_clamp(10.0, 0.0, 10.0), 10.0);
    }

    #[test]
    fn test_sign() {
        assert_eq!(rt_math_sign(5.0), 1.0);
        assert_eq!(rt_math_sign(-5.0), -1.0);
        assert_eq!(rt_math_sign(0.0), 0.0);
        assert_eq!(rt_math_sign(f64::INFINITY), 1.0);
        assert_eq!(rt_math_sign(f64::NEG_INFINITY), -1.0);
        assert!(rt_math_sign(f64::NAN).is_nan());
    }

    #[test]
    fn test_fract() {
        assert_close(rt_math_fract(3.7), 0.7, EPSILON);
        assert_close(rt_math_fract(-3.7), -0.7, EPSILON);
        assert_eq!(rt_math_fract(5.0), 0.0);
        assert_close(rt_math_fract(0.25), 0.25, EPSILON);
    }

    #[test]
    fn test_rem() {
        assert_eq!(rt_math_rem(7.0, 3.0), 1.0);
        assert_eq!(rt_math_rem(-7.0, 3.0), -1.0);
        assert_eq!(rt_math_rem(7.0, -3.0), 1.0);
        assert_eq!(rt_math_rem(-7.0, -3.0), -1.0);
        assert_close(rt_math_rem(5.5, 2.0), 1.5, EPSILON);
    }

    // ========================================================================
    // Special Value Tests
    // ========================================================================

    #[test]
    fn test_nan_propagation() {
        // NaN inputs should produce NaN outputs
        assert!(rt_math_sin(f64::NAN).is_nan());
        assert!(rt_math_cos(f64::NAN).is_nan());
        assert!(rt_math_sqrt(f64::NAN).is_nan());
        assert!(rt_math_log(f64::NAN).is_nan());
    }

    #[test]
    fn test_infinity_handling() {
        assert_eq!(rt_math_floor(f64::INFINITY), f64::INFINITY);
        assert_eq!(rt_math_ceil(f64::INFINITY), f64::INFINITY);
        assert_eq!(rt_math_floor(f64::NEG_INFINITY), f64::NEG_INFINITY);
        assert_eq!(rt_math_ceil(f64::NEG_INFINITY), f64::NEG_INFINITY);
    }
}
