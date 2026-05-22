//! Math SFFI — implementations live in src/runtime/runtime_math.c.
//! Safe Rust wrappers around the C extern functions.

mod c_sffi {
    extern "C" {
        pub(super) fn rt_math_pow(base: f64, exp: f64) -> f64;
        pub(super) fn rt_math_log(x: f64) -> f64;
        pub(super) fn rt_math_log10(x: f64) -> f64;
        pub(super) fn rt_math_log2(x: f64) -> f64;
        pub(super) fn rt_math_exp(x: f64) -> f64;
        pub(super) fn rt_math_sqrt(x: f64) -> f64;
        pub(super) fn rt_math_cbrt(x: f64) -> f64;
        pub(super) fn rt_math_sin(x: f64) -> f64;
        pub(super) fn rt_math_cos(x: f64) -> f64;
        pub(super) fn rt_math_tan(x: f64) -> f64;
        pub(super) fn rt_math_asin(x: f64) -> f64;
        pub(super) fn rt_math_acos(x: f64) -> f64;
        pub(super) fn rt_math_atan(x: f64) -> f64;
        pub(super) fn rt_math_atan2(y: f64, x: f64) -> f64;
        pub(super) fn rt_math_sinh(x: f64) -> f64;
        pub(super) fn rt_math_cosh(x: f64) -> f64;
        pub(super) fn rt_math_tanh(x: f64) -> f64;
        pub(super) fn rt_math_floor(x: f64) -> f64;
        pub(super) fn rt_math_ceil(x: f64) -> f64;
        pub(super) fn rt_math_round(x: f64) -> f64;
        pub(super) fn rt_math_trunc(x: f64) -> f64;
        pub(super) fn rt_math_abs(x: f64) -> f64;
        pub(super) fn rt_math_hypot(x: f64, y: f64) -> f64;
        pub(super) fn rt_math_gcd(a: i64, b: i64) -> i64;
        pub(super) fn rt_math_min(a: f64, b: f64) -> f64;
        pub(super) fn rt_math_max(a: f64, b: f64) -> f64;
        pub(super) fn rt_math_clamp(x: f64, min: f64, max: f64) -> f64;
        pub(super) fn rt_math_fma(x: f64, y: f64, z: f64) -> f64;
    }
}

#[inline(always)]
pub fn rt_math_pow(base: f64, exp: f64) -> f64 {
    unsafe { c_sffi::rt_math_pow(base, exp) }
}
#[inline(always)]
pub fn rt_math_log(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_log(x) }
}
#[inline(always)]
pub fn rt_math_log10(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_log10(x) }
}
#[inline(always)]
pub fn rt_math_log2(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_log2(x) }
}
#[inline(always)]
pub fn rt_math_exp(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_exp(x) }
}
#[inline(always)]
pub fn rt_math_sqrt(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_sqrt(x) }
}
#[inline(always)]
pub fn rt_math_cbrt(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_cbrt(x) }
}
#[inline(always)]
pub fn rt_math_sin(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_sin(x) }
}
#[inline(always)]
pub fn rt_math_cos(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_cos(x) }
}
#[inline(always)]
pub fn rt_math_tan(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_tan(x) }
}
#[inline(always)]
pub fn rt_math_asin(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_asin(x) }
}
#[inline(always)]
pub fn rt_math_acos(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_acos(x) }
}
#[inline(always)]
pub fn rt_math_atan(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_atan(x) }
}
#[inline(always)]
pub fn rt_math_atan2(y: f64, x: f64) -> f64 {
    unsafe { c_sffi::rt_math_atan2(y, x) }
}
#[inline(always)]
pub fn rt_math_sinh(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_sinh(x) }
}
#[inline(always)]
pub fn rt_math_cosh(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_cosh(x) }
}
#[inline(always)]
pub fn rt_math_tanh(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_tanh(x) }
}
#[inline(always)]
pub fn rt_math_floor(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_floor(x) }
}
#[inline(always)]
pub fn rt_math_ceil(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_ceil(x) }
}
#[inline(always)]
pub fn rt_math_round(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_round(x) }
}
#[inline(always)]
pub fn rt_math_trunc(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_trunc(x) }
}
#[inline(always)]
pub fn rt_math_abs(x: f64) -> f64 {
    unsafe { c_sffi::rt_math_abs(x) }
}
#[inline(always)]
pub fn rt_math_hypot(x: f64, y: f64) -> f64 {
    unsafe { c_sffi::rt_math_hypot(x, y) }
}
#[inline(always)]
pub fn rt_math_gcd(a: i64, b: i64) -> i64 {
    unsafe { c_sffi::rt_math_gcd(a, b) }
}
#[inline(always)]
pub fn rt_math_min(a: f64, b: f64) -> f64 {
    unsafe { c_sffi::rt_math_min(a, b) }
}
#[inline(always)]
pub fn rt_math_max(a: f64, b: f64) -> f64 {
    unsafe { c_sffi::rt_math_max(a, b) }
}
#[inline(always)]
pub fn rt_math_clamp(x: f64, min: f64, max: f64) -> f64 {
    unsafe { c_sffi::rt_math_clamp(x, min, max) }
}
#[inline(always)]
pub fn rt_math_fma(x: f64, y: f64, z: f64) -> f64 {
    unsafe { c_sffi::rt_math_fma(x, y, z) }
}

// Constants and utility functions that were in the old Rust math.rs
#[inline(always)]
pub fn rt_math_nan() -> f64 {
    f64::NAN
}
#[inline(always)]
pub fn rt_math_inf() -> f64 {
    f64::INFINITY
}
#[inline(always)]
pub fn rt_math_is_nan(x: f64) -> bool {
    x.is_nan()
}
#[inline(always)]
pub fn rt_math_is_inf(x: f64) -> bool {
    x.is_infinite()
}
#[inline(always)]
pub fn rt_math_is_finite(x: f64) -> bool {
    x.is_finite()
}
