//! Math SFFI implemented directly in Rust.

#[inline(always)]
pub fn rt_math_pow(base: f64, exp: f64) -> f64 {
    base.powf(exp)
}
#[inline(always)]
pub fn rt_math_log(x: f64) -> f64 {
    x.ln()
}
#[inline(always)]
pub fn rt_math_log10(x: f64) -> f64 {
    x.log10()
}
#[inline(always)]
pub fn rt_math_log2(x: f64) -> f64 {
    x.log2()
}
#[inline(always)]
pub fn rt_math_exp(x: f64) -> f64 {
    x.exp()
}
#[inline(always)]
pub fn rt_math_sqrt(x: f64) -> f64 {
    x.sqrt()
}
#[inline(always)]
pub fn rt_math_cbrt(x: f64) -> f64 {
    x.cbrt()
}
#[inline(always)]
pub fn rt_math_sin(x: f64) -> f64 {
    x.sin()
}
#[inline(always)]
pub fn rt_math_cos(x: f64) -> f64 {
    x.cos()
}
#[inline(always)]
pub fn rt_math_tan(x: f64) -> f64 {
    x.tan()
}
#[inline(always)]
pub fn rt_math_asin(x: f64) -> f64 {
    x.asin()
}
#[inline(always)]
pub fn rt_math_acos(x: f64) -> f64 {
    x.acos()
}
#[inline(always)]
pub fn rt_math_atan(x: f64) -> f64 {
    x.atan()
}
#[inline(always)]
pub fn rt_math_atan2(y: f64, x: f64) -> f64 {
    y.atan2(x)
}
#[inline(always)]
pub fn rt_math_sinh(x: f64) -> f64 {
    x.sinh()
}
#[inline(always)]
pub fn rt_math_cosh(x: f64) -> f64 {
    x.cosh()
}
#[inline(always)]
pub fn rt_math_tanh(x: f64) -> f64 {
    x.tanh()
}
#[inline(always)]
pub fn rt_math_floor(x: f64) -> f64 {
    x.floor()
}
#[inline(always)]
pub fn rt_math_ceil(x: f64) -> f64 {
    x.ceil()
}
#[inline(always)]
pub fn rt_math_round(x: f64) -> f64 {
    x.round()
}
#[inline(always)]
pub fn rt_math_trunc(x: f64) -> f64 {
    x.trunc()
}
#[inline(always)]
pub fn rt_math_abs(x: f64) -> f64 {
    x.abs()
}
#[inline(always)]
pub fn rt_math_hypot(x: f64, y: f64) -> f64 {
    x.hypot(y)
}
#[inline(always)]
pub fn rt_math_gcd(a: i64, b: i64) -> i64 {
    let mut a = a.saturating_abs();
    let mut b = b.saturating_abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}
#[inline(always)]
pub fn rt_math_min(a: f64, b: f64) -> f64 {
    a.min(b)
}
#[inline(always)]
pub fn rt_math_max(a: f64, b: f64) -> f64 {
    a.max(b)
}
#[inline(always)]
pub fn rt_math_clamp(x: f64, min: f64, max: f64) -> f64 {
    if x < min {
        min
    } else if x > max {
        max
    } else {
        x
    }
}
#[inline(always)]
pub fn rt_math_fma(x: f64, y: f64, z: f64) -> f64 {
    x.mul_add(y, z)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd_matches_c_semantics_for_positive_and_negative_inputs() {
        assert_eq!(rt_math_gcd(54, 24), 6);
        assert_eq!(rt_math_gcd(-54, 24), 6);
        assert_eq!(rt_math_gcd(0, 9), 9);
    }

    #[test]
    fn clamp_preserves_bounds() {
        assert_eq!(rt_math_clamp(2.0, 0.0, 1.0), 1.0);
        assert_eq!(rt_math_clamp(-1.0, 0.0, 1.0), 0.0);
        assert_eq!(rt_math_clamp(0.5, 0.0, 1.0), 0.5);
    }
}
