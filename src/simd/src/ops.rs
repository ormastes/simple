//! SIMD Operations
//!
//! This module provides higher-level operations built on top of the core vector types.

use crate::types::*;

/// Process an array in SIMD chunks with F32x4.
///
/// Applies the given function to each 4-element chunk of the array,
/// with scalar fallback for the remainder.
pub fn process_f32_array<F>(data: &mut [f32], mut simd_op: F)
where
    F: FnMut(F32x4) -> F32x4,
{
    let chunks = data.len() / 4;

    // Process SIMD chunks
    for i in 0..chunks {
        let v = F32x4::load(data, i * 4);
        let result = simd_op(v);
        result.store(data, i * 4);
    }
}

/// Process an array in SIMD chunks with F32x8.
pub fn process_f32_array_x8<F>(data: &mut [f32], mut simd_op: F)
where
    F: FnMut(F32x8) -> F32x8,
{
    let chunks = data.len() / 8;

    for i in 0..chunks {
        let v = F32x8::load(data, i * 8);
        let result = simd_op(v);
        result.store(data, i * 8);
    }
}

/// Compute dot product of two f32 arrays using SIMD.
pub fn dot_product_f32(a: &[f32], b: &[f32]) -> f32 {
    assert_eq!(a.len(), b.len());

    let chunks = a.len() / 4;
    let mut sum = F32x4::zero();

    for i in 0..chunks {
        let va = F32x4::load(a, i * 4);
        let vb = F32x4::load(b, i * 4);
        sum = sum + va * vb;
    }

    let mut result = sum.sum();

    // Handle remainder
    for i in (chunks * 4)..a.len() {
        result += a[i] * b[i];
    }

    result
}

/// Compute sum of f32 array using SIMD.
pub fn sum_f32(data: &[f32]) -> f32 {
    let chunks = data.len() / 4;
    let mut sum = F32x4::zero();

    for i in 0..chunks {
        let v = F32x4::load(data, i * 4);
        sum = sum + v;
    }

    let mut result = sum.sum();

    // Handle remainder
    for i in (chunks * 4)..data.len() {
        result += data[i];
    }

    result
}

/// Helper for reduction operations on f32 arrays using SIMD.
fn reduce_f32_helper(
    data: &[f32],
    scalar_reduce: fn(f32, f32) -> f32,
    simd_combine: fn(F32x4, F32x4) -> F32x4,
    simd_reduce: fn(F32x4) -> f32,
) -> Option<f32> {
    if data.is_empty() {
        return None;
    }

    let chunks = data.len() / 4;

    if chunks == 0 {
        return data.iter().cloned().reduce(scalar_reduce);
    }

    let mut acc = F32x4::load(data, 0);

    for i in 1..chunks {
        let v = F32x4::load(data, i * 4);
        acc = simd_combine(acc, v);
    }

    let mut result = simd_reduce(acc);

    // Handle remainder
    for i in (chunks * 4)..data.len() {
        result = scalar_reduce(result, data[i]);
    }

    Some(result)
}

/// Find maximum value in f32 array using SIMD.
pub fn max_f32(data: &[f32]) -> Option<f32> {
    reduce_f32_helper(
        data,
        f32::max,
        |a, b| a.max(b),
        |v| v.max_element(),
    )
}

/// Find minimum value in f32 array using SIMD.
pub fn min_f32(data: &[f32]) -> Option<f32> {
    reduce_f32_helper(
        data,
        f32::min,
        |a, b| a.min(b),
        |v| v.min_element(),
    )
}

/// Scale all elements in an f32 array by a constant.
pub fn scale_f32(data: &mut [f32], factor: f32) {
    let factor_vec = F32x4::splat(factor);
    process_f32_array(data, |v| v * factor_vec);

    // Handle remainder
    let remainder_start = (data.len() / 4) * 4;
    for i in remainder_start..data.len() {
        data[i] *= factor;
    }
}

/// Add a constant to all elements in an f32 array.
pub fn add_scalar_f32(data: &mut [f32], value: f32) {
    let value_vec = F32x4::splat(value);
    process_f32_array(data, |v| v + value_vec);

    let remainder_start = (data.len() / 4) * 4;
    for i in remainder_start..data.len() {
        data[i] += value;
    }
}

/// Helper for element-wise binary operations on two arrays.
fn binop_arrays_f32(
    a: &[f32],
    b: &[f32],
    out: &mut [f32],
    simd_op: fn(F32x4, F32x4) -> F32x4,
    scalar_op: fn(f32, f32) -> f32,
) {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), out.len());

    let chunks = a.len() / 4;

    for i in 0..chunks {
        let va = F32x4::load(a, i * 4);
        let vb = F32x4::load(b, i * 4);
        let result = simd_op(va, vb);
        result.store(out, i * 4);
    }

    for i in (chunks * 4)..a.len() {
        out[i] = scalar_op(a[i], b[i]);
    }
}

/// Element-wise addition of two arrays.
pub fn add_arrays_f32(a: &[f32], b: &[f32], out: &mut [f32]) {
    binop_arrays_f32(a, b, out, std::ops::Add::add, std::ops::Add::add)
}

/// Element-wise multiplication of two arrays.
pub fn mul_arrays_f32(a: &[f32], b: &[f32], out: &mut [f32]) {
    binop_arrays_f32(a, b, out, std::ops::Mul::mul, std::ops::Mul::mul)
}

/// Apply fused multiply-add to arrays: out = a * b + c.
pub fn fma_arrays_f32(a: &[f32], b: &[f32], c: &[f32], out: &mut [f32]) {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), c.len());
    assert_eq!(a.len(), out.len());

    let chunks = a.len() / 4;

    for i in 0..chunks {
        let va = F32x4::load(a, i * 4);
        let vb = F32x4::load(b, i * 4);
        let vc = F32x4::load(c, i * 4);
        let result = va.fma(vb, vc);
        result.store(out, i * 4);
    }

    for i in (chunks * 4)..a.len() {
        out[i] = a[i].mul_add(b[i], c[i]);
    }
}

/// Count elements greater than a threshold.
pub fn count_greater_than_f32(data: &[f32], threshold: f32) -> usize {
    let chunks = data.len() / 4;
    let threshold_vec = F32x4::splat(threshold);
    let mut count = 0usize;

    for i in 0..chunks {
        let v = F32x4::load(data, i * 4);
        let mask = v.gt(threshold_vec);
        // Count true lanes
        for j in 0..4 {
            if mask.test(j) {
                count += 1;
            }
        }
    }

    // Handle remainder
    for i in (chunks * 4)..data.len() {
        if data[i] > threshold {
            count += 1;
        }
    }

    count
}

/// Clamp all values in an array to [min, max].
pub fn clamp_f32(data: &mut [f32], min_val: f32, max_val: f32) {
    let min_vec = F32x4::splat(min_val);
    let max_vec = F32x4::splat(max_val);

    process_f32_array(data, |v| v.max(min_vec).min(max_vec));

    let remainder_start = (data.len() / 4) * 4;
    for i in remainder_start..data.len() {
        data[i] = data[i].max(min_val).min(max_val);
    }
}

/// Normalize array (subtract mean, divide by std dev).
pub fn normalize_f32(data: &mut [f32]) {
    if data.is_empty() {
        return;
    }

    // Compute mean
    let sum = sum_f32(data);
    let mean = sum / data.len() as f32;

    // Subtract mean
    add_scalar_f32(data, -mean);

    // Compute variance
    let mut variance_sum = 0.0f32;
    let chunks = data.len() / 4;

    for i in 0..chunks {
        let v = F32x4::load(data, i * 4);
        let sq = v * v;
        variance_sum += sq.sum();
    }

    for i in (chunks * 4)..data.len() {
        variance_sum += data[i] * data[i];
    }

    let std_dev = (variance_sum / data.len() as f32).sqrt();

    if std_dev > 0.0 {
        scale_f32(data, 1.0 / std_dev);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dot_product() {
        let a = [1.0f32, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let b = [1.0f32, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0];

        let result = dot_product_f32(&a, &b);
        assert_eq!(result, 36.0);
    }

    #[test]
    fn test_sum() {
        let data = [1.0f32, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0];
        let result = sum_f32(&data);
        assert_eq!(result, 45.0);
    }

    #[test]
    fn test_max_min() {
        let data = [3.0f32, 1.0, 4.0, 1.0, 5.0, 9.0, 2.0, 6.0];
        assert_eq!(max_f32(&data), Some(9.0));
        assert_eq!(min_f32(&data), Some(1.0));
    }

    #[test]
    fn test_scale() {
        let mut data = [1.0f32, 2.0, 3.0, 4.0, 5.0];
        scale_f32(&mut data, 2.0);
        assert_eq!(data, [2.0, 4.0, 6.0, 8.0, 10.0]);
    }

    #[test]
    fn test_add_arrays() {
        let a = [1.0f32, 2.0, 3.0, 4.0, 5.0];
        let b = [5.0f32, 4.0, 3.0, 2.0, 1.0];
        let mut out = [0.0f32; 5];

        add_arrays_f32(&a, &b, &mut out);
        assert_eq!(out, [6.0, 6.0, 6.0, 6.0, 6.0]);
    }

    #[test]
    fn test_count_greater_than() {
        let data = [1.0f32, 5.0, 2.0, 6.0, 3.0, 7.0, 4.0, 8.0];
        assert_eq!(count_greater_than_f32(&data, 4.0), 4);
    }

    #[test]
    fn test_clamp() {
        let mut data = [0.0f32, 5.0, 10.0, 15.0, 20.0];
        clamp_f32(&mut data, 5.0, 15.0);
        assert_eq!(data, [5.0, 5.0, 10.0, 15.0, 15.0]);
    }

    #[test]
    fn test_fma_arrays() {
        let a = [1.0f32, 2.0, 3.0, 4.0];
        let b = [2.0f32, 2.0, 2.0, 2.0];
        let c = [1.0f32, 1.0, 1.0, 1.0];
        let mut out = [0.0f32; 4];

        fma_arrays_f32(&a, &b, &c, &mut out);
        assert_eq!(out, [3.0, 5.0, 7.0, 9.0]);
    }
}
