use std::sync::OnceLock;

use super::collections::{rt_array_get, rt_array_len, rt_array_new, rt_array_push};
use super::core::RuntimeValue;
use simple_simd::{active_simd_tier, SimdTier};

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

const PACK_THRESHOLD_F32: usize = 32;
const PACK_THRESHOLD_F64: usize = 24;

type F32MapKernel = fn(&[f32], &[f32], &mut [f32]);
type F32FmaKernel = fn(&[f32], &[f32], &[f32], &mut [f32]);
type F32ReduceKernel = fn(&[f32]) -> f32;
type F32DotKernel = fn(&[f32], &[f32]) -> f32;
type F64MapKernel = fn(&[f64], &[f64], &mut [f64]);
type F64FmaKernel = fn(&[f64], &[f64], &[f64], &mut [f64]);
type F64ReduceKernel = fn(&[f64]) -> f64;
type F64DotKernel = fn(&[f64], &[f64]) -> f64;

struct NumericKernelProvider {
    tier: SimdTier,
    add_f32: F32MapKernel,
    mul_f32: F32MapKernel,
    fma_f32: F32FmaKernel,
    dot_f32: F32DotKernel,
    sum_f32: F32ReduceKernel,
    min_f32: F32ReduceKernel,
    max_f32: F32ReduceKernel,
    add_f64: F64MapKernel,
    mul_f64: F64MapKernel,
    fma_f64: F64FmaKernel,
    sum_f64: F64ReduceKernel,
    dot_f64: F64DotKernel,
}

fn provider_for_tier(tier: SimdTier) -> NumericKernelProvider {
    match tier {
        SimdTier::X86_64Sse2 => NumericKernelProvider {
            tier: SimdTier::X86_64Sse2,
            add_f32: scalar_add_f32,
            mul_f32: scalar_mul_f32,
            fma_f32: scalar_fma_f32,
            dot_f32: scalar_dot_f32,
            sum_f32: scalar_sum_f32,
            min_f32: scalar_min_f32,
            max_f32: scalar_max_f32,
            add_f64: scalar_add_f64,
            mul_f64: scalar_mul_f64,
            fma_f64: scalar_fma_f64,
            sum_f64: scalar_sum_f64,
            dot_f64: scalar_dot_f64,
        },
        SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => NumericKernelProvider {
            tier: SimdTier::X86_64Avx2,
            add_f32: avx2_add_f32,
            mul_f32: avx2_mul_f32,
            fma_f32: avx2_fma_f32,
            dot_f32: avx2_dot_f32,
            sum_f32: avx2_sum_f32,
            min_f32: avx2_min_f32,
            max_f32: avx2_max_f32,
            add_f64: avx2_add_f64,
            mul_f64: avx2_mul_f64,
            fma_f64: avx2_fma_f64,
            sum_f64: avx2_sum_f64,
            dot_f64: avx2_dot_f64,
        },
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => NumericKernelProvider {
            tier: SimdTier::Aarch64Neon,
            add_f32: neon_add_f32,
            mul_f32: neon_mul_f32,
            fma_f32: neon_fma_f32,
            dot_f32: neon_dot_f32,
            sum_f32: neon_sum_f32,
            min_f32: neon_min_f32,
            max_f32: neon_max_f32,
            add_f64: neon_add_f64,
            mul_f64: neon_mul_f64,
            fma_f64: neon_fma_f64,
            sum_f64: neon_sum_f64,
            dot_f64: neon_dot_f64,
        },
        _ => NumericKernelProvider {
            tier: SimdTier::Scalar,
            add_f32: scalar_add_f32,
            mul_f32: scalar_mul_f32,
            fma_f32: scalar_fma_f32,
            dot_f32: scalar_dot_f32,
            sum_f32: scalar_sum_f32,
            min_f32: scalar_min_f32,
            max_f32: scalar_max_f32,
            add_f64: scalar_add_f64,
            mul_f64: scalar_mul_f64,
            fma_f64: scalar_fma_f64,
            sum_f64: scalar_sum_f64,
            dot_f64: scalar_dot_f64,
        },
    }
}

fn numeric_kernel_provider() -> &'static NumericKernelProvider {
    static PROVIDER: OnceLock<NumericKernelProvider> = OnceLock::new();
    PROVIDER.get_or_init(|| provider_for_tier(active_simd_tier()))
}

pub(crate) fn active_numeric_kernel_tier() -> SimdTier {
    numeric_kernel_provider().tier
}

pub(crate) fn should_use_packed_f32(len: usize) -> bool {
    len >= PACK_THRESHOLD_F32
}

pub(crate) fn should_use_packed_f64(len: usize) -> bool {
    len >= PACK_THRESHOLD_F64
}

fn runtime_numeric_to_f64(value: RuntimeValue) -> Option<f64> {
    if value.is_float() {
        Some(value.as_float())
    } else if value.is_int() {
        Some(value.as_int() as f64)
    } else {
        None
    }
}

fn runtime_numeric_to_f32(value: RuntimeValue) -> Option<f32> {
    runtime_numeric_to_f64(value).map(|value| value as f32)
}

fn pack_f32_array(value: RuntimeValue) -> Option<Vec<f32>> {
    let len = usize::try_from(rt_array_len(value)).ok()?;
    let mut out = Vec::with_capacity(len);
    for index in 0..len {
        let item = rt_array_get(value, index as i64);
        if !item.is_float() {
            return None;
        }
        out.push(item.as_float() as f32);
    }
    Some(out)
}

fn pack_f64_array(value: RuntimeValue) -> Option<Vec<f64>> {
    let len = usize::try_from(rt_array_len(value)).ok()?;
    let mut out = Vec::with_capacity(len);
    for index in 0..len {
        let item = rt_array_get(value, index as i64);
        if !item.is_float() {
            return None;
        }
        out.push(item.as_float());
    }
    Some(out)
}

fn runtime_array_from_f32(values: &[f32]) -> RuntimeValue {
    let array = rt_array_new(values.len() as u64);
    for value in values {
        rt_array_push(array, RuntimeValue::from_float(*value as f64));
    }
    array
}

fn runtime_array_from_f64(values: &[f64]) -> RuntimeValue {
    let array = rt_array_new(values.len() as u64);
    for value in values {
        rt_array_push(array, RuntimeValue::from_float(*value));
    }
    array
}

fn runtime_array_len_usize(value: RuntimeValue) -> Option<usize> {
    usize::try_from(rt_array_len(value)).ok()
}

fn scalar_array_binary_f32(lhs: RuntimeValue, rhs: RuntimeValue, op: impl Fn(f32, f32) -> f32) -> RuntimeValue {
    let Some(lhs_len) = runtime_array_len_usize(lhs) else {
        return RuntimeValue::NIL;
    };
    if runtime_array_len_usize(rhs) != Some(lhs_len) {
        return RuntimeValue::NIL;
    }
    let out = rt_array_new(lhs_len as u64);
    for index in 0..lhs_len {
        let Some(a) = runtime_numeric_to_f32(rt_array_get(lhs, index as i64)) else {
            return RuntimeValue::NIL;
        };
        let Some(b) = runtime_numeric_to_f32(rt_array_get(rhs, index as i64)) else {
            return RuntimeValue::NIL;
        };
        rt_array_push(out, RuntimeValue::from_float(op(a, b) as f64));
    }
    out
}

fn scalar_array_binary_f64(lhs: RuntimeValue, rhs: RuntimeValue, op: impl Fn(f64, f64) -> f64) -> RuntimeValue {
    let Some(lhs_len) = runtime_array_len_usize(lhs) else {
        return RuntimeValue::NIL;
    };
    if runtime_array_len_usize(rhs) != Some(lhs_len) {
        return RuntimeValue::NIL;
    }
    let out = rt_array_new(lhs_len as u64);
    for index in 0..lhs_len {
        let Some(a) = runtime_numeric_to_f64(rt_array_get(lhs, index as i64)) else {
            return RuntimeValue::NIL;
        };
        let Some(b) = runtime_numeric_to_f64(rt_array_get(rhs, index as i64)) else {
            return RuntimeValue::NIL;
        };
        rt_array_push(out, RuntimeValue::from_float(op(a, b)));
    }
    out
}

fn scalar_array_fma_f32(a: RuntimeValue, b: RuntimeValue, c: RuntimeValue) -> RuntimeValue {
    let Some(len) = runtime_array_len_usize(a) else {
        return RuntimeValue::NIL;
    };
    if runtime_array_len_usize(b) != Some(len) || runtime_array_len_usize(c) != Some(len) {
        return RuntimeValue::NIL;
    }
    let out = rt_array_new(len as u64);
    for index in 0..len {
        let Some(lhs) = runtime_numeric_to_f32(rt_array_get(a, index as i64)) else {
            return RuntimeValue::NIL;
        };
        let Some(rhs) = runtime_numeric_to_f32(rt_array_get(b, index as i64)) else {
            return RuntimeValue::NIL;
        };
        let Some(add) = runtime_numeric_to_f32(rt_array_get(c, index as i64)) else {
            return RuntimeValue::NIL;
        };
        rt_array_push(out, RuntimeValue::from_float(lhs.mul_add(rhs, add) as f64));
    }
    out
}

fn scalar_array_fma_f64(a: RuntimeValue, b: RuntimeValue, c: RuntimeValue) -> RuntimeValue {
    let Some(len) = runtime_array_len_usize(a) else {
        return RuntimeValue::NIL;
    };
    if runtime_array_len_usize(b) != Some(len) || runtime_array_len_usize(c) != Some(len) {
        return RuntimeValue::NIL;
    }
    let out = rt_array_new(len as u64);
    for index in 0..len {
        let Some(lhs) = runtime_numeric_to_f64(rt_array_get(a, index as i64)) else {
            return RuntimeValue::NIL;
        };
        let Some(rhs) = runtime_numeric_to_f64(rt_array_get(b, index as i64)) else {
            return RuntimeValue::NIL;
        };
        let Some(add) = runtime_numeric_to_f64(rt_array_get(c, index as i64)) else {
            return RuntimeValue::NIL;
        };
        rt_array_push(out, RuntimeValue::from_float(lhs.mul_add(rhs, add)));
    }
    out
}

fn scalar_dot_runtime_f32(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_len) = runtime_array_len_usize(lhs) else {
        return RuntimeValue::NIL;
    };
    if runtime_array_len_usize(rhs) != Some(lhs_len) {
        return RuntimeValue::NIL;
    }
    let mut acc = 0.0f32;
    for index in 0..lhs_len {
        let Some(a) = runtime_numeric_to_f32(rt_array_get(lhs, index as i64)) else {
            return RuntimeValue::NIL;
        };
        let Some(b) = runtime_numeric_to_f32(rt_array_get(rhs, index as i64)) else {
            return RuntimeValue::NIL;
        };
        acc = a.mul_add(b, acc);
    }
    RuntimeValue::from_float(acc as f64)
}

fn scalar_dot_runtime_f64(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_len) = runtime_array_len_usize(lhs) else {
        return RuntimeValue::NIL;
    };
    if runtime_array_len_usize(rhs) != Some(lhs_len) {
        return RuntimeValue::NIL;
    }
    let mut acc = 0.0f64;
    for index in 0..lhs_len {
        let Some(a) = runtime_numeric_to_f64(rt_array_get(lhs, index as i64)) else {
            return RuntimeValue::NIL;
        };
        let Some(b) = runtime_numeric_to_f64(rt_array_get(rhs, index as i64)) else {
            return RuntimeValue::NIL;
        };
        acc = a.mul_add(b, acc);
    }
    RuntimeValue::from_float(acc)
}

fn scalar_reduce_runtime_f32(value: RuntimeValue, mut acc: f32, op: impl Fn(f32, f32) -> f32) -> RuntimeValue {
    let Some(len) = runtime_array_len_usize(value) else {
        return RuntimeValue::NIL;
    };
    for index in 0..len {
        let Some(item) = runtime_numeric_to_f32(rt_array_get(value, index as i64)) else {
            return RuntimeValue::NIL;
        };
        acc = op(acc, item);
    }
    RuntimeValue::from_float(acc as f64)
}

fn scalar_min_runtime_f32(value: RuntimeValue) -> RuntimeValue {
    let Some(len) = runtime_array_len_usize(value) else {
        return RuntimeValue::NIL;
    };
    if len == 0 {
        return RuntimeValue::NIL;
    }
    let Some(mut acc) = runtime_numeric_to_f32(rt_array_get(value, 0)) else {
        return RuntimeValue::NIL;
    };
    for index in 1..len {
        let Some(item) = runtime_numeric_to_f32(rt_array_get(value, index as i64)) else {
            return RuntimeValue::NIL;
        };
        acc = acc.min(item);
    }
    RuntimeValue::from_float(acc as f64)
}

fn scalar_max_runtime_f32(value: RuntimeValue) -> RuntimeValue {
    let Some(len) = runtime_array_len_usize(value) else {
        return RuntimeValue::NIL;
    };
    if len == 0 {
        return RuntimeValue::NIL;
    }
    let Some(mut acc) = runtime_numeric_to_f32(rt_array_get(value, 0)) else {
        return RuntimeValue::NIL;
    };
    for index in 1..len {
        let Some(item) = runtime_numeric_to_f32(rt_array_get(value, index as i64)) else {
            return RuntimeValue::NIL;
        };
        acc = acc.max(item);
    }
    RuntimeValue::from_float(acc as f64)
}

fn scalar_add_f32(lhs: &[f32], rhs: &[f32], out: &mut [f32]) {
    for ((out, lhs), rhs) in out.iter_mut().zip(lhs.iter()).zip(rhs.iter()) {
        *out = *lhs + *rhs;
    }
}

fn scalar_mul_f32(lhs: &[f32], rhs: &[f32], out: &mut [f32]) {
    for ((out, lhs), rhs) in out.iter_mut().zip(lhs.iter()).zip(rhs.iter()) {
        *out = *lhs * *rhs;
    }
}

fn scalar_fma_f32(a: &[f32], b: &[f32], c: &[f32], out: &mut [f32]) {
    for (((out, a), b), c) in out.iter_mut().zip(a.iter()).zip(b.iter()).zip(c.iter()) {
        *out = a.mul_add(*b, *c);
    }
}

fn scalar_dot_f32(lhs: &[f32], rhs: &[f32]) -> f32 {
    lhs.iter()
        .zip(rhs.iter())
        .fold(0.0f32, |acc, (lhs, rhs)| lhs.mul_add(*rhs, acc))
}

fn scalar_sum_f32(values: &[f32]) -> f32 {
    values.iter().copied().sum()
}

fn scalar_min_f32(values: &[f32]) -> f32 {
    values.iter().copied().reduce(f32::min).unwrap_or(0.0)
}

fn scalar_max_f32(values: &[f32]) -> f32 {
    values.iter().copied().reduce(f32::max).unwrap_or(0.0)
}

fn scalar_add_f64(lhs: &[f64], rhs: &[f64], out: &mut [f64]) {
    for ((out, lhs), rhs) in out.iter_mut().zip(lhs.iter()).zip(rhs.iter()) {
        *out = *lhs + *rhs;
    }
}

fn scalar_mul_f64(lhs: &[f64], rhs: &[f64], out: &mut [f64]) {
    for ((out, lhs), rhs) in out.iter_mut().zip(lhs.iter()).zip(rhs.iter()) {
        *out = *lhs * *rhs;
    }
}

fn scalar_fma_f64(a: &[f64], b: &[f64], c: &[f64], out: &mut [f64]) {
    for (((out, a), b), c) in out.iter_mut().zip(a.iter()).zip(b.iter()).zip(c.iter()) {
        *out = a.mul_add(*b, *c);
    }
}

fn scalar_sum_f64(values: &[f64]) -> f64 {
    values.iter().copied().sum()
}

fn scalar_dot_f64(lhs: &[f64], rhs: &[f64]) -> f64 {
    lhs.iter()
        .zip(rhs.iter())
        .fold(0.0f64, |acc, (lhs, rhs)| lhs.mul_add(*rhs, acc))
}

fn avx2_add_f32(lhs: &[f32], rhs: &[f32], out: &mut [f32]) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        avx2_add_f32_impl(lhs, rhs, out);
        return;
    }
    #[allow(unreachable_code)]
    scalar_add_f32(lhs, rhs, out)
}

fn avx2_mul_f32(lhs: &[f32], rhs: &[f32], out: &mut [f32]) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        avx2_mul_f32_impl(lhs, rhs, out);
        return;
    }
    #[allow(unreachable_code)]
    scalar_mul_f32(lhs, rhs, out)
}

fn avx2_fma_f32(a: &[f32], b: &[f32], c: &[f32], out: &mut [f32]) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        if std::arch::is_x86_feature_detected!("fma") {
            avx2_fma_f32_fma_impl(a, b, c, out);
        } else {
            avx2_fma_f32_impl(a, b, c, out);
        }
        return;
    }
    #[allow(unreachable_code)]
    scalar_fma_f32(a, b, c, out)
}

fn avx2_dot_f32(lhs: &[f32], rhs: &[f32]) -> f32 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        return avx2_dot_f32_impl(lhs, rhs);
    }
    #[allow(unreachable_code)]
    scalar_dot_f32(lhs, rhs)
}

fn avx2_sum_f32(values: &[f32]) -> f32 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        return avx2_sum_f32_impl(values);
    }
    #[allow(unreachable_code)]
    scalar_sum_f32(values)
}

fn avx2_min_f32(values: &[f32]) -> f32 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        return avx2_min_f32_impl(values);
    }
    #[allow(unreachable_code)]
    scalar_min_f32(values)
}

fn avx2_max_f32(values: &[f32]) -> f32 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        return avx2_max_f32_impl(values);
    }
    #[allow(unreachable_code)]
    scalar_max_f32(values)
}

fn avx2_add_f64(lhs: &[f64], rhs: &[f64], out: &mut [f64]) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        avx2_add_f64_impl(lhs, rhs, out);
        return;
    }
    #[allow(unreachable_code)]
    scalar_add_f64(lhs, rhs, out)
}

fn avx2_mul_f64(lhs: &[f64], rhs: &[f64], out: &mut [f64]) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        avx2_mul_f64_impl(lhs, rhs, out);
        return;
    }
    #[allow(unreachable_code)]
    scalar_mul_f64(lhs, rhs, out)
}

fn avx2_fma_f64(a: &[f64], b: &[f64], c: &[f64], out: &mut [f64]) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        if std::arch::is_x86_feature_detected!("fma") {
            avx2_fma_f64_fma_impl(a, b, c, out);
        } else {
            avx2_fma_f64_impl(a, b, c, out);
        }
        return;
    }
    #[allow(unreachable_code)]
    scalar_fma_f64(a, b, c, out)
}

fn avx2_sum_f64(values: &[f64]) -> f64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        return avx2_sum_f64_impl(values);
    }
    #[allow(unreachable_code)]
    scalar_sum_f64(values)
}

fn avx2_dot_f64(lhs: &[f64], rhs: &[f64]) -> f64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        return avx2_dot_f64_impl(lhs, rhs);
    }
    #[allow(unreachable_code)]
    scalar_dot_f64(lhs, rhs)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_add_f32_impl(lhs: &[f32], rhs: &[f32], out: &mut [f32]) {
    let width = 8;
    let len = lhs.len().min(rhs.len()).min(out.len());
    let simd_len = len / width * width;
    let mut index = 0;
    while index < simd_len {
        let a = unsafe { _mm256_loadu_ps(lhs.as_ptr().add(index)) };
        let b = unsafe { _mm256_loadu_ps(rhs.as_ptr().add(index)) };
        let sum = _mm256_add_ps(a, b);
        unsafe { _mm256_storeu_ps(out.as_mut_ptr().add(index), sum) };
        index += width;
    }
    scalar_add_f32(&lhs[simd_len..len], &rhs[simd_len..len], &mut out[simd_len..len]);
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_mul_f32_impl(lhs: &[f32], rhs: &[f32], out: &mut [f32]) {
    let width = 8;
    let len = lhs.len().min(rhs.len()).min(out.len());
    let simd_len = len / width * width;
    let mut index = 0;
    while index < simd_len {
        let a = unsafe { _mm256_loadu_ps(lhs.as_ptr().add(index)) };
        let b = unsafe { _mm256_loadu_ps(rhs.as_ptr().add(index)) };
        let product = _mm256_mul_ps(a, b);
        unsafe { _mm256_storeu_ps(out.as_mut_ptr().add(index), product) };
        index += width;
    }
    scalar_mul_f32(&lhs[simd_len..len], &rhs[simd_len..len], &mut out[simd_len..len]);
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_fma_f32_impl(a: &[f32], b: &[f32], c: &[f32], out: &mut [f32]) {
    let width = 8;
    let len = a.len().min(b.len()).min(c.len()).min(out.len());
    let simd_len = len / width * width;
    let mut index = 0;
    while index < simd_len {
        let av = unsafe { _mm256_loadu_ps(a.as_ptr().add(index)) };
        let bv = unsafe { _mm256_loadu_ps(b.as_ptr().add(index)) };
        let cv = unsafe { _mm256_loadu_ps(c.as_ptr().add(index)) };
        let result = _mm256_add_ps(_mm256_mul_ps(av, bv), cv);
        unsafe { _mm256_storeu_ps(out.as_mut_ptr().add(index), result) };
        index += width;
    }
    scalar_fma_f32(
        &a[simd_len..len],
        &b[simd_len..len],
        &c[simd_len..len],
        &mut out[simd_len..len],
    );
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2,fma")]
unsafe fn avx2_fma_f32_fma_impl(a: &[f32], b: &[f32], c: &[f32], out: &mut [f32]) {
    let width = 8;
    let len = a.len().min(b.len()).min(c.len()).min(out.len());
    let simd_len = len / width * width;
    let mut index = 0;
    while index < simd_len {
        let av = unsafe { _mm256_loadu_ps(a.as_ptr().add(index)) };
        let bv = unsafe { _mm256_loadu_ps(b.as_ptr().add(index)) };
        let cv = unsafe { _mm256_loadu_ps(c.as_ptr().add(index)) };
        let result = _mm256_fmadd_ps(av, bv, cv);
        unsafe { _mm256_storeu_ps(out.as_mut_ptr().add(index), result) };
        index += width;
    }
    scalar_fma_f32(
        &a[simd_len..len],
        &b[simd_len..len],
        &c[simd_len..len],
        &mut out[simd_len..len],
    );
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_dot_f32_impl(lhs: &[f32], rhs: &[f32]) -> f32 {
    let width = 8;
    let len = lhs.len().min(rhs.len());
    let simd_len = len / width * width;
    let mut acc = _mm256_setzero_ps();
    let mut index = 0;
    while index < simd_len {
        let a = unsafe { _mm256_loadu_ps(lhs.as_ptr().add(index)) };
        let b = unsafe { _mm256_loadu_ps(rhs.as_ptr().add(index)) };
        acc = _mm256_add_ps(acc, _mm256_mul_ps(a, b));
        index += width;
    }
    let mut lanes = [0.0f32; 8];
    unsafe { _mm256_storeu_ps(lanes.as_mut_ptr(), acc) };
    let mut total = lanes.into_iter().sum::<f32>();
    total += scalar_dot_f32(&lhs[simd_len..len], &rhs[simd_len..len]);
    total
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_sum_f32_impl(values: &[f32]) -> f32 {
    let width = 8;
    let len = values.len();
    let simd_len = len / width * width;
    let mut acc = _mm256_setzero_ps();
    let mut index = 0;
    while index < simd_len {
        let chunk = unsafe { _mm256_loadu_ps(values.as_ptr().add(index)) };
        acc = _mm256_add_ps(acc, chunk);
        index += width;
    }
    let mut lanes = [0.0f32; 8];
    unsafe { _mm256_storeu_ps(lanes.as_mut_ptr(), acc) };
    lanes.into_iter().sum::<f32>() + scalar_sum_f32(&values[simd_len..])
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_min_f32_impl(values: &[f32]) -> f32 {
    if values.is_empty() {
        return 0.0;
    }
    let width = 8;
    let len = values.len();
    if len < width {
        return scalar_min_f32(values);
    }
    let simd_len = len / width * width;
    let mut acc = unsafe { _mm256_loadu_ps(values.as_ptr()) };
    let mut index = width;
    while index < simd_len {
        let chunk = unsafe { _mm256_loadu_ps(values.as_ptr().add(index)) };
        acc = _mm256_min_ps(acc, chunk);
        index += width;
    }
    let mut lanes = [0.0f32; 8];
    unsafe { _mm256_storeu_ps(lanes.as_mut_ptr(), acc) };
    let mut total = lanes.into_iter().reduce(f32::min).unwrap_or(values[0]);
    if simd_len < len {
        total = total.min(scalar_min_f32(&values[simd_len..]));
    }
    total
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_max_f32_impl(values: &[f32]) -> f32 {
    if values.is_empty() {
        return 0.0;
    }
    let width = 8;
    let len = values.len();
    if len < width {
        return scalar_max_f32(values);
    }
    let simd_len = len / width * width;
    let mut acc = unsafe { _mm256_loadu_ps(values.as_ptr()) };
    let mut index = width;
    while index < simd_len {
        let chunk = unsafe { _mm256_loadu_ps(values.as_ptr().add(index)) };
        acc = _mm256_max_ps(acc, chunk);
        index += width;
    }
    let mut lanes = [0.0f32; 8];
    unsafe { _mm256_storeu_ps(lanes.as_mut_ptr(), acc) };
    let mut total = lanes.into_iter().reduce(f32::max).unwrap_or(values[0]);
    if simd_len < len {
        total = total.max(scalar_max_f32(&values[simd_len..]));
    }
    total
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_add_f64_impl(lhs: &[f64], rhs: &[f64], out: &mut [f64]) {
    let width = 4;
    let len = lhs.len().min(rhs.len()).min(out.len());
    let simd_len = len / width * width;
    let mut index = 0;
    while index < simd_len {
        let a = unsafe { _mm256_loadu_pd(lhs.as_ptr().add(index)) };
        let b = unsafe { _mm256_loadu_pd(rhs.as_ptr().add(index)) };
        let sum = _mm256_add_pd(a, b);
        unsafe { _mm256_storeu_pd(out.as_mut_ptr().add(index), sum) };
        index += width;
    }
    scalar_add_f64(&lhs[simd_len..len], &rhs[simd_len..len], &mut out[simd_len..len]);
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_mul_f64_impl(lhs: &[f64], rhs: &[f64], out: &mut [f64]) {
    let width = 4;
    let len = lhs.len().min(rhs.len()).min(out.len());
    let simd_len = len / width * width;
    let mut index = 0;
    while index < simd_len {
        let a = unsafe { _mm256_loadu_pd(lhs.as_ptr().add(index)) };
        let b = unsafe { _mm256_loadu_pd(rhs.as_ptr().add(index)) };
        let product = _mm256_mul_pd(a, b);
        unsafe { _mm256_storeu_pd(out.as_mut_ptr().add(index), product) };
        index += width;
    }
    scalar_mul_f64(&lhs[simd_len..len], &rhs[simd_len..len], &mut out[simd_len..len]);
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_fma_f64_impl(a: &[f64], b: &[f64], c: &[f64], out: &mut [f64]) {
    let width = 4;
    let len = a.len().min(b.len()).min(c.len()).min(out.len());
    let simd_len = len / width * width;
    let mut index = 0;
    while index < simd_len {
        let av = unsafe { _mm256_loadu_pd(a.as_ptr().add(index)) };
        let bv = unsafe { _mm256_loadu_pd(b.as_ptr().add(index)) };
        let cv = unsafe { _mm256_loadu_pd(c.as_ptr().add(index)) };
        let result = _mm256_add_pd(_mm256_mul_pd(av, bv), cv);
        unsafe { _mm256_storeu_pd(out.as_mut_ptr().add(index), result) };
        index += width;
    }
    scalar_fma_f64(
        &a[simd_len..len],
        &b[simd_len..len],
        &c[simd_len..len],
        &mut out[simd_len..len],
    );
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2,fma")]
unsafe fn avx2_fma_f64_fma_impl(a: &[f64], b: &[f64], c: &[f64], out: &mut [f64]) {
    let width = 4;
    let len = a.len().min(b.len()).min(c.len()).min(out.len());
    let simd_len = len / width * width;
    let mut index = 0;
    while index < simd_len {
        let av = unsafe { _mm256_loadu_pd(a.as_ptr().add(index)) };
        let bv = unsafe { _mm256_loadu_pd(b.as_ptr().add(index)) };
        let cv = unsafe { _mm256_loadu_pd(c.as_ptr().add(index)) };
        let result = _mm256_fmadd_pd(av, bv, cv);
        unsafe { _mm256_storeu_pd(out.as_mut_ptr().add(index), result) };
        index += width;
    }
    scalar_fma_f64(
        &a[simd_len..len],
        &b[simd_len..len],
        &c[simd_len..len],
        &mut out[simd_len..len],
    );
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_sum_f64_impl(values: &[f64]) -> f64 {
    let width = 4;
    let len = values.len();
    let simd_len = len / width * width;
    let mut acc = _mm256_setzero_pd();
    let mut index = 0;
    while index < simd_len {
        let chunk = unsafe { _mm256_loadu_pd(values.as_ptr().add(index)) };
        acc = _mm256_add_pd(acc, chunk);
        index += width;
    }
    let mut lanes = [0.0f64; 4];
    unsafe { _mm256_storeu_pd(lanes.as_mut_ptr(), acc) };
    lanes.into_iter().sum::<f64>() + scalar_sum_f64(&values[simd_len..])
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_dot_f64_impl(lhs: &[f64], rhs: &[f64]) -> f64 {
    let width = 4;
    let len = lhs.len().min(rhs.len());
    let simd_len = len / width * width;
    let mut acc = _mm256_setzero_pd();
    let mut index = 0;
    while index < simd_len {
        let a = unsafe { _mm256_loadu_pd(lhs.as_ptr().add(index)) };
        let b = unsafe { _mm256_loadu_pd(rhs.as_ptr().add(index)) };
        acc = _mm256_add_pd(acc, _mm256_mul_pd(a, b));
        index += width;
    }
    let mut lanes = [0.0f64; 4];
    unsafe { _mm256_storeu_pd(lanes.as_mut_ptr(), acc) };
    let mut total = lanes.into_iter().sum::<f64>();
    total += scalar_dot_f64(&lhs[simd_len..len], &rhs[simd_len..len]);
    total
}

fn neon_add_f32(lhs: &[f32], rhs: &[f32], out: &mut [f32]) {
    scalar_add_f32(lhs, rhs, out)
}

fn neon_mul_f32(lhs: &[f32], rhs: &[f32], out: &mut [f32]) {
    scalar_mul_f32(lhs, rhs, out)
}

fn neon_fma_f32(a: &[f32], b: &[f32], c: &[f32], out: &mut [f32]) {
    scalar_fma_f32(a, b, c, out)
}

fn neon_dot_f32(lhs: &[f32], rhs: &[f32]) -> f32 {
    scalar_dot_f32(lhs, rhs)
}

fn neon_sum_f32(values: &[f32]) -> f32 {
    scalar_sum_f32(values)
}

fn neon_min_f32(values: &[f32]) -> f32 {
    scalar_min_f32(values)
}

fn neon_max_f32(values: &[f32]) -> f32 {
    scalar_max_f32(values)
}

fn neon_add_f64(lhs: &[f64], rhs: &[f64], out: &mut [f64]) {
    scalar_add_f64(lhs, rhs, out)
}

fn neon_mul_f64(lhs: &[f64], rhs: &[f64], out: &mut [f64]) {
    scalar_mul_f64(lhs, rhs, out)
}

fn neon_fma_f64(a: &[f64], b: &[f64], c: &[f64], out: &mut [f64]) {
    scalar_fma_f64(a, b, c, out)
}

fn neon_sum_f64(values: &[f64]) -> f64 {
    scalar_sum_f64(values)
}

fn neon_dot_f64(lhs: &[f64], rhs: &[f64]) -> f64 {
    scalar_dot_f64(lhs, rhs)
}

fn packed_add_f32(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_vec) = pack_f32_array(lhs) else {
        return scalar_array_binary_f32(lhs, rhs, |lhs, rhs| lhs + rhs);
    };
    let Some(rhs_vec) = pack_f32_array(rhs) else {
        return scalar_array_binary_f32(lhs, rhs, |lhs, rhs| lhs + rhs);
    };
    if lhs_vec.len() != rhs_vec.len() || !should_use_packed_f32(lhs_vec.len()) {
        return scalar_array_binary_f32(lhs, rhs, |lhs, rhs| lhs + rhs);
    }
    let mut out = vec![0.0f32; lhs_vec.len()];
    (numeric_kernel_provider().add_f32)(&lhs_vec, &rhs_vec, &mut out);
    runtime_array_from_f32(&out)
}

fn packed_mul_f32(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_vec) = pack_f32_array(lhs) else {
        return scalar_array_binary_f32(lhs, rhs, |lhs, rhs| lhs * rhs);
    };
    let Some(rhs_vec) = pack_f32_array(rhs) else {
        return scalar_array_binary_f32(lhs, rhs, |lhs, rhs| lhs * rhs);
    };
    if lhs_vec.len() != rhs_vec.len() || !should_use_packed_f32(lhs_vec.len()) {
        return scalar_array_binary_f32(lhs, rhs, |lhs, rhs| lhs * rhs);
    }
    let mut out = vec![0.0f32; lhs_vec.len()];
    (numeric_kernel_provider().mul_f32)(&lhs_vec, &rhs_vec, &mut out);
    runtime_array_from_f32(&out)
}

fn packed_fma_f32(a: RuntimeValue, b: RuntimeValue, c: RuntimeValue) -> RuntimeValue {
    let Some(a_vec) = pack_f32_array(a) else {
        return scalar_array_fma_f32(a, b, c);
    };
    let Some(b_vec) = pack_f32_array(b) else {
        return scalar_array_fma_f32(a, b, c);
    };
    let Some(c_vec) = pack_f32_array(c) else {
        return scalar_array_fma_f32(a, b, c);
    };
    if a_vec.len() != b_vec.len() || a_vec.len() != c_vec.len() || !should_use_packed_f32(a_vec.len()) {
        return scalar_array_fma_f32(a, b, c);
    }
    let mut out = vec![0.0f32; a_vec.len()];
    (numeric_kernel_provider().fma_f32)(&a_vec, &b_vec, &c_vec, &mut out);
    runtime_array_from_f32(&out)
}

fn packed_dot_f32(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_vec) = pack_f32_array(lhs) else {
        return scalar_dot_runtime_f32(lhs, rhs);
    };
    let Some(rhs_vec) = pack_f32_array(rhs) else {
        return scalar_dot_runtime_f32(lhs, rhs);
    };
    if lhs_vec.len() != rhs_vec.len() || !should_use_packed_f32(lhs_vec.len()) {
        return scalar_dot_runtime_f32(lhs, rhs);
    }
    RuntimeValue::from_float((numeric_kernel_provider().dot_f32)(&lhs_vec, &rhs_vec) as f64)
}

fn packed_sum_f32(value: RuntimeValue) -> RuntimeValue {
    let Some(values) = pack_f32_array(value) else {
        return scalar_reduce_runtime_f32(value, 0.0, |acc, item| acc + item);
    };
    if !should_use_packed_f32(values.len()) {
        return scalar_reduce_runtime_f32(value, 0.0, |acc, item| acc + item);
    }
    RuntimeValue::from_float((numeric_kernel_provider().sum_f32)(&values) as f64)
}

fn packed_min_f32(value: RuntimeValue) -> RuntimeValue {
    let Some(values) = pack_f32_array(value) else {
        return scalar_min_runtime_f32(value);
    };
    if values.is_empty() {
        return RuntimeValue::NIL;
    }
    if !should_use_packed_f32(values.len()) {
        return scalar_min_runtime_f32(value);
    }
    RuntimeValue::from_float((numeric_kernel_provider().min_f32)(&values) as f64)
}

fn packed_max_f32(value: RuntimeValue) -> RuntimeValue {
    let Some(values) = pack_f32_array(value) else {
        return scalar_max_runtime_f32(value);
    };
    if values.is_empty() {
        return RuntimeValue::NIL;
    }
    if !should_use_packed_f32(values.len()) {
        return scalar_max_runtime_f32(value);
    }
    RuntimeValue::from_float((numeric_kernel_provider().max_f32)(&values) as f64)
}

fn packed_add_f64(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_vec) = pack_f64_array(lhs) else {
        return scalar_array_binary_f64(lhs, rhs, |lhs, rhs| lhs + rhs);
    };
    let Some(rhs_vec) = pack_f64_array(rhs) else {
        return scalar_array_binary_f64(lhs, rhs, |lhs, rhs| lhs + rhs);
    };
    if lhs_vec.len() != rhs_vec.len() || !should_use_packed_f64(lhs_vec.len()) {
        return scalar_array_binary_f64(lhs, rhs, |lhs, rhs| lhs + rhs);
    }
    let mut out = vec![0.0f64; lhs_vec.len()];
    (numeric_kernel_provider().add_f64)(&lhs_vec, &rhs_vec, &mut out);
    runtime_array_from_f64(&out)
}

fn packed_mul_f64(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_vec) = pack_f64_array(lhs) else {
        return scalar_array_binary_f64(lhs, rhs, |lhs, rhs| lhs * rhs);
    };
    let Some(rhs_vec) = pack_f64_array(rhs) else {
        return scalar_array_binary_f64(lhs, rhs, |lhs, rhs| lhs * rhs);
    };
    if lhs_vec.len() != rhs_vec.len() || !should_use_packed_f64(lhs_vec.len()) {
        return scalar_array_binary_f64(lhs, rhs, |lhs, rhs| lhs * rhs);
    }
    let mut out = vec![0.0f64; lhs_vec.len()];
    (numeric_kernel_provider().mul_f64)(&lhs_vec, &rhs_vec, &mut out);
    runtime_array_from_f64(&out)
}

fn packed_fma_f64(a: RuntimeValue, b: RuntimeValue, c: RuntimeValue) -> RuntimeValue {
    let Some(a_vec) = pack_f64_array(a) else {
        return scalar_array_fma_f64(a, b, c);
    };
    let Some(b_vec) = pack_f64_array(b) else {
        return scalar_array_fma_f64(a, b, c);
    };
    let Some(c_vec) = pack_f64_array(c) else {
        return scalar_array_fma_f64(a, b, c);
    };
    if a_vec.len() != b_vec.len() || a_vec.len() != c_vec.len() || !should_use_packed_f64(a_vec.len()) {
        return scalar_array_fma_f64(a, b, c);
    }
    let mut out = vec![0.0f64; a_vec.len()];
    (numeric_kernel_provider().fma_f64)(&a_vec, &b_vec, &c_vec, &mut out);
    runtime_array_from_f64(&out)
}

fn packed_sum_f64(value: RuntimeValue) -> RuntimeValue {
    let Some(values) = pack_f64_array(value) else {
        let Some(len) = runtime_array_len_usize(value) else {
            return RuntimeValue::NIL;
        };
        let mut acc = 0.0f64;
        for index in 0..len {
            let Some(item) = runtime_numeric_to_f64(rt_array_get(value, index as i64)) else {
                return RuntimeValue::NIL;
            };
            acc += item;
        }
        return RuntimeValue::from_float(acc);
    };
    if !should_use_packed_f64(values.len()) {
        return RuntimeValue::from_float(scalar_sum_f64(&values));
    }
    RuntimeValue::from_float((numeric_kernel_provider().sum_f64)(&values))
}

fn packed_dot_f64(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    let Some(lhs_vec) = pack_f64_array(lhs) else {
        return scalar_dot_runtime_f64(lhs, rhs);
    };
    let Some(rhs_vec) = pack_f64_array(rhs) else {
        return scalar_dot_runtime_f64(lhs, rhs);
    };
    if lhs_vec.len() != rhs_vec.len() || !should_use_packed_f64(lhs_vec.len()) {
        return scalar_dot_runtime_f64(lhs, rhs);
    }
    RuntimeValue::from_float((numeric_kernel_provider().dot_f64)(&lhs_vec, &rhs_vec))
}

#[no_mangle]
pub extern "C" fn rt_numeric_active_simd_tier() -> i64 {
    active_numeric_kernel_tier().rank() as i64
}

#[no_mangle]
pub extern "C" fn rt_numeric_add_f32(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    packed_add_f32(lhs, rhs)
}

#[no_mangle]
pub extern "C" fn rt_numeric_mul_f32(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    packed_mul_f32(lhs, rhs)
}

#[no_mangle]
pub extern "C" fn rt_numeric_fma_f32(a: RuntimeValue, b: RuntimeValue, c: RuntimeValue) -> RuntimeValue {
    packed_fma_f32(a, b, c)
}

#[no_mangle]
pub extern "C" fn rt_numeric_dot_f32(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    packed_dot_f32(lhs, rhs)
}

#[no_mangle]
pub extern "C" fn rt_numeric_sum_f32(value: RuntimeValue) -> RuntimeValue {
    packed_sum_f32(value)
}

#[no_mangle]
pub extern "C" fn rt_numeric_min_f32(value: RuntimeValue) -> RuntimeValue {
    packed_min_f32(value)
}

#[no_mangle]
pub extern "C" fn rt_numeric_max_f32(value: RuntimeValue) -> RuntimeValue {
    packed_max_f32(value)
}

#[no_mangle]
pub extern "C" fn rt_numeric_add_f64(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    packed_add_f64(lhs, rhs)
}

#[no_mangle]
pub extern "C" fn rt_numeric_mul_f64(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    packed_mul_f64(lhs, rhs)
}

#[no_mangle]
pub extern "C" fn rt_numeric_fma_f64(a: RuntimeValue, b: RuntimeValue, c: RuntimeValue) -> RuntimeValue {
    packed_fma_f64(a, b, c)
}

#[no_mangle]
pub extern "C" fn rt_numeric_sum_f64(value: RuntimeValue) -> RuntimeValue {
    packed_sum_f64(value)
}

#[no_mangle]
pub extern "C" fn rt_numeric_dot_f64(lhs: RuntimeValue, rhs: RuntimeValue) -> RuntimeValue {
    packed_dot_f64(lhs, rhs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn runtime_array_to_f64s(value: RuntimeValue) -> Vec<f64> {
        let len = rt_array_len(value);
        let mut out = Vec::new();
        for index in 0..len {
            out.push(rt_array_get(value, index).as_float());
        }
        out
    }

    fn mixed_array() -> RuntimeValue {
        let array = rt_array_new(2);
        rt_array_push(array, RuntimeValue::from_int(1));
        rt_array_push(array, RuntimeValue::from_float(2.5));
        array
    }

    #[test]
    fn thresholds_follow_pack_policy() {
        assert!(!should_use_packed_f32(PACK_THRESHOLD_F32 - 1));
        assert!(should_use_packed_f32(PACK_THRESHOLD_F32));
        assert!(!should_use_packed_f64(PACK_THRESHOLD_F64 - 1));
        assert!(should_use_packed_f64(PACK_THRESHOLD_F64));
    }

    #[test]
    fn sse2_tier_keeps_scalar_kernels_without_rewriting_active_tier() {
        let provider = provider_for_tier(SimdTier::X86_64Sse2);
        assert_eq!(provider.tier, SimdTier::X86_64Sse2);

        let lhs = [1.0f32, 2.0, 3.0];
        let rhs = [4.0f32, 5.0, 6.0];
        let mut out = [0.0f32; 3];
        (provider.add_f32)(&lhs, &rhs, &mut out);
        assert_eq!(out, [5.0, 7.0, 9.0]);
    }

    #[test]
    fn packed_add_f32_matches_scalar() {
        let lhs: Vec<f32> = (0..64).map(|i| i as f32).collect();
        let rhs: Vec<f32> = (0..64).map(|i| (i as f32) * 2.0).collect();
        let result = rt_numeric_add_f32(runtime_array_from_f32(&lhs), runtime_array_from_f32(&rhs));
        assert_eq!(runtime_array_to_f64s(result)[10], 30.0);
    }

    #[test]
    fn mixed_inputs_stay_scalar() {
        let result = rt_numeric_add_f32(mixed_array(), mixed_array());
        assert_eq!(runtime_array_to_f64s(result), vec![2.0, 5.0]);
    }

    #[test]
    fn dot_and_reductions_match_scalar() {
        let lhs: Vec<f32> = (0..80).map(|i| i as f32 * 0.5).collect();
        let rhs: Vec<f32> = (0..80).map(|i| (i as f32) - 4.0).collect();
        let value = runtime_array_from_f32(&lhs);
        let dot = rt_numeric_dot_f32(runtime_array_from_f32(&lhs), runtime_array_from_f32(&rhs));
        assert!((dot.as_float() - scalar_dot_f32(&lhs, &rhs) as f64).abs() < 0.01);
        assert!((rt_numeric_sum_f32(value).as_float() - scalar_sum_f32(&lhs) as f64).abs() < 0.01);
    }

    #[test]
    fn f64_dot_matches_scalar() {
        let lhs: Vec<f64> = (0..48).map(|i| i as f64 * 0.25).collect();
        let rhs: Vec<f64> = (0..48).map(|i| (i as f64) + 1.0).collect();
        let result = rt_numeric_dot_f64(runtime_array_from_f64(&lhs), runtime_array_from_f64(&rhs));
        assert!((result.as_float() - scalar_dot_f64(&lhs, &rhs)).abs() < 0.0001);
    }

    #[test]
    fn packed_f32_ops_handle_avx_tail() {
        let lhs: Vec<f32> = (0..37).map(|i| i as f32 * 1.25 - 3.0).collect();
        let rhs: Vec<f32> = (0..37).map(|i| i as f32 * -0.5 + 2.0).collect();
        let add = rt_numeric_add_f32(runtime_array_from_f32(&lhs), runtime_array_from_f32(&rhs));
        let mul = rt_numeric_mul_f32(runtime_array_from_f32(&lhs), runtime_array_from_f32(&rhs));
        let sum = rt_numeric_sum_f32(runtime_array_from_f32(&lhs));
        let min = rt_numeric_min_f32(runtime_array_from_f32(&lhs));
        let max = rt_numeric_max_f32(runtime_array_from_f32(&lhs));

        let add_values = runtime_array_to_f64s(add);
        let mul_values = runtime_array_to_f64s(mul);
        for index in 0..lhs.len() {
            assert!((add_values[index] - (lhs[index] + rhs[index]) as f64).abs() < 0.001);
            assert!((mul_values[index] - (lhs[index] * rhs[index]) as f64).abs() < 0.001);
        }
        assert!((sum.as_float() - scalar_sum_f32(&lhs) as f64).abs() < 0.01);
        assert!((min.as_float() - scalar_min_f32(&lhs) as f64).abs() < 0.001);
        assert!((max.as_float() - scalar_max_f32(&lhs) as f64).abs() < 0.001);
    }

    #[test]
    fn packed_fma_and_f64_add_match_scalar_with_tail() {
        let a: Vec<f32> = (0..35).map(|i| i as f32 * 0.75 - 1.0).collect();
        let b: Vec<f32> = (0..35).map(|i| i as f32 * -1.25 + 4.0).collect();
        let c: Vec<f32> = (0..35).map(|i| i as f32 * 0.5 + 0.25).collect();
        let fma = rt_numeric_fma_f32(
            runtime_array_from_f32(&a),
            runtime_array_from_f32(&b),
            runtime_array_from_f32(&c),
        );
        let fma_values = runtime_array_to_f64s(fma);
        for index in 0..a.len() {
            assert!((fma_values[index] - a[index].mul_add(b[index], c[index]) as f64).abs() < 0.001);
        }

        let lhs: Vec<f64> = (0..29).map(|i| i as f64 * 1.5 - 2.0).collect();
        let rhs: Vec<f64> = (0..29).map(|i| i as f64 * -0.25 + 7.0).collect();
        let add = rt_numeric_add_f64(runtime_array_from_f64(&lhs), runtime_array_from_f64(&rhs));
        let add_values = runtime_array_to_f64s(add);
        for index in 0..lhs.len() {
            assert!((add_values[index] - (lhs[index] + rhs[index])).abs() < 0.000001);
        }

        let mul = rt_numeric_mul_f64(runtime_array_from_f64(&lhs), runtime_array_from_f64(&rhs));
        let mul_values = runtime_array_to_f64s(mul);
        for index in 0..lhs.len() {
            assert!((mul_values[index] - (lhs[index] * rhs[index])).abs() < 0.000001);
        }

        let sum = rt_numeric_sum_f64(runtime_array_from_f64(&lhs));
        assert!((sum.as_float() - scalar_sum_f64(&lhs)).abs() < 0.000001);
    }

    #[test]
    fn packed_f64_fma_matches_scalar_with_tail() {
        let a: Vec<f64> = (0..27).map(|i| i as f64 * 0.5 - 2.0).collect();
        let b: Vec<f64> = (0..27).map(|i| i as f64 * -0.75 + 3.0).collect();
        let c: Vec<f64> = (0..27).map(|i| i as f64 * 0.25 + 1.0).collect();

        let fma = rt_numeric_fma_f64(
            runtime_array_from_f64(&a),
            runtime_array_from_f64(&b),
            runtime_array_from_f64(&c),
        );
        let fma_values = runtime_array_to_f64s(fma);
        for index in 0..a.len() {
            assert!((fma_values[index] - a[index].mul_add(b[index], c[index])).abs() < 0.000001);
        }
    }
}
