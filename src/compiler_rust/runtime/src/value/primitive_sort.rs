//! Primitive sort helpers for homogeneous `RuntimeValue` arrays.
//!
//! These helpers operate on contiguous primitive buffers instead of sorting
//! tagged `RuntimeValue` words directly. Mixed or non-primitive arrays are
//! explicitly reported back to the caller so the existing generic path can
//! preserve broader runtime semantics.

use super::core::RuntimeValue;
use simple_simd::{detect_profile, SimdTier};
#[cfg(test)]
use std::cell::Cell;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveSortKind {
    Int64,
    Float64,
    Byte,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveSortDispatch {
    Scalar,
    Avx2,
    Neon,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveSortFallback {
    MixedPrimitiveKinds,
    NonPrimitive,
    FloatNaN,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrimitiveSortReport {
    pub kind: Option<PrimitiveSortKind>,
    pub dispatch: PrimitiveSortDispatch,
    pub len: usize,
    pub fallback: Option<PrimitiveSortFallback>,
}

impl PrimitiveSortReport {
    #[inline]
    const fn sorted(kind: Option<PrimitiveSortKind>, dispatch: PrimitiveSortDispatch, len: usize) -> Self {
        Self {
            kind,
            dispatch,
            len,
            fallback: None,
        }
    }

    #[inline]
    const fn fallback(dispatch: PrimitiveSortDispatch, len: usize, reason: PrimitiveSortFallback) -> Self {
        Self {
            kind: None,
            dispatch,
            len,
            fallback: Some(reason),
        }
    }

    #[inline]
    pub const fn used_specialized_path(self) -> bool {
        self.fallback.is_none()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrimitiveSortClassification {
    Int64,
    Float64,
    Byte,
}

const SIMD_RADIX_MIN_LEN: usize = 128;
const SIMD_BYTE_HISTOGRAM_MIN_LEN: usize = 256;
const RADIX_PASS_BITS: usize = 8;
const RADIX_BUCKETS: usize = 1 << RADIX_PASS_BITS;
const AVX2_I64_RADIX_MIN_LEN: usize = usize::MAX;
const AVX2_F64_RADIX_MIN_LEN: usize = usize::MAX;
const NEON_I64_RADIX_MIN_LEN: usize = usize::MAX;
const NEON_F64_RADIX_MIN_LEN: usize = usize::MAX;

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TestKernelPath {
    ScalarI64,
    ScalarF64,
    ScalarU8,
    Avx2I64Radix,
    Avx2F64Radix,
    Avx2U8Histogram,
    NeonU8Histogram,
}

#[cfg(test)]
thread_local! {
    static LAST_KERNEL_PATH: Cell<Option<TestKernelPath>> = const { Cell::new(None) };
}

#[cfg(test)]
fn record_test_kernel(path: TestKernelPath) {
    LAST_KERNEL_PATH.with(|slot| slot.set(Some(path)));
}

#[cfg(test)]
fn take_test_kernel() -> Option<TestKernelPath> {
    LAST_KERNEL_PATH.with(|slot| slot.replace(None))
}

#[inline]
pub const fn dispatch_for_tier(tier: SimdTier) -> PrimitiveSortDispatch {
    match tier {
        SimdTier::X86_64Avx2 => PrimitiveSortDispatch::Avx2,
        SimdTier::Aarch64Neon => PrimitiveSortDispatch::Neon,
        SimdTier::Scalar | SimdTier::Riscv64Rvv => PrimitiveSortDispatch::Scalar,
    }
}

#[inline]
pub fn sort_runtime_values_auto(values: &mut [RuntimeValue]) -> PrimitiveSortReport {
    sort_runtime_values(values, detect_profile())
}

pub fn sort_runtime_values(values: &mut [RuntimeValue], tier: SimdTier) -> PrimitiveSortReport {
    let dispatch = dispatch_for_tier(tier);
    if values.len() < 2 {
        return PrimitiveSortReport::sorted(None, dispatch, values.len());
    }

    match classify(values) {
        Ok(PrimitiveSortClassification::Int64) => {
            let mut packed = values.iter().map(|value| value.as_int()).collect::<Vec<_>>();
            sort_i64(&mut packed, dispatch);
            for (slot, value) in values.iter_mut().zip(packed) {
                *slot = RuntimeValue::from_int(value);
            }
            PrimitiveSortReport::sorted(Some(PrimitiveSortKind::Int64), dispatch, values.len())
        }
        Ok(PrimitiveSortClassification::Float64) => {
            let mut packed = values.iter().map(|value| value.as_float()).collect::<Vec<_>>();
            sort_f64(&mut packed, dispatch);
            for (slot, value) in values.iter_mut().zip(packed) {
                *slot = RuntimeValue::from_float(value);
            }
            PrimitiveSortReport::sorted(Some(PrimitiveSortKind::Float64), dispatch, values.len())
        }
        Ok(PrimitiveSortClassification::Byte) => {
            let mut packed = values
                .iter()
                .map(|value| u8::try_from(value.as_int()).expect("byte classification guarantees range"))
                .collect::<Vec<_>>();
            sort_u8(&mut packed, dispatch);
            for (slot, value) in values.iter_mut().zip(packed) {
                *slot = RuntimeValue::from_int(i64::from(value));
            }
            PrimitiveSortReport::sorted(Some(PrimitiveSortKind::Byte), dispatch, values.len())
        }
        Err(reason) => PrimitiveSortReport::fallback(dispatch, values.len(), reason),
    }
}

fn classify(values: &[RuntimeValue]) -> Result<PrimitiveSortClassification, PrimitiveSortFallback> {
    let mut saw_int = false;
    let mut saw_float = false;
    let mut all_bytes = true;

    for value in values {
        if value.is_int() {
            saw_int = true;
            let int_value = value.as_int();
            if !(0..=255).contains(&int_value) {
                all_bytes = false;
            }
            continue;
        }

        if value.is_float() {
            if value.as_float().is_nan() {
                return Err(PrimitiveSortFallback::FloatNaN);
            }
            saw_float = true;
            all_bytes = false;
            continue;
        }

        return Err(PrimitiveSortFallback::NonPrimitive);
    }

    match (saw_int, saw_float, all_bytes) {
        (true, false, true) => Ok(PrimitiveSortClassification::Byte),
        (true, false, false) => Ok(PrimitiveSortClassification::Int64),
        (false, true, false) => Ok(PrimitiveSortClassification::Float64),
        (true, true, _) => Err(PrimitiveSortFallback::MixedPrimitiveKinds),
        _ => Err(PrimitiveSortFallback::NonPrimitive),
    }
}

#[inline]
fn sort_i64(values: &mut [i64], dispatch: PrimitiveSortDispatch) {
    match dispatch {
        PrimitiveSortDispatch::Scalar => scalar_sort_i64(values),
        PrimitiveSortDispatch::Avx2 => avx2_sort_i64(values),
        PrimitiveSortDispatch::Neon => neon_sort_i64(values),
    }
}

#[inline]
fn sort_f64(values: &mut [f64], dispatch: PrimitiveSortDispatch) {
    match dispatch {
        PrimitiveSortDispatch::Scalar => scalar_sort_f64(values),
        PrimitiveSortDispatch::Avx2 => avx2_sort_f64(values),
        PrimitiveSortDispatch::Neon => neon_sort_f64(values),
    }
}

#[inline]
fn sort_u8(values: &mut [u8], dispatch: PrimitiveSortDispatch) {
    match dispatch {
        PrimitiveSortDispatch::Scalar => scalar_sort_u8(values),
        PrimitiveSortDispatch::Avx2 => avx2_sort_u8(values),
        PrimitiveSortDispatch::Neon => neon_sort_u8(values),
    }
}

#[inline]
fn scalar_sort_i64(values: &mut [i64]) {
    #[cfg(test)]
    record_test_kernel(TestKernelPath::ScalarI64);
    values.sort_unstable();
}

#[inline]
fn scalar_sort_f64(values: &mut [f64]) {
    #[cfg(test)]
    record_test_kernel(TestKernelPath::ScalarF64);
    values.sort_unstable_by(f64::total_cmp);
}

#[inline]
fn scalar_sort_u8(values: &mut [u8]) {
    #[cfg(test)]
    record_test_kernel(TestKernelPath::ScalarU8);
    values.sort_unstable();
}

#[inline]
fn i64_to_sortable_key(value: i64) -> u64 {
    (value as u64) ^ (1_u64 << 63)
}

#[inline]
fn sortable_key_to_i64(key: u64) -> i64 {
    (key ^ (1_u64 << 63)) as i64
}

#[inline]
fn f64_to_sortable_key(value: f64) -> u64 {
    let bits = value.to_bits();
    let sign_spread = 0_u64.wrapping_sub(bits >> 63);
    bits ^ (sign_spread | (1_u64 << 63))
}

#[inline]
fn sortable_key_to_f64(key: u64) -> f64 {
    let bits = if (key >> 63) == 1 { key ^ (1_u64 << 63) } else { !key };
    f64::from_bits(bits)
}

fn radix_sort_u64(values: &mut [u64]) {
    let len = values.len();
    if len < 2 {
        return;
    }

    let mut scratch = vec![0_u64; len];
    let mut from_input = true;

    for shift in (0..64).step_by(RADIX_PASS_BITS) {
        let mut counts = [0_usize; RADIX_BUCKETS];
        if from_input {
            for &value in values.iter() {
                counts[((value >> shift) & 0xff) as usize] += 1;
            }
        } else {
            for &value in scratch.iter() {
                counts[((value >> shift) & 0xff) as usize] += 1;
            }
        }

        let mut offsets = [0_usize; RADIX_BUCKETS];
        let mut total = 0_usize;
        for (bucket, count) in counts.into_iter().enumerate() {
            offsets[bucket] = total;
            total += count;
        }

        if from_input {
            for &value in values.iter() {
                let bucket = ((value >> shift) & 0xff) as usize;
                scratch[offsets[bucket]] = value;
                offsets[bucket] += 1;
            }
        } else {
            for &value in scratch.iter() {
                let bucket = ((value >> shift) & 0xff) as usize;
                values[offsets[bucket]] = value;
                offsets[bucket] += 1;
            }
        }

        from_input = !from_input;
    }
}

#[inline]
const fn avx2_i64_radix_enabled(len: usize) -> bool {
    len >= AVX2_I64_RADIX_MIN_LEN
}

#[inline]
const fn avx2_f64_radix_enabled(len: usize) -> bool {
    len >= AVX2_F64_RADIX_MIN_LEN
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "avx2")]
unsafe fn avx2_sort_i64_impl(values: &mut [i64]) {
    use core::arch::x86_64::{__m256i, _mm256_loadu_si256, _mm256_set1_epi64x, _mm256_storeu_si256, _mm256_xor_si256};

    if values.len() < SIMD_RADIX_MIN_LEN || !avx2_i64_radix_enabled(values.len()) {
        scalar_sort_i64(values);
        return;
    }

    #[cfg(test)]
    record_test_kernel(TestKernelPath::Avx2I64Radix);

    let mut keys = vec![0_u64; values.len()];
    let sign = _mm256_set1_epi64x(i64::MIN);

    let mut chunk_index = 0_usize;
    while chunk_index + 4 <= values.len() {
        let input = values.as_ptr().add(chunk_index) as *const __m256i;
        let output = keys.as_mut_ptr().add(chunk_index) as *mut __m256i;
        let lanes = _mm256_loadu_si256(input);
        let mapped = _mm256_xor_si256(lanes, sign);
        _mm256_storeu_si256(output, mapped);
        chunk_index += 4;
    }
    for index in chunk_index..values.len() {
        keys[index] = i64_to_sortable_key(values[index]);
    }

    radix_sort_u64(&mut keys);

    for (slot, key) in values.iter_mut().zip(keys) {
        *slot = sortable_key_to_i64(key);
    }
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "avx2")]
unsafe fn avx2_sort_f64_impl(values: &mut [f64]) {
    use core::arch::x86_64::{
        __m256i, _mm256_cmpgt_epi64, _mm256_loadu_si256, _mm256_or_si256, _mm256_set1_epi64x, _mm256_setzero_si256,
        _mm256_storeu_si256, _mm256_xor_si256,
    };

    if values.len() < SIMD_RADIX_MIN_LEN || !avx2_f64_radix_enabled(values.len()) {
        scalar_sort_f64(values);
        return;
    }

    #[cfg(test)]
    record_test_kernel(TestKernelPath::Avx2F64Radix);

    let mut keys = vec![0_u64; values.len()];
    let sign = _mm256_set1_epi64x(i64::MIN);
    let zero = _mm256_setzero_si256();

    let mut chunk_index = 0_usize;
    while chunk_index + 4 <= values.len() {
        let input = values.as_ptr().add(chunk_index) as *const __m256i;
        let output = keys.as_mut_ptr().add(chunk_index) as *mut __m256i;
        let bits = _mm256_loadu_si256(input);
        let negative_mask = _mm256_cmpgt_epi64(zero, bits);
        let flip_mask = _mm256_or_si256(sign, negative_mask);
        let mapped = _mm256_xor_si256(bits, flip_mask);
        _mm256_storeu_si256(output, mapped);
        chunk_index += 4;
    }
    for index in chunk_index..values.len() {
        keys[index] = f64_to_sortable_key(values[index]);
    }

    radix_sort_u64(&mut keys);

    for (slot, key) in values.iter_mut().zip(keys) {
        *slot = sortable_key_to_f64(key);
    }
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "avx2")]
unsafe fn avx2_sort_u8_impl(values: &mut [u8]) {
    use core::arch::x86_64::{__m256i, _mm256_loadu_si256, _mm256_storeu_si256};

    if values.len() < SIMD_BYTE_HISTOGRAM_MIN_LEN {
        scalar_sort_u8(values);
        return;
    }

    #[cfg(test)]
    record_test_kernel(TestKernelPath::Avx2U8Histogram);

    let mut counts = [0_usize; RADIX_BUCKETS];
    let mut block = [0_u8; 32];
    let mut chunk_index = 0_usize;
    while chunk_index + 32 <= values.len() {
        let input = values.as_ptr().add(chunk_index) as *const __m256i;
        let lanes = _mm256_loadu_si256(input);
        _mm256_storeu_si256(block.as_mut_ptr() as *mut __m256i, lanes);
        for &value in &block {
            counts[value as usize] += 1;
        }
        chunk_index += 32;
    }
    for &value in &values[chunk_index..] {
        counts[value as usize] += 1;
    }

    let mut index = 0_usize;
    for (byte, count) in counts.into_iter().enumerate() {
        if count == 0 {
            continue;
        }
        values[index..index + count].fill(byte as u8);
        index += count;
    }
}

fn avx2_sort_i64(values: &mut [i64]) {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    unsafe {
        return avx2_sort_i64_impl(values);
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    scalar_sort_i64(values);
}

fn avx2_sort_f64(values: &mut [f64]) {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    unsafe {
        return avx2_sort_f64_impl(values);
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    scalar_sort_f64(values);
}

fn avx2_sort_u8(values: &mut [u8]) {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    unsafe {
        return avx2_sort_u8_impl(values);
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    scalar_sort_u8(values);
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn neon_sort_u8_impl(values: &mut [u8]) {
    use core::arch::aarch64::{uint8x16_t, vld1q_u8, vst1q_u8};

    if values.len() < SIMD_BYTE_HISTOGRAM_MIN_LEN {
        scalar_sort_u8(values);
        return;
    }

    #[cfg(test)]
    record_test_kernel(TestKernelPath::NeonU8Histogram);

    let mut counts = [0_usize; RADIX_BUCKETS];
    let mut block = [0_u8; 16];
    let mut chunk_index = 0_usize;
    while chunk_index + 16 <= values.len() {
        let input = values.as_ptr().add(chunk_index);
        let lanes: uint8x16_t = vld1q_u8(input);
        vst1q_u8(block.as_mut_ptr(), lanes);
        for &value in &block {
            counts[value as usize] += 1;
        }
        chunk_index += 16;
    }
    for &value in &values[chunk_index..] {
        counts[value as usize] += 1;
    }

    let mut index = 0_usize;
    for (byte, count) in counts.into_iter().enumerate() {
        if count == 0 {
            continue;
        }
        values[index..index + count].fill(byte as u8);
        index += count;
    }
}

fn neon_sort_i64(values: &mut [i64]) {
    scalar_sort_i64(values);
}

fn neon_sort_f64(values: &mut [f64]) {
    scalar_sort_f64(values);
}

fn neon_sort_u8(values: &mut [u8]) {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        return neon_sort_u8_impl(values);
    }

    #[cfg(not(target_arch = "aarch64"))]
    scalar_sort_u8(values);
}

#[cfg(test)]
mod tests {
    use super::{
        AVX2_F64_RADIX_MIN_LEN, AVX2_I64_RADIX_MIN_LEN, NEON_F64_RADIX_MIN_LEN, NEON_I64_RADIX_MIN_LEN,
        PrimitiveSortDispatch, PrimitiveSortFallback, PrimitiveSortKind, SIMD_BYTE_HISTOGRAM_MIN_LEN,
        SIMD_RADIX_MIN_LEN, TestKernelPath, dispatch_for_tier, sort_runtime_values, take_test_kernel,
    };
    use crate::value::RuntimeValue;
    use simple_simd::SimdTier;
    use std::time::{Duration, Instant};

    fn build_int_values(len: usize) -> Vec<RuntimeValue> {
        (0..len)
            .map(|index| {
                let n = index as i64;
                RuntimeValue::from_int(((n * 97) % 8_191) - ((n * 53) % 4_099))
            })
            .collect()
    }

    fn build_float_values(len: usize) -> Vec<RuntimeValue> {
        let mut values = Vec::with_capacity(len);
        for index in 0..len {
            let value = match index % 9 {
                0 => -0.0,
                1 => 0.0,
                2 => f64::NEG_INFINITY,
                3 => f64::INFINITY,
                _ => ((index as f64 * 1.5) % 4096.0) - ((index as f64 * 0.75) % 2048.0),
            };
            values.push(RuntimeValue::from_float(value));
        }
        values
    }

    fn build_byte_values(len: usize) -> Vec<RuntimeValue> {
        (0..len)
            .map(|index| RuntimeValue::from_int(((index * 29) % 251) as i64))
            .collect()
    }

    #[test]
    fn sorts_homogeneous_i64_arrays() {
        let mut values = [
            RuntimeValue::from_int(9),
            RuntimeValue::from_int(-3),
            RuntimeValue::from_int(4),
            RuntimeValue::from_int(0),
        ];

        let report = sort_runtime_values(&mut values, SimdTier::Scalar);

        assert!(report.used_specialized_path());
        assert_eq!(report.kind, Some(PrimitiveSortKind::Int64));
        assert_eq!(report.dispatch, PrimitiveSortDispatch::Scalar);
        assert_eq!(
            values.iter().map(|value| value.as_int()).collect::<Vec<_>>(),
            vec![-3, 0, 4, 9]
        );
    }

    #[test]
    fn sorts_byte_like_int_arrays() {
        let mut values = [
            RuntimeValue::from_int(255),
            RuntimeValue::from_int(3),
            RuntimeValue::from_int(0),
            RuntimeValue::from_int(128),
        ];

        let report = sort_runtime_values(&mut values, SimdTier::Scalar);

        assert!(report.used_specialized_path());
        assert_eq!(report.kind, Some(PrimitiveSortKind::Byte));
        assert_eq!(
            values.iter().map(|value| value.as_int()).collect::<Vec<_>>(),
            vec![0, 3, 128, 255]
        );
    }

    #[test]
    fn sorts_homogeneous_float_arrays() {
        let mut values = [
            RuntimeValue::from_float(3.5),
            RuntimeValue::from_float(-1.0),
            RuntimeValue::from_float(2.25),
        ];

        let report = sort_runtime_values(&mut values, SimdTier::Scalar);

        assert!(report.used_specialized_path());
        assert_eq!(report.kind, Some(PrimitiveSortKind::Float64));
        assert_eq!(
            values.iter().map(|value| value.as_float()).collect::<Vec<_>>(),
            vec![-1.0, 2.25, 3.5]
        );
    }

    #[test]
    fn mixed_numeric_tags_report_fallback_and_leave_values_unchanged() {
        let original = [
            RuntimeValue::from_int(1),
            RuntimeValue::from_float(2.0),
            RuntimeValue::from_int(0),
        ];
        let mut values = original;

        let report = sort_runtime_values(&mut values, SimdTier::Scalar);

        assert_eq!(report.fallback, Some(PrimitiveSortFallback::MixedPrimitiveKinds));
        assert_eq!(values, original);
    }

    #[test]
    fn non_primitive_arrays_report_fallback_and_leave_values_unchanged() {
        let original = [RuntimeValue::from_int(1), RuntimeValue::TRUE, RuntimeValue::from_int(0)];
        let mut values = original;

        let report = sort_runtime_values(&mut values, SimdTier::Scalar);

        assert_eq!(report.fallback, Some(PrimitiveSortFallback::NonPrimitive));
        assert_eq!(values, original);
    }

    #[test]
    fn nan_float_arrays_report_fallback() {
        let mut values = [RuntimeValue::from_float(f64::NAN), RuntimeValue::from_float(1.0)];

        let report = sort_runtime_values(&mut values, SimdTier::Scalar);

        assert_eq!(report.fallback, Some(PrimitiveSortFallback::FloatNaN));
        assert!(values[0].as_float().is_nan());
        assert_eq!(values[1].as_float(), 1.0);
    }

    #[test]
    fn dispatch_mapping_tracks_simd_tier() {
        assert_eq!(dispatch_for_tier(SimdTier::Scalar), PrimitiveSortDispatch::Scalar);
        assert_eq!(dispatch_for_tier(SimdTier::X86_64Avx2), PrimitiveSortDispatch::Avx2);
        assert_eq!(dispatch_for_tier(SimdTier::Aarch64Neon), PrimitiveSortDispatch::Neon);
        assert_eq!(dispatch_for_tier(SimdTier::Riscv64Rvv), PrimitiveSortDispatch::Scalar);
    }

    #[test]
    fn empty_and_singleton_slices_are_trivial_specialized_successes() {
        let mut empty = [];
        let empty_report = sort_runtime_values(&mut empty, SimdTier::Scalar);
        assert!(empty_report.used_specialized_path());
        assert_eq!(empty_report.kind, None);

        let mut singleton = [RuntimeValue::from_int(7)];
        let singleton_report = sort_runtime_values(&mut singleton, SimdTier::Scalar);
        assert!(singleton_report.used_specialized_path());
        assert_eq!(singleton_report.kind, None);
        assert_eq!(singleton[0].as_int(), 7);
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn avx2_large_paths_match_scalar_results_with_scalar_numeric_fallback_and_byte_specialization() {
        if !std::arch::is_x86_feature_detected!("avx2") {
            return;
        }

        let mut scalar_ints = build_int_values(SIMD_RADIX_MIN_LEN + 65);
        let mut simd_ints = scalar_ints.clone();
        sort_runtime_values(&mut scalar_ints, SimdTier::Scalar);
        let report = sort_runtime_values(&mut simd_ints, SimdTier::X86_64Avx2);
        assert_eq!(report.kind, Some(PrimitiveSortKind::Int64));
        assert_eq!(simd_ints, scalar_ints);
        let expected_int_kernel = if AVX2_I64_RADIX_MIN_LEN <= SIMD_RADIX_MIN_LEN + 65 {
            TestKernelPath::Avx2I64Radix
        } else {
            TestKernelPath::ScalarI64
        };
        assert_eq!(take_test_kernel(), Some(expected_int_kernel));

        let mut scalar_floats = build_float_values(SIMD_RADIX_MIN_LEN + 33);
        let mut simd_floats = scalar_floats.clone();
        sort_runtime_values(&mut scalar_floats, SimdTier::Scalar);
        let report = sort_runtime_values(&mut simd_floats, SimdTier::X86_64Avx2);
        assert_eq!(report.kind, Some(PrimitiveSortKind::Float64));
        assert_eq!(simd_floats, scalar_floats);
        let expected_float_kernel = if AVX2_F64_RADIX_MIN_LEN <= SIMD_RADIX_MIN_LEN + 33 {
            TestKernelPath::Avx2F64Radix
        } else {
            TestKernelPath::ScalarF64
        };
        assert_eq!(take_test_kernel(), Some(expected_float_kernel));

        let mut scalar_bytes = build_byte_values(SIMD_BYTE_HISTOGRAM_MIN_LEN + 47);
        let mut simd_bytes = scalar_bytes.clone();
        sort_runtime_values(&mut scalar_bytes, SimdTier::Scalar);
        let report = sort_runtime_values(&mut simd_bytes, SimdTier::X86_64Avx2);
        assert_eq!(report.kind, Some(PrimitiveSortKind::Byte));
        assert_eq!(simd_bytes, scalar_bytes);
        assert_eq!(take_test_kernel(), Some(TestKernelPath::Avx2U8Histogram));
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn neon_large_paths_match_scalar_results_with_scalar_numeric_fallback_and_byte_specialization() {
        let mut scalar_ints = build_int_values(SIMD_RADIX_MIN_LEN + 65);
        let mut simd_ints = scalar_ints.clone();
        sort_runtime_values(&mut scalar_ints, SimdTier::Scalar);
        let report = sort_runtime_values(&mut simd_ints, SimdTier::Aarch64Neon);
        assert_eq!(report.kind, Some(PrimitiveSortKind::Int64));
        assert_eq!(simd_ints, scalar_ints);
        assert_eq!(take_test_kernel(), Some(TestKernelPath::ScalarI64));

        let mut scalar_floats = build_float_values(SIMD_RADIX_MIN_LEN + 33);
        let mut simd_floats = scalar_floats.clone();
        sort_runtime_values(&mut scalar_floats, SimdTier::Scalar);
        let report = sort_runtime_values(&mut simd_floats, SimdTier::Aarch64Neon);
        assert_eq!(report.kind, Some(PrimitiveSortKind::Float64));
        assert_eq!(simd_floats, scalar_floats);
        assert_eq!(take_test_kernel(), Some(TestKernelPath::ScalarF64));

        let mut scalar_bytes = build_byte_values(SIMD_BYTE_HISTOGRAM_MIN_LEN + 47);
        let mut simd_bytes = scalar_bytes.clone();
        sort_runtime_values(&mut scalar_bytes, SimdTier::Scalar);
        let report = sort_runtime_values(&mut simd_bytes, SimdTier::Aarch64Neon);
        assert_eq!(report.kind, Some(PrimitiveSortKind::Byte));
        assert_eq!(simd_bytes, scalar_bytes);
        assert_eq!(take_test_kernel(), Some(TestKernelPath::NeonU8Histogram));
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn avx2_small_inputs_still_fall_back_to_scalar_kernels() {
        if !std::arch::is_x86_feature_detected!("avx2") {
            return;
        }

        let mut values = build_int_values(16);
        sort_runtime_values(&mut values, SimdTier::X86_64Avx2);
        assert_eq!(take_test_kernel(), Some(TestKernelPath::ScalarI64));
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[cfg(feature = "bench-internals")]
    #[test]
    #[ignore]
    fn probe_avx2_vs_scalar_large_numeric_sorts() {
        if !std::arch::is_x86_feature_detected!("avx2") {
            return;
        }

        fn measure<F>(source: &[RuntimeValue], runs: usize, mut sort_fn: F) -> Duration
        where
            F: FnMut(&mut [RuntimeValue]),
        {
            let mut best = Duration::MAX;
            for _ in 0..runs {
                let mut values = source.to_vec();
                let started = Instant::now();
                sort_fn(&mut values);
                best = best.min(started.elapsed());
            }
            best
        }

        for len in [65_536_usize, 1_048_576] {
            let ints = build_int_values(len);
            let scalar_int = measure(&ints, 12, |values| {
                sort_runtime_values(values, SimdTier::Scalar);
            });
            let host_int = measure(&ints, 12, |values| {
                sort_runtime_values(values, SimdTier::X86_64Avx2);
            });
            eprintln!(
                "sort_int len={} scalar={:.4}ms host={:.4}ms",
                len,
                scalar_int.as_secs_f64() * 1_000.0,
                host_int.as_secs_f64() * 1_000.0
            );

            let floats = build_float_values(len);
            let scalar_float = measure(&floats, 12, |values| {
                sort_runtime_values(values, SimdTier::Scalar);
            });
            let host_float = measure(&floats, 12, |values| {
                sort_runtime_values(values, SimdTier::X86_64Avx2);
            });
            eprintln!(
                "sort_float len={} scalar={:.4}ms host={:.4}ms",
                len,
                scalar_float.as_secs_f64() * 1_000.0,
                host_float.as_secs_f64() * 1_000.0
            );
        }
    }
}
