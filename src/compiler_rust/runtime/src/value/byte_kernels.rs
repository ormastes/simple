use simple_simd::SimdTier;

pub(crate) fn scalar_byte_find(haystack: &[u8], needle: &[u8], start: usize) -> Option<usize> {
    if needle.is_empty() {
        return Some(start.min(haystack.len()));
    }
    if start > haystack.len() || needle.len() > haystack.len() {
        return None;
    }
    let limit = haystack.len().saturating_sub(needle.len());
    (start..=limit).find(|&idx| &haystack[idx..idx + needle.len()] == needle)
}

pub(crate) fn scalar_byte_rfind(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() {
        return Some(haystack.len());
    }
    if needle.len() > haystack.len() {
        return None;
    }
    let mut idx = haystack.len() - needle.len();
    loop {
        if &haystack[idx..idx + needle.len()] == needle {
            return Some(idx);
        }
        if idx == 0 {
            return None;
        }
        idx -= 1;
    }
}

pub(crate) fn scalar_byte_split_ranges(haystack: &str, delimiter: &str) -> Vec<(usize, usize)> {
    if delimiter.is_empty() {
        return haystack
            .char_indices()
            .map(|(idx, ch)| (idx, idx + ch.len_utf8()))
            .chain(std::iter::once((haystack.len(), haystack.len())))
            .collect();
    }

    let bytes = haystack.as_bytes();
    let delimiter_bytes = delimiter.as_bytes();
    let mut ranges = Vec::new();
    let mut start = 0usize;
    while let Some(found) = scalar_byte_find(bytes, delimiter_bytes, start) {
        ranges.push((start, found));
        start = found + delimiter_bytes.len();
    }
    ranges.push((start, haystack.len()));
    ranges
}

pub(crate) fn avx2_byte_find(haystack: &[u8], needle: &[u8], start: usize) -> Option<usize> {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        if std::is_x86_feature_detected!("avx2") {
            return avx2_byte_find_impl(haystack, needle, start);
        }
    }
    scalar_byte_find(haystack, needle, start)
}

pub(crate) fn avx2_byte_rfind(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        if std::is_x86_feature_detected!("avx2") {
            return avx2_byte_rfind_impl(haystack, needle);
        }
    }
    scalar_byte_rfind(haystack, needle)
}

pub(crate) fn neon_byte_find(haystack: &[u8], needle: &[u8], start: usize) -> Option<usize> {
    #[cfg(target_arch = "aarch64")]
    {
        unsafe { neon_byte_find_impl(haystack, needle, start) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        scalar_byte_find(haystack, needle, start)
    }
}

pub(crate) fn neon_byte_rfind(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    #[cfg(target_arch = "aarch64")]
    {
        unsafe { neon_byte_rfind_impl(haystack, needle) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        scalar_byte_rfind(haystack, needle)
    }
}

pub(crate) fn byte_split_ranges_for_tier(simd_tier: SimdTier, haystack: &str, delimiter: &str) -> Vec<(usize, usize)> {
    if delimiter.is_empty() {
        return scalar_byte_split_ranges(haystack, delimiter);
    }

    let find_fn: fn(&[u8], &[u8], usize) -> Option<usize> = match simd_tier {
        SimdTier::X86_64Sse2 | SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => avx2_byte_find,
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => neon_byte_find,
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => scalar_byte_find,
    };

    let mut ranges = Vec::new();
    let mut start = 0usize;
    let bytes = haystack.as_bytes();
    let delimiter_bytes = delimiter.as_bytes();
    while let Some(found) = find_fn(bytes, delimiter_bytes, start) {
        ranges.push((start, found));
        start = found + delimiter_bytes.len();
    }
    ranges.push((start, haystack.len()));
    ranges
}

pub(crate) fn byte_find_for_tier(simd_tier: SimdTier, haystack: &[u8], needle: &[u8], start: usize) -> Option<usize> {
    match simd_tier {
        SimdTier::X86_64Sse2 | SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => avx2_byte_find(haystack, needle, start),
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => neon_byte_find(haystack, needle, start),
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => scalar_byte_find(haystack, needle, start),
    }
}

pub(crate) fn byte_rfind_for_tier(simd_tier: SimdTier, haystack: &[u8], needle: &[u8]) -> Option<usize> {
    match simd_tier {
        SimdTier::X86_64Sse2 | SimdTier::X86_64Avx2 | SimdTier::X86_64Avx512 => avx2_byte_rfind(haystack, needle),
        SimdTier::Aarch64Neon | SimdTier::Aarch64Sve | SimdTier::Aarch64Sve2 => neon_byte_rfind(haystack, needle),
        SimdTier::Riscv64Rvv | SimdTier::Wasm128 | SimdTier::Scalar => scalar_byte_rfind(haystack, needle),
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_byte_find_impl(haystack: &[u8], needle: &[u8], start: usize) -> Option<usize> {
    use std::arch::x86_64::{__m256i, _mm256_cmpeq_epi8, _mm256_loadu_si256, _mm256_movemask_epi8, _mm256_set1_epi8};

    if needle.is_empty() {
        return Some(start.min(haystack.len()));
    }
    if start > haystack.len() || needle.len() > haystack.len() {
        return None;
    }

    let limit = haystack.len() - needle.len();
    let first = _mm256_set1_epi8(needle[0] as i8);
    let mut idx = start;
    while idx <= limit && idx + 32 <= haystack.len() {
        let chunk = _mm256_loadu_si256(haystack.as_ptr().add(idx) as *const __m256i);
        let mut mask = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chunk, first)) as u32;
        let remaining = limit + 1 - idx;
        if remaining < 32 {
            mask &= (1u32 << remaining) - 1;
        }
        while mask != 0 {
            let offset = mask.trailing_zeros() as usize;
            let candidate = idx + offset;
            if &haystack[candidate..candidate + needle.len()] == needle {
                return Some(candidate);
            }
            mask &= mask - 1;
        }
        idx += 32;
    }

    scalar_byte_find(haystack, needle, idx)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn avx2_byte_rfind_impl(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    use std::arch::x86_64::{__m256i, _mm256_cmpeq_epi8, _mm256_loadu_si256, _mm256_movemask_epi8, _mm256_set1_epi8};

    if needle.is_empty() {
        return Some(haystack.len());
    }
    if needle.len() > haystack.len() {
        return None;
    }
    if haystack.len() < 32 {
        return scalar_byte_rfind(haystack, needle);
    }

    let limit = haystack.len() - needle.len();
    let first = _mm256_set1_epi8(needle[0] as i8);
    let mut chunk_end = limit + 1;
    loop {
        let chunk_start = chunk_end.saturating_sub(32);
        let chunk = _mm256_loadu_si256(haystack.as_ptr().add(chunk_start) as *const __m256i);
        let mut mask = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chunk, first)) as u32;
        let valid = chunk_end - chunk_start;
        if valid < 32 {
            mask &= (1u32 << valid) - 1;
        }
        while mask != 0 {
            let highest = 31 - mask.leading_zeros() as usize;
            let candidate = chunk_start + highest;
            if candidate <= limit && &haystack[candidate..candidate + needle.len()] == needle {
                return Some(candidate);
            }
            mask &= !(1u32 << highest);
        }
        if chunk_start == 0 {
            break;
        }
        chunk_end = chunk_start;
    }

    scalar_byte_rfind(haystack, needle)
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn neon_byte_find_impl(haystack: &[u8], needle: &[u8], start: usize) -> Option<usize> {
    use std::arch::aarch64::{uint8x16_t, vceqq_u8, vdupq_n_u8, vgetq_lane_u64, vld1q_u8, vreinterpretq_u64_u8};

    if needle.is_empty() {
        return Some(start.min(haystack.len()));
    }
    if start > haystack.len() || needle.len() > haystack.len() {
        return None;
    }

    let limit = haystack.len() - needle.len();
    let first = vdupq_n_u8(needle[0]);
    let mut idx = start;
    while idx <= limit && idx + 16 <= haystack.len() {
        let chunk: uint8x16_t = vld1q_u8(haystack.as_ptr().add(idx));
        let matches = vceqq_u8(chunk, first);
        let lanes = vreinterpretq_u64_u8(matches);
        let lane0 = vgetq_lane_u64(lanes, 0);
        let lane1 = vgetq_lane_u64(lanes, 1);
        let combined = [lane0, lane1];
        for (lane_idx, lane) in combined.into_iter().enumerate() {
            if lane == 0 {
                continue;
            }
            for byte_idx in 0..8usize {
                if ((lane >> (byte_idx * 8)) & 0xFF) == 0xFF {
                    let candidate = idx + lane_idx * 8 + byte_idx;
                    if candidate <= limit && &haystack[candidate..candidate + needle.len()] == needle {
                        return Some(candidate);
                    }
                }
            }
        }
        idx += 16;
    }

    scalar_byte_find(haystack, needle, idx)
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn neon_byte_rfind_impl(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    use std::arch::aarch64::{uint8x16_t, vceqq_u8, vdupq_n_u8, vgetq_lane_u64, vld1q_u8, vreinterpretq_u64_u8};

    if needle.is_empty() {
        return Some(haystack.len());
    }
    if needle.len() > haystack.len() {
        return None;
    }
    if haystack.len() < 16 {
        return scalar_byte_rfind(haystack, needle);
    }

    let limit = haystack.len() - needle.len();
    let first = vdupq_n_u8(needle[0]);
    let mut chunk_end = limit + 1;
    loop {
        let chunk_start = chunk_end.saturating_sub(16);
        let chunk: uint8x16_t = vld1q_u8(haystack.as_ptr().add(chunk_start));
        let matches = vceqq_u8(chunk, first);
        let lanes = vreinterpretq_u64_u8(matches);
        let lane0 = vgetq_lane_u64(lanes, 0);
        let lane1 = vgetq_lane_u64(lanes, 1);
        for (lane_idx, lane) in [(1usize, lane1), (0usize, lane0)] {
            if lane == 0 {
                continue;
            }
            for byte_idx in (0..8usize).rev() {
                if ((lane >> (byte_idx * 8)) & 0xFF) == 0xFF {
                    let candidate = chunk_start + lane_idx * 8 + byte_idx;
                    if candidate <= limit && &haystack[candidate..candidate + needle.len()] == needle {
                        return Some(candidate);
                    }
                }
            }
        }
        if chunk_start == 0 {
            break;
        }
        chunk_end = chunk_start;
    }

    scalar_byte_rfind(haystack, needle)
}

#[cfg(test)]
mod tests {
    use super::{
        avx2_byte_find, avx2_byte_rfind, byte_split_ranges_for_tier, neon_byte_find, neon_byte_rfind, scalar_byte_find,
        scalar_byte_rfind, scalar_byte_split_ranges,
    };
    use simple_simd::SimdTier;

    #[test]
    fn split_empty_delimiter_tracks_char_boundaries() {
        let ranges = scalar_byte_split_ranges("A€😀", "");
        assert_eq!(ranges, vec![(0, 1), (1, 4), (4, 8), (8, 8)]);
    }

    #[test]
    fn byte_find_and_rfind_match_scalar_for_unaligned_inputs() {
        let haystack = b"xxprefix-needle-suffix-needle";
        let needle = b"needle";
        let start = 3;
        let expected_find = scalar_byte_find(haystack, needle, start);
        let expected_rfind = scalar_byte_rfind(haystack, needle);
        assert_eq!(avx2_byte_find(haystack, needle, start), expected_find);
        assert_eq!(avx2_byte_rfind(haystack, needle), expected_rfind);
        assert_eq!(neon_byte_find(haystack, needle, start), expected_find);
        assert_eq!(neon_byte_rfind(haystack, needle), expected_rfind);
    }

    #[test]
    fn tier_split_uses_same_ranges_as_scalar() {
        let haystack = "alpha--beta--gamma--";
        let expected = scalar_byte_split_ranges(haystack, "--");
        assert_eq!(byte_split_ranges_for_tier(SimdTier::Scalar, haystack, "--"), expected);
        assert_eq!(
            byte_split_ranges_for_tier(SimdTier::X86_64Avx2, haystack, "--"),
            expected
        );
        assert_eq!(
            byte_split_ranges_for_tier(SimdTier::Aarch64Neon, haystack, "--"),
            expected
        );
    }
}
