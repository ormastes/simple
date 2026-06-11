# Compress Utilities Specification

> <details>

<!-- sdn-diagram:id=compress_utilities_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compress_utilities_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compress_utilities_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compress_utilities_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compress Utilities Specification

## Scenarios

### compression shared utilities

#### round-trips little-endian integer helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out16 = write_u16_le([], 0x3412u16)
expect(out16).to_equal([0x12u8, 0x34u8])
val out32 = write_u32_le([], 0x78563412u32)
expect(out32).to_equal([0x12u8, 0x34u8, 0x56u8, 0x78u8])
val out64 = write_u64_le([], 0x0807060504030201u64)
expect(out64).to_equal([0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8, 0x08u8])
expect(read_u16_le(out16, 0).unwrap()).to_equal(0x3412u16)
expect(read_u32_le(out32, 0).unwrap()).to_equal(0x78563412u32)
expect(read_u64_le(out64, 0).unwrap()).to_equal(0x0807060504030201u64)
```

</details>

#### writes big-endian u16 bytes in network order

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(write_u16_be([], 0x3412u16)).to_equal([0x34u8, 0x12u8])
```

</details>

#### reports truncated integer reads with typed errors

1.  expect truncated
   - Expected: short4.is_err() is true
2.  expect truncated
   - Expected: short8.is_err() is true
3.  expect truncated


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short2 = read_u16_le([0x01u8], 0)
expect(short2.is_err()).to_equal(true)
_expect_truncated(short2.unwrap_err(), "need 2 bytes")

val short4 = read_u32_le([0x01u8, 0x02u8, 0x03u8], 0)
expect(short4.is_err()).to_equal(true)
_expect_truncated(short4.unwrap_err(), "need 4 bytes")

val short8 = read_u64_le([0x01u8, 0x02u8, 0x03u8, 0x04u8], 0)
expect(short8.is_err()).to_equal(true)
_expect_truncated(short8.unwrap_err(), "need 8 bytes")
```

</details>

#### extends outputs with repeated bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(push_many_byte([0xAAu8], 0x10u8, 4)).to_equal([0xAAu8, 0x10u8, 0x10u8, 0x10u8, 0x10u8])
expect(push_many_byte([], 0xFFu8, 0)).to_equal([])
```

</details>

#### reuses shared append helpers for range copies and overlap copies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(append_bytes([0x00u8], [0x01u8, 0x02u8])).to_equal([0x00u8, 0x01u8, 0x02u8])
expect(append_bytes_range([0x00u8], _bytes_0_to_31(), 3, 6)).to_equal([0x00u8, 0x03u8, 0x04u8, 0x05u8])
expect(append_self_overlap_copy([0x41u8, 0x42u8], 2, 5).unwrap()).to_equal("ABABABA".bytes())
```

</details>

#### fails closed on invalid overlap copy offsets

1.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = append_self_overlap_copy([0x41u8], 2, 1)
expect(result.is_err()).to_equal(true)
match result.unwrap_err():
    CompressionError.CorruptStream(message): expect(message).to_contain("offset")
    _: fail("expected corrupt-stream error with offset message")
```

</details>

#### matches published crc32 vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(crc32_bytes([])).to_equal(0x00000000u32)
expect(crc32_bytes("123456789".bytes())).to_equal(0xCBF43926u32)
```

</details>

#### matches published xxh32 vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(xxhash32_bytes([], 0u32)).to_equal(0x02CC5D05u32)
expect(xxhash32_bytes("123456789".bytes(), 0u32)).to_equal(0x937BAD67u32)
expect(xxhash32_bytes("123456789".bytes(), 0x9747B28Cu32)).to_equal(0x770BC670u32)
expect(xxhash32_bytes(_bytes_0_to_31(), 0u32)).to_equal(0xE84EC021u32)
```

</details>

#### keeps scalar avx2 and neon checksum/hash helpers in parity

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _bytes_0_to_31()
val scalar_crc = crc32_bytes_for_tier(bytes, CompressionSimdTier.scalar)
val avx2_crc = crc32_bytes_for_tier(bytes, CompressionSimdTier.avx2)
val neon_crc = crc32_bytes_for_tier(bytes, CompressionSimdTier.neon)
expect(avx2_crc).to_equal(scalar_crc)
expect(neon_crc).to_equal(scalar_crc)

val scalar_xxh = xxhash32_bytes_for_tier(bytes, 0x9747B28Cu32, CompressionSimdTier.scalar)
val avx2_xxh = xxhash32_bytes_for_tier(bytes, 0x9747B28Cu32, CompressionSimdTier.avx2)
val neon_xxh = xxhash32_bytes_for_tier(bytes, 0x9747B28Cu32, CompressionSimdTier.neon)
expect(avx2_xxh).to_equal(scalar_xxh)
expect(neon_xxh).to_equal(scalar_xxh)
expect(crc32_bytes(bytes)).to_equal(scalar_crc)
expect(xxhash32_bytes(bytes, 0x9747B28Cu32)).to_equal(scalar_xxh)
```

</details>

#### maps canonical simd profiles onto the shared compression seam explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compression_simd_tier_from_simd_profile(SimdTier.scalar)).to_equal(CompressionSimdTier.scalar)
expect(compression_simd_tier_from_simd_profile(SimdTier.x86_64_avx2)).to_equal(CompressionSimdTier.avx2)
expect(compression_simd_tier_from_simd_profile(SimdTier.aarch64_neon)).to_equal(CompressionSimdTier.neon)
expect(compression_simd_tier_from_simd_profile(SimdTier.riscv64_rvv)).to_equal(CompressionSimdTier.scalar)
```

</details>

#### reports the runtime-selected tier with a stable public name

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detected = compression_simd_tier_detect()
expect(detected).to_equal(compression_simd_tier_from_simd_profile(detect_profile()))
val name = compression_simd_tier_name(detected)
if detected == CompressionSimdTier.scalar:
    expect(name).to_equal("scalar")
elif detected == CompressionSimdTier.avx2:
    expect(name).to_equal("avx2")
else:
    expect(name).to_equal("neon")
expect(compression_simd_runtime_profile_name()).to_equal(profile_name())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress_utilities_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compression shared utilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
