# Compress Utilities Specification

> Tests covering compression shared utilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compress Utilities Specification

## Scenarios

### compression shared utilities

#### round-trips little-endian integer helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips little-endian integer helpers
   - Expected: out16 equals `[0x12u8, 0x34u8]`
   - Expected: out32 equals `[0x12u8, 0x34u8, 0x56u8, 0x78u8]`
   - Expected: out64 equals `[0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8, 0x08u8]`
   - Expected: read_u16_le(out16, 0).unwrap() equals `0x3412u16`
   - Expected: read_u32_le(out32, 0).unwrap() equals `0x78563412u32`
   - Expected: read_u64_le(out64, 0).unwrap() equals `0x0807060504030201u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips little-endian integer helpers")
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

- writes big-endian u16 bytes in network order
   - Expected: write_u16_be([], 0x3412u16) equals `[0x34u8, 0x12u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes big-endian u16 bytes in network order")
expect(write_u16_be([], 0x3412u16)).to_equal([0x34u8, 0x12u8])
```

</details>

#### reports truncated integer reads with typed errors

- reports truncated integer reads with typed errors
   - Expected: short2.is_err() is true
   - Expected: short4.is_err() is true
   - Expected: short8.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports truncated integer reads with typed errors")
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

- extends outputs with repeated bytes
   - Expected: push_many_byte([0xAAu8], 0x10u8, 4) equals `[0xAAu8, 0x10u8, 0x10u8, 0x10u8, 0x10u8]`
   - Expected: push_many_byte([], 0xFFu8, 0) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extends outputs with repeated bytes")
expect(push_many_byte([0xAAu8], 0x10u8, 4)).to_equal([0xAAu8, 0x10u8, 0x10u8, 0x10u8, 0x10u8])
expect(push_many_byte([], 0xFFu8, 0)).to_equal([])
```

</details>

#### reuses shared append helpers for range copies and overlap copies

- reuses shared append helpers for range copies and overlap copies
   - Expected: append_bytes([0x00u8], [0x01u8, 0x02u8]) equals `[0x00u8, 0x01u8, 0x02u8]`
   - Expected: append_bytes_range([0x00u8], _bytes_0_to_31(), 3, 6) equals `[0x00u8, 0x03u8, 0x04u8, 0x05u8]`
   - Expected: append_self_overlap_copy([0x41u8, 0x42u8], 2, 5).unwrap() equals `"ABABABA".bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses shared append helpers for range copies and overlap copies")
expect(append_bytes([0x00u8], [0x01u8, 0x02u8])).to_equal([0x00u8, 0x01u8, 0x02u8])
expect(append_bytes_range([0x00u8], _bytes_0_to_31(), 3, 6)).to_equal([0x00u8, 0x03u8, 0x04u8, 0x05u8])
expect(append_self_overlap_copy([0x41u8, 0x42u8], 2, 5).unwrap()).to_equal("ABABABA".bytes())
```

</details>

#### fails closed on invalid overlap copy offsets

- fails closed on invalid overlap copy offsets
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on invalid overlap copy offsets")
val result = append_self_overlap_copy([0x41u8], 2, 1)
expect(result.is_err()).to_equal(true)
match result.unwrap_err():
    CompressionError.CorruptStream(message): expect(message).to_contain("offset")
    _: fail("expected corrupt-stream error with offset message")
```

</details>

#### matches published crc32 vectors

- matches published crc32 vectors
   - Expected: crc32_bytes([]) equals `0x00000000u32`
   - Expected: crc32_bytes("123456789".bytes()) equals `0xCBF43926u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches published crc32 vectors")
expect(crc32_bytes([])).to_equal(0x00000000u32)
expect(crc32_bytes("123456789".bytes())).to_equal(0xCBF43926u32)
```

</details>

#### matches published xxh32 vectors

- matches published xxh32 vectors
   - Expected: xxhash32_bytes([], 0u32) equals `0x02CC5D05u32`
   - Expected: xxhash32_bytes("123456789".bytes(), 0u32) equals `0x937BAD67u32`
   - Expected: xxhash32_bytes("123456789".bytes(), 0x9747B28Cu32) equals `0x770BC670u32`
   - Expected: xxhash32_bytes(_bytes_0_to_31(), 0u32) equals `0x830741C1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches published xxh32 vectors")
expect(xxhash32_bytes([], 0u32)).to_equal(0x02CC5D05u32)
expect(xxhash32_bytes("123456789".bytes(), 0u32)).to_equal(0x937BAD67u32)
expect(xxhash32_bytes("123456789".bytes(), 0x9747B28Cu32)).to_equal(0x770BC670u32)
expect(xxhash32_bytes(_bytes_0_to_31(), 0u32)).to_equal(0x830741C1u32)
```

</details>

#### keeps scalar avx2 and neon checksum/hash helpers in parity

- keeps scalar avx2 and neon checksum/hash helpers in parity
   - Expected: avx2_crc equals `scalar_crc`
   - Expected: neon_crc equals `scalar_crc`
   - Expected: avx2_xxh equals `scalar_xxh`
   - Expected: neon_xxh equals `scalar_xxh`
   - Expected: crc32_bytes(bytes) equals `scalar_crc`
   - Expected: xxhash32_bytes(bytes, 0x9747B28Cu32) equals `scalar_xxh`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps scalar avx2 and neon checksum/hash helpers in parity")
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

- maps canonical simd profiles onto the shared compression seam explicitly
   - Expected: compression_simd_tier_from_simd_profile(SimdTier.scalar) equals `CompressionSimdTier.scalar`
   - Expected: compression_simd_tier_from_simd_profile(SimdTier.x86_64_avx2) equals `CompressionSimdTier.avx2`
   - Expected: compression_simd_tier_from_simd_profile(SimdTier.aarch64_neon) equals `CompressionSimdTier.neon`
   - Expected: compression_simd_tier_from_simd_profile(SimdTier.riscv64_rvv) equals `CompressionSimdTier.scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps canonical simd profiles onto the shared compression seam explicitly")
expect(compression_simd_tier_from_simd_profile(SimdTier.scalar)).to_equal(CompressionSimdTier.scalar)
expect(compression_simd_tier_from_simd_profile(SimdTier.x86_64_avx2)).to_equal(CompressionSimdTier.avx2)
expect(compression_simd_tier_from_simd_profile(SimdTier.aarch64_neon)).to_equal(CompressionSimdTier.neon)
expect(compression_simd_tier_from_simd_profile(SimdTier.riscv64_rvv)).to_equal(CompressionSimdTier.scalar)
```

</details>

#### reports the runtime-selected tier with a stable public name

- reports the runtime-selected tier with a stable public name
   - Expected: detected equals `compression_simd_tier_from_simd_profile(detect_profile())`
   - Expected: name equals `scalar`
   - Expected: name equals `avx2`
   - Expected: name equals `neon`
   - Expected: compression_simd_runtime_profile_name() equals `profile_name()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the runtime-selected tier with a stable public name")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compression shared utilities.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4207c4a78e54fde047352439019059cdee0db12eed16711a065b3f169c15c434`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4207c4a78e54fde047352439019059cdee0db12eed16711a065b3f169c15c434`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4207c4a78e54fde047352439019059cdee0db12eed16711a065b3f169c15c434`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress_utilities_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress_utilities_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress_utilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress_utilities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress_utilities_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips little-endian integer helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress_utilities_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes big-endian u16 bytes in network order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress_utilities_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports truncated integer reads with typed errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
