# Compress Shared Helpers Specification

> Tests covering compression shared helper kernels.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compress Shared Helpers Specification

## Scenarios

### compression shared helper kernels

#### decodes repeated match extension bytes until a terminating lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes repeated match extension bytes until a terminating lane
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap().length equals `15 + 255 + 255 + 7`
   - Expected: decoded.unwrap().next_pos equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes repeated match extension bytes until a terminating lane")
val decoded = decode_match_extension_length(15, [255u8, 255u8, 7u8], 0, "lz4 match extension")
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap().length).to_equal(15 + 255 + 255 + 7)
expect(decoded.unwrap().next_pos).to_equal(3)
```

</details>

#### fails closed when match extension bytes are truncated

- fails closed when match extension bytes are truncated
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when match extension bytes are truncated")
val decoded = decode_match_extension_length(15, [255u8], 0, "lz4 match extension")
expect(decoded.is_err()).to_equal(true)
_expect_truncated(decoded.unwrap_err(), "match extension")
```

</details>

#### copies checked literal ranges and advances the cursor

- copies checked literal ranges and advances the cursor
   - Expected: copied.is_err() is false
   - Expected: copied.unwrap().out equals `[0x00u8, 0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]`
   - Expected: copied.unwrap().next_pos equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies checked literal ranges and advances the cursor")
val copied = append_literal_copy([0x00u8], _fixture_bytes(), 3, 6, "lz4 literal body")
expect(copied.is_err()).to_equal(false)
expect(copied.unwrap().out).to_equal([0x00u8, 0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8])
expect(copied.unwrap().next_pos).to_equal(9)
```

</details>

#### fails closed when literal copy would read past the input

- fails closed when literal copy would read past the input
   - Expected: copied.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when literal copy would read past the input")
val copied = append_literal_copy([], _fixture_bytes(), 22, 4, "lz4 literal body")
expect(copied.is_err()).to_equal(true)
_expect_truncated(copied.unwrap_err(), "literal body")
```

</details>

#### keeps overlap-safe match copy parity across explicit scalar avx2 and neon entrypoints

- keeps overlap-safe match copy parity across explicit scalar avx2 and neon entrypoints
   - Expected: scalar.is_err() is false
   - Expected: avx2.is_err() is false
   - Expected: neon.is_err() is false
   - Expected: forced_scalar.unwrap() equals `scalar.unwrap()`
   - Expected: forced_avx2.unwrap() equals `scalar.unwrap()`
   - Expected: forced_neon.unwrap() equals `scalar.unwrap()`
   - Expected: append_self_overlap_copy(base, 4, 8).unwrap() equals `scalar.unwrap()`
   - Expected: scalar.unwrap() equals `"ABCDABCDABCD".bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps overlap-safe match copy parity across explicit scalar avx2 and neon entrypoints")
val base = "ABCD".bytes()
val scalar = append_self_overlap_copy_scalar(base, 4, 8)
val avx2 = append_self_overlap_copy_avx2(base, 4, 8)
val neon = append_self_overlap_copy_neon(base, 4, 8)
val forced_scalar = append_self_overlap_copy_for_tier(base, 4, 8, CompressionSimdTier.scalar)
val forced_avx2 = append_self_overlap_copy_for_tier(base, 4, 8, CompressionSimdTier.avx2)
val forced_neon = append_self_overlap_copy_for_tier(base, 4, 8, CompressionSimdTier.neon)
expect(scalar.is_err()).to_equal(false)
expect(avx2.is_err()).to_equal(false)
expect(neon.is_err()).to_equal(false)
expect(forced_scalar.unwrap()).to_equal(scalar.unwrap())
expect(forced_avx2.unwrap()).to_equal(scalar.unwrap())
expect(forced_neon.unwrap()).to_equal(scalar.unwrap())
expect(append_self_overlap_copy(base, 4, 8).unwrap()).to_equal(scalar.unwrap())
expect(scalar.unwrap()).to_equal("ABCDABCDABCD".bytes())
```

</details>

#### matches crc32 vectors across the forced-tier helper entrypoints

- matches crc32 vectors across the forced-tier helper entrypoints
   - Expected: scalar equals `crc32_bytes(bytes)`
   - Expected: crc32_bytes_avx2(bytes) equals `scalar`
   - Expected: crc32_bytes_neon(bytes) equals `scalar`
   - Expected: crc32_bytes_scalar("123456789".bytes()) equals `0xCBF43926u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches crc32 vectors across the forced-tier helper entrypoints")
val bytes = _fixture_bytes()
val scalar = crc32_bytes_scalar(bytes)
expect(scalar).to_equal(crc32_bytes(bytes))
expect(crc32_bytes_avx2(bytes)).to_equal(scalar)
expect(crc32_bytes_neon(bytes)).to_equal(scalar)
expect(crc32_bytes_scalar("123456789".bytes())).to_equal(0xCBF43926u32)
```

</details>

#### matches xxh32 vectors across the forced-tier helper entrypoints

- matches xxh32 vectors across the forced-tier helper entrypoints
   - Expected: scalar equals `xxhash32_bytes(bytes, seed)`
   - Expected: xxhash32_bytes_avx2(bytes, seed) equals `scalar`
   - Expected: xxhash32_bytes_neon(bytes, seed) equals `scalar`
   - Expected: xxhash32_bytes_scalar("123456789".bytes(), 0u32) equals `0x937BAD67u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches xxh32 vectors across the forced-tier helper entrypoints")
val bytes = _fixture_bytes()
val seed = 0x9747B28Cu32
val scalar = xxhash32_bytes_scalar(bytes, seed)
expect(scalar).to_equal(xxhash32_bytes(bytes, seed))
expect(xxhash32_bytes_avx2(bytes, seed)).to_equal(scalar)
expect(xxhash32_bytes_neon(bytes, seed)).to_equal(scalar)
expect(xxhash32_bytes_scalar("123456789".bytes(), 0u32)).to_equal(0x937BAD67u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/compress_shared_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compression shared helper kernels.
- compression shared helper kernels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `4657804cb2a641fda280ad4d2dce2f266f45b8e74f4016d54388c2661c27c6c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4657804cb2a641fda280ad4d2dce2f266f45b8e74f4016d54388c2661c27c6c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4657804cb2a641fda280ad4d2dce2f266f45b8e74f4016d54388c2661c27c6c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/compress_shared_helpers_spec.spl
mirror: doc/06_spec/unit/lib/common/compress_shared_helpers_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/compress_shared_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/compress_shared_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/compress_shared_helpers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/compress_shared_helpers_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes repeated match extension bytes until a terminating lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress_shared_helpers_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when match extension bytes are truncated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress_shared_helpers_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies checked literal ranges and advances the cursor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
