# Xz Lzma2 Periodic Encode Specification

> Tests covering xz lzma2 periodic encode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Xz Lzma2 Periodic Encode Specification

## Scenarios

### xz lzma2 periodic encode

#### compresses alternating-byte runs into a real lzma2 chunk that host xz can decode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compresses alternating-byte runs into a real lzma2 chunk that host xz can decode
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: lzma2_decompress_xz_lane(encoded).unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses alternating-byte runs into a real lzma2 chunk that host xz can decode")
_ensure_tmp_root()
val input = _repeat_pattern([65u8, 66u8], 96)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz_lane(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
expect(lzma2_decompress_xz_lane(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("alternating", input, encoded)
```

</details>

#### compresses odd-length alternating-byte tails into a real lzma2 chunk that host xz can decode

- compresses odd-length alternating-byte tails into a real lzma2 chunk that host xz can decode
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: lzma2_decompress_xz_lane(encoded).unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses odd-length alternating-byte tails into a real lzma2 chunk that host xz can decode")
_ensure_tmp_root()
val input = _repeat_pattern([65u8, 66u8], 35)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz_lane(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
expect(lzma2_decompress_xz_lane(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("alternating-odd-tail", input, encoded)
```

</details>

#### compresses three-byte periodic runs into a real lzma2 chunk that host xz can decode

- compresses three-byte periodic runs into a real lzma2 chunk that host xz can decode
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: lzma2_decompress_xz_lane(encoded).unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses three-byte periodic runs into a real lzma2 chunk that host xz can decode")
_ensure_tmp_root()
val input = _repeat_pattern([65u8, 66u8, 67u8], 96)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz_lane(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
expect(lzma2_decompress_xz_lane(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("triple-period", input, encoded)
```

</details>

#### compresses three-byte periodic runs across the max-match boundary into a real lzma2 chunk that host xz can decode

- compresses three-byte periodic runs across the max-match boundary into a real lzma2 chunk that host xz can decode
   - Expected: encoded[_first_block_data_start(encoded)] equals `0xE0u8`
   - Expected: _first_block_declared_compressed_size(encoded) < input.len() is true
   - Expected: lzma2_decompress_xz_lane(encoded).unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses three-byte periodic runs across the max-match boundary into a real lzma2 chunk that host xz can decode")
_ensure_tmp_root()
val input = _repeat_pattern([65u8, 66u8, 67u8], 277)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz_lane(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0xE0u8)
expect(_first_block_declared_compressed_size(encoded) < input.len()).to_equal(true)
expect(lzma2_decompress_xz_lane(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("triple-period-max-match", input, encoded)
```

</details>

#### falls back cleanly for four-byte periodic input outside the verified lane

- falls back cleanly for four-byte periodic input outside the verified lane
   - Expected: encoded[_first_block_data_start(encoded)] equals `0x01u8`
   - Expected: lzma2_decompress_xz_lane(encoded).unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back cleanly for four-byte periodic input outside the verified lane")
val input = _repeat_pattern([65u8, 66u8, 67u8, 68u8], 96)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz_lane(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0x01u8)
expect(lzma2_decompress_xz_lane(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("period-four-fallback", input, encoded)
```

</details>

#### falls back cleanly for five-byte periodic input outside the bounded encode lane

- falls back cleanly for five-byte periodic input outside the bounded encode lane
   - Expected: encoded[_first_block_data_start(encoded)] equals `0x01u8`
   - Expected: lzma2_decompress_xz_lane(encoded).unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back cleanly for five-byte periodic input outside the bounded encode lane")
val input = _repeat_pattern([65u8, 66u8, 67u8, 68u8, 69u8], 125)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz_lane(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0x01u8)
expect(lzma2_decompress_xz_lane(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("period-five-fallback", input, encoded)
```

</details>

#### falls back cleanly for mixed periodic data that breaks the bounded encode shape

- falls back cleanly for mixed periodic data that breaks the bounded encode shape
   - Expected: encoded[_first_block_data_start(encoded)] equals `0x01u8`
   - Expected: lzma2_decompress_xz_lane(encoded).unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back cleanly for mixed periodic data that breaks the bounded encode shape")
val input = _repeat_pattern([65u8, 66u8], 48) + [90u8, 91u8, 92u8] + _repeat_pattern([65u8, 66u8], 45)
val options = default_compression_options(CompressionCodec.lzma2)
val encoded = lzma2_compress_xz_lane(input, options)
expect(encoded[_first_block_data_start(encoded)]).to_equal(0x01u8)
expect(lzma2_decompress_xz_lane(encoded).unwrap()).to_equal(input)
_assert_host_xz_roundtrip("mixed-periodic-fallback", input, encoded)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/xz_lzma2_periodic_encode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering xz lzma2 periodic encode.
- xz lzma2 periodic encode

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

- Canonical SPipe generation for source `2e1e4461b7e784e6fd9cdc3a7fcc6873db175ff31c8fd01d78153d01c9fd2acb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2e1e4461b7e784e6fd9cdc3a7fcc6873db175ff31c8fd01d78153d01c9fd2acb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2e1e4461b7e784e6fd9cdc3a7fcc6873db175ff31c8fd01d78153d01c9fd2acb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/xz_lzma2_periodic_encode_spec.spl
mirror: doc/06_spec/01_unit/lib/common/xz_lzma2_periodic_encode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/xz_lzma2_periodic_encode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/xz_lzma2_periodic_encode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/xz_lzma2_periodic_encode_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compresses alternating-byte runs into a real lzma2 chunk that host xz can decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/xz_lzma2_periodic_encode_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compresses odd-length alternating-byte tails into a real lzma2 chunk that host xz can decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/xz_lzma2_periodic_encode_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compresses three-byte periodic runs into a real lzma2 chunk that host xz can decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
