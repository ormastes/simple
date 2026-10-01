# Lz4 Specification

> Tests covering lz4 pure-Simple block and frame.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lz4 Specification

## Scenarios

### lz4 pure-Simple block and frame

#### round-trips overlap-heavy raw blocks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips overlap-heavy raw blocks
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips overlap-heavy raw blocks")
val input = _repetitive_bytes(8192)
val encoded = lz4_compress_block(input)
val decoded = lz4_decompress_block(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### round-trips repetitive data through the baseline raw-block encoder

- round-trips repetitive data through the baseline raw-block encoder
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips repetitive data through the baseline raw-block encoder")
val input = _repetitive_bytes(8192)
val encoded = lz4_compress_block(input)
val decoded = lz4_decompress_block(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### emits framed bytes with declared content size

- emits framed bytes with declared content size
   - Expected: encoded[4] & 0x20u8 != 0u8 is true
   - Expected: encoded[4] & 0x08u8 != 0u8 is true
   - Expected: encoded[5] equals `0x40u8`
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`
   - Expected: public_decoded.is_err() is false
   - Expected: public_decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits framed bytes with declared content size")
val input = _repetitive_bytes(4096)
val options = _frame_options(false, input.len(), 1)
val encoded = lz4_compress_frame(input, options)
expect(encoded[4] & 0x20u8 != 0u8).to_equal(true)
expect(encoded[4] & 0x08u8 != 0u8).to_equal(true)
expect(encoded[5]).to_equal(0x40u8)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
val public_decoded = decompress_bytes(encoded, nil)
expect(public_decoded.is_err()).to_equal(false)
expect(public_decoded.unwrap()).to_equal(input)
```

</details>

#### keeps public block mode round-tripping through explicit lz4 hint

- keeps public block mode round-tripping through explicit lz4 hint
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps public block mode round-tripping through explicit lz4 hint")
val base = default_compression_options(CompressionCodec.lz4)
val options = CompressionOptions(
    codec: base.codec,
    level: base.level,
    checksum: false,
    block_mode: "block",
    dictionary_bytes: nil,
    dictionary_id: nil,
    content_size: nil
)
val input = _repetitive_bytes(4096)
val encoded = compress_bytes(input, options)
val decoded = decompress_bytes(encoded, Some(CompressionCodec.lz4))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### keeps framed output and decode parity across scalar avx2 and neon tiers

- keeps framed output and decode parity across scalar avx2 and neon tiers
   - Expected: avx2 equals `scalar`
   - Expected: neon equals `scalar`
   - Expected: lz4_compress_frame(input, options) equals `scalar`
   - Expected: lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.scalar).unwrap() equals `input`
   - Expected: lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.avx2).unwrap() equals `input`
   - Expected: lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.neon).unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps framed output and decode parity across scalar avx2 and neon tiers")
val input = _repetitive_bytes(4096)
val options = _frame_options(false, input.len(), 1)
val scalar = lz4_compress_frame_for_tier(input, options, CompressionSimdTier.scalar)
val avx2 = lz4_compress_frame_for_tier(input, options, CompressionSimdTier.avx2)
val neon = lz4_compress_frame_for_tier(input, options, CompressionSimdTier.neon)
expect(avx2).to_equal(scalar)
expect(neon).to_equal(scalar)
expect(lz4_compress_frame(input, options)).to_equal(scalar)
expect(lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.scalar).unwrap()).to_equal(input)
expect(lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.avx2).unwrap()).to_equal(input)
expect(lz4_decompress_frame_for_tier(scalar, CompressionSimdTier.neon).unwrap()).to_equal(input)
```

</details>

#### stores compressed frame blocks for repetitive data on the baseline path

- stores compressed frame blocks for repetitive data on the baseline path
   - Expected: (size_word & 0x80000000u32) equals `0u32`
   - Expected: (size_word & 0x7FFFFFFFu32).to_i64() < input.len() is true
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores compressed frame blocks for repetitive data on the baseline path")
val input = _repetitive_bytes(8192)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
val size_word = _frame_first_block_size_word(encoded)
expect((size_word & 0x80000000u32)).to_equal(0u32)
expect((size_word & 0x7FFFFFFFu32).to_i64() < input.len()).to_equal(true)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### stores incompressible frame blocks as raw literals

- stores incompressible frame blocks as raw literals
   - Expected: (size_word & 0x80000000u32) != 0u32 is true
   - Expected: (size_word & 0x7FFFFFFFu32).to_i64() equals `input.len()`
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores incompressible frame blocks as raw literals")
val input = _unique_bytes(251, 17)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
val size_word = _frame_first_block_size_word(encoded)
expect((size_word & 0x80000000u32) != 0u32).to_equal(true)
expect((size_word & 0x7FFFFFFFu32).to_i64()).to_equal(input.len())
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### emits exact raw single-block frames with host-compatible wire bytes

- emits exact raw single-block frames with host-compatible wire bytes
   - Expected: encoded equals `expected`
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits exact raw single-block frames with host-compatible wire bytes")
val input = [0x00u8, 0x01u8, 0x02u8, 0x03u8]
val expected = _manual_raw_frame(input, false, true)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
expect(encoded).to_equal(expected)
val decoded = lz4_decompress_frame(expected)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### decodes multi-block raw frames with content-size framing

- decodes multi-block raw frames with content-size framing
   - Expected: encoded[4] equals `0x68u8`
   - Expected: _count_frame_blocks(encoded) equals `2`
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes multi-block raw frames with content-size framing")
val first = _unique_bytes(251, 23)
val second = _repetitive_bytes(64)
val input = _concat_bytes(first, second)
val encoded = _manual_raw_two_block_frame(first, second, false, true)
expect(encoded[4]).to_equal(0x68u8)
expect(_count_frame_blocks(encoded)).to_equal(2)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal(input)
```

</details>

#### fails closed on a corrupt frame header checksum

- fails closed on a corrupt frame header checksum
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on a corrupt frame header checksum")
val input = _repetitive_bytes(2048)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
var corrupt = encoded
val hc_offset = _frame_header_checksum_offset(corrupt)
corrupt[hc_offset] = corrupt[hc_offset] ^ 0x01u8
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "header checksum")
```

</details>

#### fails closed on a corrupt block checksum

- fails closed on a corrupt block checksum
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on a corrupt block checksum")
val input = _repetitive_bytes(4096)
val encoded = lz4_compress_frame(input, _frame_options(true, input.len(), 1))
var corrupt = encoded
val payload_offset = _frame_first_block_payload_offset(corrupt)
corrupt[payload_offset] = corrupt[payload_offset] ^ 0x01u8
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "block checksum")
```

</details>

#### fails closed on a corrupt content checksum

- fails closed on a corrupt content checksum
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on a corrupt content checksum")
val input = _repetitive_bytes(4096)
val encoded = lz4_compress_frame(input, _frame_options(true, input.len(), 1))
var corrupt = encoded
val checksum_offset = _frame_content_checksum_offset(corrupt)
corrupt[checksum_offset] = corrupt[checksum_offset] ^ 0x01u8
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "ChecksumMismatch", "content checksum")
```

</details>

#### fails closed on truncated block payload bytes

- fails closed on truncated block payload bytes
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on truncated block payload bytes")
val input = _unique_bytes(251, 91)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
val truncated = encoded.slice(0, encoded.len() - 6)
val decoded = lz4_decompress_frame(truncated)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "lz4 block")
```

</details>

#### fails closed on truncated block checksum bytes

- fails closed on truncated block checksum bytes
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on truncated block checksum bytes")
val input = _unique_bytes(251, 101)
val encoded = lz4_compress_frame(input, _frame_options(true, input.len(), 1))
val truncated = encoded.slice(0, encoded.len() - 10)
val decoded = lz4_decompress_frame(truncated)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "block checksum")
```

</details>

#### fails closed on truncated content checksum bytes

- fails closed on truncated content checksum bytes
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on truncated content checksum bytes")
val input = _unique_bytes(251, 111)
val encoded = lz4_compress_frame(input, _frame_options(true, input.len(), 1))
val truncated = encoded.slice(0, encoded.len() - 2)
val decoded = lz4_decompress_frame(truncated)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "content checksum")
```

</details>

#### validates declared content size against decoded bytes

- validates declared content size against decoded bytes
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates declared content size against decoded bytes")
val input = _repetitive_bytes(2048)
val encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
var corrupt = encoded
corrupt[6] = corrupt[6] + 1u8
corrupt = _set_header_checksum(corrupt)
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "content size mismatch")
```

</details>

#### rejects dependent-block frames explicitly

- rejects dependent-block frames explicitly
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects dependent-block frames explicitly")
val input = _repetitive_bytes(2048)
val encoded = lz4_compress_frame(input, _frame_options(false, nil, 1))
var corrupt = encoded
corrupt[4] = corrupt[4] & 0xDFu8
corrupt = _set_header_checksum(corrupt)
val decoded = lz4_decompress_frame(corrupt)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "dependent blocks")
```

</details>

#### rejects trailing bytes after a valid frame

- rejects trailing bytes after a valid frame
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects trailing bytes after a valid frame")
val input = _repetitive_bytes(2048)
var encoded = lz4_compress_frame(input, _frame_options(false, input.len(), 1))
encoded.push(0xAAu8)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "trailing bytes")
```

</details>

#### rejects empty non-terminal data blocks

- rejects empty non-terminal data blocks
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects empty non-terminal data blocks")
var frame = _manual_raw_frame([0x41u8], false, true)
val size_offset = _frame_header_checksum_offset(frame) + 1
frame[size_offset] = 0u8
frame[size_offset + 1] = 0u8
frame[size_offset + 2] = 0u8
frame[size_offset + 3] = 0x80u8
val decoded = lz4_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "empty data block")
```

</details>

#### rejects impossible raw block back-references

- rejects impossible raw block back-references
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects impossible raw block back-references")
val decoded = lz4_decompress_block([0x00u8, 0x00u8, 0x00u8])
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "invalid match offset")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/lz4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering lz4 pure-Simple block and frame.
- lz4 pure-Simple block and frame

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e711e9c2ce5134d60ceb1774d01f2d92792ee571868a4c24364aef94e0aa7e1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e711e9c2ce5134d60ceb1774d01f2d92792ee571868a4c24364aef94e0aa7e1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e711e9c2ce5134d60ceb1774d01f2d92792ee571868a4c24364aef94e0aa7e1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/lz4_spec.spl
mirror: doc/06_spec/01_unit/lib/common/lz4_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/lz4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/lz4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/lz4_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/lz4_spec.spl:261:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips overlap-heavy raw blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/lz4_spec.spl:270:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips repetitive data through the baseline raw-block encoder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/lz4_spec.spl:279:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits framed bytes with declared content size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
