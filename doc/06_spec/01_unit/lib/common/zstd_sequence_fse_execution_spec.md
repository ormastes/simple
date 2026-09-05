# Zstd Sequence Fse Execution Specification

> Tests covering zstd fse/predefined sequence execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Sequence Fse Execution Specification

## Scenarios

### zstd fse/predefined sequence execution

#### packs decoder-read sequences into the MSB-first backward bitstream

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- packs decoder-read sequences into the MSB-first backward bitstream
   - Expected: _zstd_msb_backward_stream(bits) equals `[0x4Au8, 0x00u8, 0x02u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("packs decoder-read sequences into the MSB-first backward bitstream")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 1, 5)
bits = _append_msb_bits(bits, 2, 4)
bits = _append_msb_bits(bits, 1, 1)
bits = _append_msb_bits(bits, 0, 1)
expect(_zstd_msb_backward_stream(bits)).to_equal([0x4Au8, 0x00u8, 0x02u8])
```

</details>

#### packs a longer consumed-bit list with a nontrivial tail

- packs a longer consumed-bit list with a nontrivial tail
   - Expected: _zstd_msb_backward_stream(bits) equals `[0x65u8, 0xDBu8, 0x9Cu8, 0x35u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("packs a longer consumed-bit list with a nontrivial tail")
val bits = [
    1, 0, 1, 0, 1,
    1, 0, 0, 1, 1, 1, 0, 0,
    1, 1, 0, 1, 1, 0, 1, 1,
    0, 1, 1, 0, 0, 1, 0, 1
]
expect(_zstd_msb_backward_stream(bits)).to_equal([0x65u8, 0xDBu8, 0x9Cu8, 0x35u8])
```

</details>

#### executes a sequence using a predefined ll table and rle offset/ml tables

- executes a sequence using a predefined ll table and rle offset/ml tables
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a sequence using a predefined ll table and rle offset/ml tables")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 2, 2)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x14u8,
    0x02u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(6,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8])
```

</details>

#### fails closed on offset code 31 with an invalid match offset instead of unsupported-feature gating

- fails closed on offset code 31 with an invalid match offset instead of unsupported-feature gating
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on offset code 31 with an invalid match offset instead of unsupported-feature gating")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 0, 31)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x14u8,
    0x1Fu8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(4,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "invalid match offset")
```

</details>

#### executes a sequence using an fse-compressed ll table with a prior raw block

- executes a sequence using an fse-compressed ll table with a prior raw block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a sequence using an fse-compressed ll table with a prior raw block")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 5)
bits = _append_msb_bits(bits, 2, 2)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x94u8,
    0x10u8, 0x3Fu8,
    0x02u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(6,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8])
```

</details>

#### executes two sequences using a predefined ll table with state advancement

- executes two sequences using a predefined ll table with state advancement
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes two sequences using a predefined ll table with state advancement")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 0, 2)
bits = _append_msb_bits(bits, 0, 4)
bits = _append_msb_bits(bits, 0, 2)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x14u8,
    0x02u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(7,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes two sequences using an fse-compressed ll table with state advancement

- executes two sequences using an fse-compressed ll table with state advancement
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes two sequences using an fse-compressed ll table with state advancement")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 5)
bits = _append_msb_bits(bits, 0, 2)
bits = _append_msb_bits(bits, 0, 1)
bits = _append_msb_bits(bits, 0, 2)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x94u8,
    0x10u8, 0x3Fu8,
    0x02u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(7,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes two sequences using a predefined offset table with state advancement

- executes two sequences using a predefined offset table with state advancement
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes two sequences using a predefined offset table with state advancement")
var bits: [i64] = []
bits = _append_msb_bits(bits, 14, 5)
bits = _append_msb_bits(bits, 0, 2)
bits = _append_msb_bits(bits, 14, 5)
bits = _append_msb_bits(bits, 0, 2)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x44u8,
    0x00u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(7,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes a sequence using a predefined match-length table

- executes a sequence using a predefined match-length table
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a sequence using a predefined match-length table")
var bits: [i64] = []
bits = _append_msb_bits(bits, 1, 6)
bits = _append_msb_bits(bits, 0, 2)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x50u8,
    0x00u8, 0x02u8
] + sequence_stream
val frame = _zstd_frame(5,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes a sequence with predefined offset and match-length tables together

- executes a sequence with predefined offset and match-length tables together
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a sequence with predefined offset and match-length tables together")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 5)
bits = _append_msb_bits(bits, 1, 6)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x40u8,
    0x00u8
] + sequence_stream
val frame = _zstd_frame(8,
    _raw_block(false, [0x61u8, 0x61u8, 0x61u8, 0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes two sequences with predefined offset and match-length state advancement

- executes two sequences with predefined offset and match-length state advancement
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes two sequences with predefined offset and match-length state advancement")
var bits: [i64] = []
bits = _append_msb_bits(bits, 14, 5)
bits = _append_msb_bits(bits, 1, 6)
bits = _append_msb_bits(bits, 0, 2)
bits = _append_msb_bits(bits, 1, 4)
bits = _append_msb_bits(bits, 14, 5)
bits = _append_msb_bits(bits, 0, 2)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x40u8,
    0x00u8
] + sequence_stream
val frame = _zstd_frame(9,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes two mixed sequences with predefined ll, compressed of, and rle ml tables

- executes two mixed sequences with predefined ll, compressed of, and rle ml tables
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes two mixed sequences with predefined ll, compressed of, and rle ml tables")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 1, 5)
bits = _append_msb_bits(bits, 2, 4)
bits = _append_msb_bits(bits, 1, 1)
bits = _append_msb_bits(bits, 1, 1)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x08u8,
    0x7Au8,
    0x02u8,
    0x24u8,
    0x10u8, 0x3Fu8,
    0x00u8
] + sequence_stream
val frame = _zstd_frame(11,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8, 0x64u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([
    0x61u8, 0x62u8, 0x63u8, 0x64u8,
    0x61u8, 0x62u8, 0x63u8,
    0x7Au8, 0x61u8, 0x62u8, 0x63u8
])
```

</details>

#### executes two mixed sequences with rle ll, compressed of, and predefined ml tables

- executes two mixed sequences with rle ll, compressed of, and predefined ml tables
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes two mixed sequences with rle ll, compressed of, and predefined ml tables")
var bits: [i64] = []
bits = _append_msb_bits(bits, 1, 5)
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 1, 6)
bits = _append_msb_bits(bits, 1, 1)
bits = _append_msb_bits(bits, 0, 1)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x60u8,
    0x00u8,
    0x10u8, 0x3Fu8
] + sequence_stream
val frame = _zstd_frame(12,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([
    0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8,
    0x62u8, 0x63u8, 0x64u8,
    0x61u8, 0x62u8, 0x63u8, 0x64u8
])
```

</details>

#### executes three mixed sequences with repeat-offset resolution after history changes

- executes three mixed sequences with repeat-offset resolution after history changes
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes three mixed sequences with repeat-offset resolution after history changes")
var bits: [i64] = []
bits = _append_msb_bits(bits, 0, 5)
bits = _append_msb_bits(bits, 5, 5)
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 0, 3)
bits = _append_msb_bits(bits, 1, 1)
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 23, 5)
bits = _append_msb_bits(bits, 0, 1)
bits = _append_msb_bits(bits, 1, 1)
bits = _append_msb_bits(bits, 0, 6)
bits = _append_msb_bits(bits, 0, 5)
val sequence_stream = _zstd_msb_backward_stream(bits)
val payload = [
    0x08u8,
    0x7Au8,
    0x03u8,
    0x80u8,
    0x10u8, 0x3Fu8
] + sequence_stream
val frame = _zstd_frame(15,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([
    0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8,
    0x61u8, 0x62u8, 0x63u8,
    0x65u8, 0x61u8, 0x62u8,
    0x7Au8, 0x65u8, 0x61u8, 0x62u8
])
```

</details>

#### fails closed when a predefined/fse sequence bitstream is truncated

- fails closed when a predefined/fse sequence bitstream is truncated
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when a predefined/fse sequence bitstream is truncated")
val payload = [
    0x00u8,
    0x01u8,
    0x14u8,
    0x02u8, 0x00u8,
    0x00u8
]
val frame = _zstd_frame(6,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "end mark")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd fse/predefined sequence execution.
- zstd fse/predefined sequence execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `039141b14e2b3e9d1a442b21224133680b70ea3e14c64e3278e9c7bc0539b4ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `039141b14e2b3e9d1a442b21224133680b70ea3e14c64e3278e9c7bc0539b4ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `039141b14e2b3e9d1a442b21224133680b70ea3e14c64e3278e9c7bc0539b4ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl
mirror: doc/06_spec/01_unit/lib/common/zstd_sequence_fse_execution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/zstd_sequence_fse_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/zstd_sequence_fse_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs decoder-read sequences into the MSB-first backward bitstream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs a longer consumed-bit list with a nontrivial tail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a sequence using a predefined ll table and rle offset/ml tables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
