# Zstd Compressed Block Specification

> Tests covering zstd compressed blocks with zero sequences.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Compressed Block Specification

## Scenarios

### zstd compressed blocks with zero sequences

#### decodes a compressed block containing raw literals and nbSeq == 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes a compressed block containing raw literals and nbSeq == 0
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a compressed block containing raw literals and nbSeq == 0")
val frame = _zstd_frame(3, _compressed_block([
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8])
```

</details>

#### decodes a compressed block containing RLE literals and nbSeq == 0

- decodes a compressed block containing RLE literals and nbSeq == 0
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x41u8, 0x41u8, 0x41u8, 0x41u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a compressed block containing RLE literals and nbSeq == 0")
val frame = _zstd_frame(4, _compressed_block([
    0x21u8,
    0x41u8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x41u8, 0x41u8, 0x41u8, 0x41u8])
```

</details>

#### rejects the host-rejected fresh-table single-stream direct-weight candidate

- rejects the host-rejected fresh-table single-stream direct-weight candidate
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the host-rejected fresh-table single-stream direct-weight candidate")
val frame = _zstd_frame(4, _compressed_block([
    0x42u8, 0x80u8, 0x01u8
] + _exact_direct_weight_literals_payload() + [
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
# Fresh-table literals now decode through the real Huffman path; this
# host-rejected candidate fails closed because the Huffman stream leaves
# trailing bits (host zstd rejects it as Data corruption likewise).
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "trailing bits")
```

</details>

#### rejects malformed fresh-table four-stream compressed literals with a truncated jump table

- rejects malformed fresh-table four-stream compressed literals with a truncated jump table
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed fresh-table four-stream compressed literals with a truncated jump table")
val frame = _zstd_frame(4, _compressed_block([
    0x46u8, 0x80u8, 0x01u8,
    0x84u8, 0x43u8, 0x20u8, 0x10u8,
    0x80u8, 0x0Du8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
# Size_Format 1 selects 4 streams; this fixture is too small to hold the
# 6-byte jump table, so the real path fails closed on the jump table.
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "4-stream jump table")
```

</details>

#### rejects malformed fresh-table four-stream direct-weight payloads behind the 4-byte header form

- rejects malformed fresh-table four-stream direct-weight payloads behind the 4-byte header form
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed fresh-table four-stream direct-weight payloads behind the 4-byte header form")
val frame = _zstd_frame(4, _compressed_block(_compressed_literals_header(2, 2, 4, 6) + _exact_direct_weight_literals_payload() + [
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
# Size_Format 2 also selects 4 streams; the payload cannot hold the jump
# table, so the real path fails closed on the jump table.
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "4-stream jump table")
```

</details>

#### rejects fresh-table single-stream direct-weight payloads with non-pinned literal bytes

- rejects fresh-table single-stream direct-weight payloads with non-pinned literal bytes
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fresh-table single-stream direct-weight payloads with non-pinned literal bytes")
val frame = _zstd_frame(4, _compressed_block([
    0x42u8, 0x80u8, 0x01u8,
    0x84u8, 0x43u8, 0x20u8, 0x10u8,
    0x80u8, 0x0Cu8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
# The final Huffman code over-runs the bitstream end (host zstd rejects
# it as Data corruption); the real path fails closed on the over-read.
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "bitstream bits")
```

</details>

#### rejects fresh-table single-stream direct-weight payloads with non-pinned regenerated size

- rejects fresh-table single-stream direct-weight payloads with non-pinned regenerated size
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fresh-table single-stream direct-weight payloads with non-pinned regenerated size")
val frame = _zstd_frame(5, _compressed_block([
    0x52u8, 0x80u8, 0x01u8
] + _exact_direct_weight_literals_payload() + [
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
# Decoding the inflated regenerated size over-runs the bitstream end
# (host zstd rejects it likewise); the real path fails closed.
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "bitstream bits")
```

</details>

#### rejects malformed fresh-table four-stream compressed literals with the 5-byte header form

- rejects malformed fresh-table four-stream compressed literals with the 5-byte header form
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed fresh-table four-stream compressed literals with the 5-byte header form")
val frame = _zstd_frame(4, _compressed_block(_unsupported_literals_payload(2, 3)))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
# The inline weights describe an invalid (>11-bit) Huffman tree; the real
# path fails closed when building the decode table.
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "huf tree depth exceeds 11 bits")
```

</details>

#### rejects sequence-bearing compressed blocks explicitly

- rejects sequence-bearing compressed blocks explicitly
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects sequence-bearing compressed blocks explicitly")
val frame = _zstd_frame(3, _compressed_block([
    0x18u8,
    0x61u8, 0x62u8, 0x63u8,
    0x01u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "sequence")
```

</details>

#### rejects treeless single-stream compressed literals without prior Huffman state

- rejects treeless single-stream compressed literals without prior Huffman state
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects treeless single-stream compressed literals without prior Huffman state")
val frame = _zstd_frame(4, _compressed_block([
    0x43u8, 0x80u8, 0x01u8,
    0x84u8, 0x43u8, 0x20u8, 0x10u8,
    0x80u8, 0x0Du8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

#### rejects treeless four-stream compressed literals without prior Huffman state

- rejects treeless four-stream compressed literals without prior Huffman state
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects treeless four-stream compressed literals without prior Huffman state")
val frame = _zstd_frame(4, _compressed_block([
    0x47u8, 0x80u8, 0x01u8,
    0x84u8, 0x43u8, 0x20u8, 0x10u8,
    0x80u8, 0x0Du8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

#### rejects treeless single-stream compressed literals with the 4-byte header form

- rejects treeless single-stream compressed literals with the 4-byte header form
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects treeless single-stream compressed literals with the 4-byte header form")
val frame = _zstd_frame(4, _compressed_block(_unsupported_literals_payload(3, 2)))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

#### rejects treeless four-stream compressed literals with the 5-byte header form

- rejects treeless four-stream compressed literals with the 5-byte header form
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects treeless four-stream compressed literals with the 5-byte header form")
val frame = _zstd_frame(4, _compressed_block(_unsupported_literals_payload(3, 3)))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "UnsupportedFeature", "treeless literals")
```

</details>

#### rejects the malformed FSE-compressed Huffman-weight fresh-table fixture

- rejects the malformed FSE-compressed Huffman-weight fresh-table fixture
   - Expected: decoded.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the malformed FSE-compressed Huffman-weight fresh-table fixture")
val frame = _zstd_frame(1, _compressed_block([
    0x12u8, 0x80u8, 0x00u8,
    0x01u8,
    0x01u8,
    0x00u8
]))
val decoded = zstd_decompress_frame(frame)
expect(decoded.is_err()).to_equal(true)
# The 1-byte FSE weight stream is too small for valid normalized counts;
# the real path fails closed while parsing the FSE table description.
_expect_compression_error(decoded.unwrap_err(), "TruncatedInput", "fse normalized counts")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_compressed_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd compressed blocks with zero sequences.
- zstd compressed blocks with zero sequences

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `f0dbb4fbf2c719c4f37354ac24182befc2eb4cdf56867d29cf903fbd21ef7a1a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0dbb4fbf2c719c4f37354ac24182befc2eb4cdf56867d29cf903fbd21ef7a1a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0dbb4fbf2c719c4f37354ac24182befc2eb4cdf56867d29cf903fbd21ef7a1a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/zstd_compressed_block_spec.spl
mirror: doc/06_spec/01_unit/lib/common/zstd_compressed_block_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/zstd_compressed_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/zstd_compressed_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/zstd_compressed_block_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes a compressed block containing raw literals and nbSeq == 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_compressed_block_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes a compressed block containing RLE literals and nbSeq == 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_compressed_block_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the host-rejected fresh-table single-stream direct-weight candidate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
