# Zstd Sequence Parser Bounds Specification

> Tests covering Zstd sequence parser bounds validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Sequence Parser Bounds Specification

## Scenarios

### Zstd sequence parser bounds validation

#### rejects negative sequence count offsets before indexing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative sequence count offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative sequence count offsets before indexing")
val decoded = _zstd_parse_sequence_count([0x00u8], -1, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd sequences header"))
    _:
        check(false)
```

</details>

#### rejects sequence count ends beyond the backing input before indexing

- rejects sequence count ends beyond the backing input before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects sequence count ends beyond the backing input before indexing")
val decoded = _zstd_parse_sequence_count([0x80u8], 0, 2)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd sequences header"))
    _:
        check(false)
```

</details>

#### rejects negative sequence mode offsets before indexing

- rejects negative sequence mode offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative sequence mode offsets before indexing")
val decoded = _zstd_parse_sequence_modes([0x00u8], -1, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd sequence modes"))
    _:
        check(false)
```

</details>

#### rejects sequence mode ends beyond the backing input before indexing

- rejects sequence mode ends beyond the backing input before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects sequence mode ends beyond the backing input before indexing")
val decoded = _zstd_parse_sequence_modes([0x00u8], 0, 2)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd sequence modes"))
    _:
        check(false)
```

</details>

#### rejects negative rle sequence table offsets before indexing

- rejects negative rle sequence table offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative rle sequence table offsets before indexing")
val modes = ZstdSequenceModes(literals_length_mode: 1, offsets_mode: 1, match_length_mode: 1, bytes_used: 1)
val decoded = _zstd_parse_rle_sequence_tables([0x00u8, 0x00u8, 0x00u8], -1, 3, modes)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd rle sequence tables"))
    _:
        check(false)
```

</details>

#### rejects rle sequence table ends beyond the backing input before indexing

- rejects rle sequence table ends beyond the backing input before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects rle sequence table ends beyond the backing input before indexing")
val modes = ZstdSequenceModes(literals_length_mode: 1, offsets_mode: 1, match_length_mode: 1, bytes_used: 1)
val decoded = _zstd_parse_rle_sequence_tables([0x00u8, 0x00u8, 0x00u8], 0, 4, modes)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd rle sequence tables"))
    _:
        check(false)
```

</details>

#### rejects negative single sequence table offsets before indexing

- rejects negative single sequence table offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative single sequence table offsets before indexing")
val previous = ZstdFseDecodeTable(table_log: 0, entries: [])
val decoded = _zstd_parse_single_sequence_table([0x00u8], -1, 1, 1, 6, [1], previous)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd rle sequence table"))
    _:
        check(false)
```

</details>

#### rejects single sequence table ends beyond the backing input before indexing

- rejects single sequence table ends beyond the backing input before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects single sequence table ends beyond the backing input before indexing")
val previous = ZstdFseDecodeTable(table_log: 0, entries: [])
val decoded = _zstd_parse_single_sequence_table([0x00u8], 0, 2, 1, 6, [1], previous)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("zstd rle sequence table"))
    _:
        check(false)
```

</details>

#### rejects negative fse sequence counts before reading state tables

- rejects negative fse sequence counts before reading state tables


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative fse sequence counts before reading state tables")
val tables = ZstdSequenceTables(
    literal_lengths_mode: 1,
    literal_lengths_rle: Some(0),
    literal_lengths: nil,
    offsets_mode: 1,
    offsets_rle: Some(0),
    offsets: nil,
    match_lengths_mode: 1,
    match_lengths_rle: Some(0),
    match_lengths: nil,
    bytes_used: 0
)
val decoded = _zstd_decode_fse_sequences([0x01u8], 0, 1, -1, tables)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("negative sequence count"))
    _:
        check(false)
```

</details>

#### rejects negative rle sequence counts before reading bitstreams

- rejects negative rle sequence counts before reading bitstreams


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative rle sequence counts before reading bitstreams")
val tables = ZstdRleSequenceTables(
    literal_length_code: 0,
    offset_code: 0,
    match_length_code: 0,
    bytes_used: 0
)
val decoded = _zstd_decode_rle_sequences([0x01u8], 0, 1, -1, tables)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("negative sequence count"))
    _:
        check(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Zstd sequence parser bounds validation.
- Zstd sequence parser bounds validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `36fd20be98864319938764a9d9e0540f787593892edce540c8b1e30ffe806e7d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36fd20be98864319938764a9d9e0540f787593892edce540c8b1e30ffe806e7d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36fd20be98864319938764a9d9e0540f787593892edce540c8b1e30ffe806e7d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative sequence count offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects sequence count ends beyond the backing input before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative sequence mode offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
