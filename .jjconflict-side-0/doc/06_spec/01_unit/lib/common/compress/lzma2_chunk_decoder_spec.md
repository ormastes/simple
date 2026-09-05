# Lzma2 Chunk Decoder Specification

> Tests covering LZMA2 chunk decoder validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lzma2 Chunk Decoder Specification

## Scenarios

### LZMA2 chunk decoder validation

#### rejects negative chunk control offsets before indexing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative chunk control offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative chunk control offsets before indexing")
var input: [u8] = [0x00u8]
val decoded = _parse_lzma2_chunk_header(input, -1, Lzma2ChunkState(need_dict_reset: true, need_props: true))
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("lzma2 control"))
    _:
        check(false)
```

</details>

#### rejects negative chunk header offsets before indexing

- rejects negative chunk header offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative chunk header offsets before indexing")
var input: [u8] = [0x00u8, 0x01u8]
val decoded = _read_u16_be_chunk(input, -1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("need 2 bytes"))
    _:
        check(false)
```

</details>

#### rejects truncated legacy range decoder bodies

- rejects truncated legacy range decoder bodies


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated legacy range decoder bodies")
var input: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x00u8]
val decoded = _lzma_decode_chunk_3_0_2(input, 0, input.len(), 1, [], fresh_state(), _lzma_init_probs(LZMA_PROBS_TOTAL), true)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("range decoder init"))
    _:
        check(false)
```

</details>

#### rejects truncated parameterized range decoder bodies

- rejects truncated parameterized range decoder bodies


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated parameterized range decoder bodies")
var input: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x00u8]
val props = LzmaProperties(lc: 3, lp: 0, pb: 2)
val decoded = _lzma_decode_chunk(input, 0, input.len(), 1, [], fresh_state(), [], true, props)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("range decoder init"))
    _:
        check(false)
```

</details>

#### rejects negative declared legacy chunk output sizes

- rejects negative declared legacy chunk output sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative declared legacy chunk output sizes")
var input: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val decoded = _lzma_decode_chunk_3_0_2(input, 0, input.len(), -1, [], fresh_state(), _lzma_init_probs(LZMA_PROBS_TOTAL), true)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("chunk size"))
    _:
        check(false)
```

</details>

#### rejects negative declared parameterized chunk output sizes

- rejects negative declared parameterized chunk output sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative declared parameterized chunk output sizes")
var input: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val props = LzmaProperties(lc: 3, lp: 0, pb: 2)
val decoded = _lzma_decode_chunk(input, 0, input.len(), -1, [], fresh_state(), [], true, props)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("chunk size"))
    _:
        check(false)
```

</details>

#### rejects invalid parameterized LZMA properties before shift-derived indexes

- rejects invalid parameterized LZMA properties before shift-derived indexes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid parameterized LZMA properties before shift-derived indexes")
var input: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val props = LzmaProperties(lc: 3, lp: 0, pb: -1)
val decoded = _lzma_decode_chunk(input, 0, input.len(), 1, [], fresh_state(), [], true, props)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("properties"))
    _:
        check(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/lzma2_chunk_decoder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LZMA2 chunk decoder validation.
- LZMA2 chunk decoder validation

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

- Canonical SPipe generation for source `00e8b9576b030e406786664b094b30fed7ce3c7df8fe54fc0d65ef0e4c835d15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00e8b9576b030e406786664b094b30fed7ce3c7df8fe54fc0d65ef0e4c835d15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00e8b9576b030e406786664b094b30fed7ce3c7df8fe54fc0d65ef0e4c835d15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/lzma2_chunk_decoder_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/lzma2_chunk_decoder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/lzma2_chunk_decoder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/lzma2_chunk_decoder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/lzma2_chunk_decoder_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative chunk control offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/lzma2_chunk_decoder_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative chunk header offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/lzma2_chunk_decoder_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects truncated legacy range decoder bodies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
