# Zstd Bits Bounds Specification

> Tests covering Zstd bit reader bounds validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Bits Bounds Specification

## Scenarios

### Zstd bit reader bounds validation

#### rejects starts beyond the backing buffer before trusting reservoir bits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects starts beyond the backing buffer before trusting reservoir bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects starts beyond the backing buffer before trusting reservoir bits")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: 2,
    byte_pos: 1,
    reservoir: 1u64,
    bits_in_reservoir: 1
)
val decoded = zstd_bits_peek(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("bitstream range"))
    _:
        check(false)
```

</details>

#### does not report remaining bits for starts beyond the backing buffer

- does not report remaining bits for starts beyond the backing buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not report remaining bits for starts beyond the backing buffer")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: 2,
    byte_pos: 1,
    reservoir: 1u64,
    bits_in_reservoir: 1
)
check(zstd_bits_remaining(state) == 0)
```

</details>

#### rejects negative refill starts before indexing

- rejects negative refill starts before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative refill starts before indexing")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: -2,
    byte_pos: -1,
    reservoir: 0u64,
    bits_in_reservoir: 0
)
val decoded = zstd_bits_peek(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("bitstream range"))
    _:
        check(false)
```

</details>

#### does not count bytes from negative refill starts

- does not count bytes from negative refill starts


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not count bytes from negative refill starts")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: -2,
    byte_pos: -1,
    reservoir: 0u64,
    bits_in_reservoir: 0
)
check(zstd_bits_remaining(state) == 0)
```

</details>

#### rejects malformed refill state before indexing

- rejects malformed refill state before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed refill state before indexing")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: 0,
    byte_pos: 4,
    reservoir: 0u64,
    bits_in_reservoir: 0
)
val decoded = zstd_bits_peek(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("bitstream bits"))
    _:
        check(false)
```

</details>

#### does not count bytes beyond the backing buffer

- does not count bytes beyond the backing buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not count bytes beyond the backing buffer")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: 0,
    byte_pos: 4,
    reservoir: 0u64,
    bits_in_reservoir: 3
)
check(zstd_bits_remaining(state) == 3)
```

</details>

#### rejects negative reservoir width before shifting

- rejects negative reservoir width before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative reservoir width before shifting")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: 0,
    byte_pos: 0,
    reservoir: 0u64,
    bits_in_reservoir: -1
)
val decoded = zstd_bits_peek(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("reservoir"))
    _:
        check(false)
```

</details>

#### does not report negative remaining bits

- does not report negative remaining bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not report negative remaining bits")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: 0,
    byte_pos: 0,
    reservoir: 0u64,
    bits_in_reservoir: -1
)
check(zstd_bits_remaining(state) == 0)
```

</details>

#### rejects oversized reservoir width before use

- rejects oversized reservoir width before use


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized reservoir width before use")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: 0,
    byte_pos: 0,
    reservoir: 0u64,
    bits_in_reservoir: 65
)
val decoded = zstd_bits_peek(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("reservoir"))
    _:
        check(false)
```

</details>

#### does not report oversized remaining bits

- does not report oversized remaining bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not report oversized remaining bits")
var data: [u8] = [0x80u8]
val state = ZstdBackwardBits(
    data: data,
    start: 0,
    byte_pos: 0,
    reservoir: 0u64,
    bits_in_reservoir: 65
)
check(zstd_bits_remaining(state) == 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/zstd_bits_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Zstd bit reader bounds validation.
- Zstd bit reader bounds validation

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

- Canonical SPipe generation for source `ab4096e3b6219498c5ed687b410010fd77532790b4542eadc2bd30b1102332a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab4096e3b6219498c5ed687b410010fd77532790b4542eadc2bd30b1102332a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab4096e3b6219498c5ed687b410010fd77532790b4542eadc2bd30b1102332a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/zstd_bits_bounds_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/zstd_bits_bounds_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/zstd_bits_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/zstd_bits_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/zstd_bits_bounds_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects starts beyond the backing buffer before trusting reservoir bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_bits_bounds_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not report remaining bits for starts beyond the backing buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_bits_bounds_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative refill starts before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
