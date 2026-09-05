# Zstd Msb Bits Bounds Specification

> Tests covering Zstd MSB bit reader bounds validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Msb Bits Bounds Specification

## Scenarios

### Zstd MSB bit reader bounds validation

#### rejects non-eof states before the start before padding

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects non-eof states before the start before padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-eof states before the start before padding")
var data: [u8] = [0x80u8]
val state = ZstdMsbBackwardBits(
    data: data,
    start: 1,
    byte_idx: 0,
    next_bit: 7,
    eof: false
)
val decoded = zstd_msb_bits_read(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("msb bitstream range"))
    _:
        check(false)
```

</details>

#### rejects malformed read state before indexing

- rejects malformed read state before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed read state before indexing")
var data: [u8] = [0x80u8]
val state = ZstdMsbBackwardBits(
    data: data,
    start: 0,
    byte_idx: 4,
    next_bit: 7,
    eof: false
)
val decoded = zstd_msb_bits_read(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        check(message.contains("msb bitstream bits"))
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
val state = ZstdMsbBackwardBits(
    data: data,
    start: 0,
    byte_idx: 4,
    next_bit: 7,
    eof: false
)
check(zstd_msb_bits_remaining(state) == 0)
```

</details>

#### rejects negative bit index before shifting

- rejects negative bit index before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative bit index before shifting")
var data: [u8] = [0x80u8]
val state = ZstdMsbBackwardBits(
    data: data,
    start: 0,
    byte_idx: 0,
    next_bit: -1,
    eof: false
)
val decoded = zstd_msb_bits_read(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("bit index"))
    _:
        check(false)
```

</details>

#### rejects oversized bit index before shifting

- rejects oversized bit index before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized bit index before shifting")
var data: [u8] = [0x80u8]
val state = ZstdMsbBackwardBits(
    data: data,
    start: 0,
    byte_idx: 0,
    next_bit: 8,
    eof: false
)
val decoded = zstd_msb_bits_read(state, 1)
check(decoded.is_err())
val err = decoded.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("bit index"))
    _:
        check(false)
```

</details>

#### does not count malformed bit indexes

- does not count malformed bit indexes


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not count malformed bit indexes")
var data: [u8] = [0x80u8]
val negative = ZstdMsbBackwardBits(
    data: data,
    start: 0,
    byte_idx: 0,
    next_bit: -1,
    eof: false
)
val oversized = ZstdMsbBackwardBits(
    data: data,
    start: 0,
    byte_idx: 0,
    next_bit: 8,
    eof: false
)
check(zstd_msb_bits_remaining(negative) == 0)
check(zstd_msb_bits_remaining(oversized) == 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Zstd MSB bit reader bounds validation.
- Zstd MSB bit reader bounds validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `4bfeded75516b2eca5cc37aa1e4b1d295f40487ed31d8b5f8a7fd17465e5adcf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4bfeded75516b2eca5cc37aa1e4b1d295f40487ed31d8b5f8a7fd17465e5adcf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4bfeded75516b2eca5cc37aa1e4b1d295f40487ed31d8b5f8a7fd17465e5adcf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-eof states before the start before padding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed read state before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not count bytes beyond the backing buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
