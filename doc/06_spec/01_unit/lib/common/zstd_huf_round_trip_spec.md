# Zstd Huf Round Trip Specification

> Tests covering zstd huf encoder round-trips the existing decoder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Huf Round Trip Specification

## Scenarios

### zstd huf encoder round-trips the existing decoder

#### round-trips a one-symbol stream via the bounded synthetic tree

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a one-symbol stream via the bounded synthetic tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a one-symbol stream via the bounded synthetic tree")
val literals: [u8] = [
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8,
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8,
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8
]
_round_trip(literals)
```

</details>

#### round-trips a two-symbol stream

- round-trips a two-symbol stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a two-symbol stream")
val literals: [u8] = [
    0x41u8, 0x42u8, 0x41u8, 0x41u8,
    0x42u8, 0x42u8, 0x41u8, 0x42u8
]
_round_trip(literals)
```

</details>

#### round-trips a 4-symbol mixed-length input

- round-trips a 4-symbol mixed-length input


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a 4-symbol mixed-length input")
# 'a' x 6, 'b' x 3, 'c' x 2, 'd' x 1 — same shape as the
# existing structural test in zstd_fse_huffman_weight_encode_spec
# (known to encode cleanly through `_zstd_huf_assign_weights`).
# Three distinct code lengths exercise cross-byte packing.
# (The original W13-B 2-symbol probe was blocked by the
# weight balancer rejecting alphabet size 2 — a separate,
# out-of-scope encoder issue.)
val literals: [u8] = [
    0x61u8, 0x62u8, 0x61u8, 0x63u8, 0x61u8, 0x62u8,
    0x61u8, 0x63u8, 0x61u8, 0x62u8, 0x61u8, 0x64u8
]
_round_trip(literals)
```

</details>

#### round-trips a skewed 'a*8 b*4 c*2 d*1' mixed-length input

- round-trips a skewed 'a*8 b*4 c*2 d*1' mixed-length input


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a skewed 'a*8 b*4 c*2 d*1' mixed-length input")
# The W13-B probe showed this input decoded as 'a*9 ...'
# because the encoder's byte layout misaligned bit positions
# across byte boundaries. Mixed-length codes (1/2/3 bits)
# exercise the cross-byte packing path.
val literals: [u8] = [
    0x61u8, 0x61u8, 0x61u8, 0x61u8,
    0x61u8, 0x61u8, 0x61u8, 0x61u8,
    0x62u8, 0x62u8, 0x62u8, 0x62u8,
    0x63u8, 0x63u8,
    0x64u8
]
_round_trip(literals)
```

</details>

#### round-trips a highly skewed 'A*16 B*4 C*2 D*1' input

- round-trips a highly skewed 'A*16 B*4 C*2 D*1' input


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a highly skewed 'A*16 B*4 C*2 D*1' input")
# Larger run of the most-frequent symbol forces the bit stream
# well past one byte; W13-B saw `byte[16] got=65 want=66`.
val literals: [u8] = [
    0x41u8, 0x41u8, 0x41u8, 0x41u8,
    0x41u8, 0x41u8, 0x41u8, 0x41u8,
    0x41u8, 0x41u8, 0x41u8, 0x41u8,
    0x41u8, 0x41u8, 0x41u8, 0x41u8,
    0x42u8, 0x42u8, 0x42u8, 0x42u8,
    0x43u8, 0x43u8,
    0x44u8
]
_round_trip(literals)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_huf_round_trip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd huf encoder round-trips the existing decoder.
- zstd huf encoder round-trips the existing decoder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `f210b3397d6853b9857451537ed109bba85a79d781448c9750bf19085888cb70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f210b3397d6853b9857451537ed109bba85a79d781448c9750bf19085888cb70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f210b3397d6853b9857451537ed109bba85a79d781448c9750bf19085888cb70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/zstd_huf_round_trip_spec.spl
mirror: doc/06_spec/01_unit/lib/common/zstd_huf_round_trip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/zstd_huf_round_trip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/zstd_huf_round_trip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/zstd_huf_round_trip_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a one-symbol stream via the bounded synthetic tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_huf_round_trip_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a two-symbol stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_huf_round_trip_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a 4-symbol mixed-length input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
