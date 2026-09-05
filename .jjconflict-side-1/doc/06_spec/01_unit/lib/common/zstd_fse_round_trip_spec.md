# Zstd Fse Round Trip Specification

> Tests covering zstd fse encoder round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Fse Round Trip Specification

## Scenarios

### zstd fse encoder round-trip

#### round-trips a tiny three-symbol alphabet

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a tiny three-symbol alphabet
   - Expected: out_res.is_err() is false
   - Expected: out_res.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a tiny three-symbol alphabet")
# table_size = 32 (table_log=5). counts sum to 32.
val counts = [12, 12, 8]
val input = [0, 1, 2, 1, 0, 2, 1, 0]
val out_res = _round_trip(5, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

#### round-trips a small symbol stream with a less-than-one symbol

- round-trips a small symbol stream with a less-than-one symbol
   - Expected: out_res.is_err() is false
   - Expected: out_res.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a small symbol stream with a less-than-one symbol")
# Symbol 2 has probability 1/32 (count == -1) so it occupies a
# high slot; symbols 0 and 1 share the body of the table.
# 15 + 16 + |-1| = 32 = table_size.
val counts = [15, 16, -1]
val input = [0, 1, 0, 1, 2, 0, 1, 0, 1]
val out_res = _round_trip(5, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

#### round-trips a longer mixed sequence

- round-trips a longer mixed sequence
   - Expected: out_res.is_err() is false
   - Expected: out_res.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a longer mixed sequence")
val counts = [10, 10, 6, 6]
val input = [
    0, 1, 2, 3, 0, 1, 2, 3,
    0, 0, 1, 1, 2, 3, 0, 1,
    2, 3, 0, 1, 2, 3, 0, 1
]
val out_res = _round_trip(5, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

#### round-trips at table_log = 6

- round-trips at table_log = 6
   - Expected: out_res.is_err() is false
   - Expected: out_res.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips at table_log = 6")
# 64-slot table; mix of high and low probabilities.
# 20+14+10+8+6+4+1+1 = 64 (last two are |-1|=1 each).
val counts = [20, 14, 10, 8, 6, 4, -1, -1]
val input = [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6]
val out_res = _round_trip(6, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

#### round-trips a single-symbol-dominant stream

- round-trips a single-symbol-dominant stream
   - Expected: out_res.is_err() is false
   - Expected: out_res.unwrap() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a single-symbol-dominant stream")
# One dominant symbol with all the mass except a single low-prob.
val counts = [30, -1, -1]
val input = [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]
val out_res = _round_trip(5, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_fse_round_trip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd fse encoder round-trip.
- zstd fse encoder round-trip

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

- Canonical SPipe generation for source `ad1610a02bc8985d9b5b9be3b02851ca19cc85cf92df818573f93b0c8cc92f11`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad1610a02bc8985d9b5b9be3b02851ca19cc85cf92df818573f93b0c8cc92f11`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad1610a02bc8985d9b5b9be3b02851ca19cc85cf92df818573f93b0c8cc92f11`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/zstd_fse_round_trip_spec.spl
mirror: doc/06_spec/01_unit/lib/common/zstd_fse_round_trip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/zstd_fse_round_trip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/zstd_fse_round_trip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/zstd_fse_round_trip_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a tiny three-symbol alphabet' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_fse_round_trip_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a small symbol stream with a less-than-one symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/zstd_fse_round_trip_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a longer mixed sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
