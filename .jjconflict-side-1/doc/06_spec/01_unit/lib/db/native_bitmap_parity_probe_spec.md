# Native Bitmap Parity Probe Specification

> Tests covering native bitmap parity probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Bitmap Parity Probe Specification

## Scenarios

### native bitmap parity probe

#### counts intersection bits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- counts intersection bits
   - Expected: both.count() equals `4`
   - Expected: either.count() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts intersection bits")
val lhs = build_lhs_bitmap()
val rhs = build_rhs_bitmap()
val both = lhs.and_with(rhs)
val either = lhs.or_with(rhs)

expect(both.count()).to_equal(4)
expect(either.count()).to_equal(7)
```

</details>

#### reads intersection bit 0

- reads intersection bit 0
   - Expected: both.get(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads intersection bit 0")
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(0)).to_equal(true)
```

</details>

#### reads intersection bit 31

- reads intersection bit 31
   - Expected: both.get(31) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads intersection bit 31")
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(31)).to_equal(false)
```

</details>

#### reads intersection bit 32

- reads intersection bit 32
   - Expected: both.get(32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads intersection bit 32")
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(32)).to_equal(true)
```

</details>

#### reads intersection bit 62

- reads intersection bit 62
   - Expected: both.get(62) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads intersection bit 62")
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(62)).to_equal(false)
```

</details>

#### reads intersection bit 63

- reads intersection bit 63
   - Expected: both.get(63) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads intersection bit 63")
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(63)).to_equal(true)
```

</details>

#### reads intersection bit 64

- reads intersection bit 64
   - Expected: both.get(64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads intersection bit 64")
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(64)).to_equal(true)
```

</details>

#### reads intersection bit 95

- reads intersection bit 95
   - Expected: both.get(95) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads intersection bit 95")
val both = build_lhs_bitmap().and_with(build_rhs_bitmap())
expect(both.get(95)).to_equal(false)
```

</details>

#### reads union bit 0

- reads union bit 0
   - Expected: either.get(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads union bit 0")
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(0)).to_equal(true)
```

</details>

#### reads union bit 31

- reads union bit 31
   - Expected: either.get(31) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads union bit 31")
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(31)).to_equal(true)
```

</details>

#### reads union bit 32

- reads union bit 32
   - Expected: either.get(32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads union bit 32")
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(32)).to_equal(true)
```

</details>

#### reads union bit 62

- reads union bit 62
   - Expected: either.get(62) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads union bit 62")
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(62)).to_equal(true)
```

</details>

#### reads union bit 63

- reads union bit 63
   - Expected: either.get(63) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads union bit 63")
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(63)).to_equal(true)
```

</details>

#### reads union bit 64

- reads union bit 64
   - Expected: either.get(64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads union bit 64")
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(64)).to_equal(true)
```

</details>

#### reads union bit 95

- reads union bit 95
   - Expected: either.get(95) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads union bit 95")
val either = build_lhs_bitmap().or_with(build_rhs_bitmap())
expect(either.get(95)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/native_bitmap_parity_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native bitmap parity probe.
- native bitmap parity probe

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6624c0aa178fc96762706b1272f75ca4d22505e5c1d2459d835cbda4d5b59862`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6624c0aa178fc96762706b1272f75ca4d22505e5c1d2459d835cbda4d5b59862`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6624c0aa178fc96762706b1272f75ca4d22505e5c1d2459d835cbda4d5b59862`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/db/native_bitmap_parity_probe_spec.spl
mirror: doc/06_spec/01_unit/lib/db/native_bitmap_parity_probe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/db/native_bitmap_parity_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/db/native_bitmap_parity_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/db/native_bitmap_parity_probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/db/native_bitmap_parity_probe_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts intersection bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/db/native_bitmap_parity_probe_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads intersection bit 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/db/native_bitmap_parity_probe_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads intersection bit 31' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
