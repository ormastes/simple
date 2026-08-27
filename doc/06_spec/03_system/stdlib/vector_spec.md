# Vector Specification

> Tests covering SkPoint — zero, SkPoint — distance_to, SkRect — contains_point, SkRect — center, PathPoint — linear, Matrix3x3 — identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Specification

## Scenarios

### SkPoint — zero

#### zero point has x equals 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- zero point has x equals 0
   - Expected: p.x > -0.01 is true
   - Expected: p.x < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zero point has x equals 0")
val p = SkPoint.zero()
expect(p.x > -0.01).to_equal(true)
expect(p.x < 0.01).to_equal(true)
```

</details>

#### zero point has y equals 0

- zero point has y equals 0
   - Expected: p.y > -0.01 is true
   - Expected: p.y < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zero point has y equals 0")
val p = SkPoint.zero()
expect(p.y > -0.01).to_equal(true)
expect(p.y < 0.01).to_equal(true)
```

</details>

### SkPoint — distance_to

#### distance between known points

- distance between known points
   - Expected: d > 4.99 is true
   - Expected: d < 5.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("distance between known points")
val a = SkPoint(x: 0.0, y: 0.0)
val b = SkPoint(x: 3.0, y: 4.0)
val d = a.distance_to(b)
expect(d > 4.99).to_equal(true)
expect(d < 5.01).to_equal(true)
```

</details>

### SkRect — contains_point

#### inside point returns true

- inside point returns true
   - Expected: r.contains_point(5.0, 5.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inside point returns true")
val r = SkRect.from_xywh(0.0, 0.0, 10.0, 10.0)
expect(r.contains_point(5.0, 5.0)).to_equal(true)
```

</details>

#### outside point returns false

- outside point returns false
   - Expected: r.contains_point(15.0, 5.0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("outside point returns false")
val r = SkRect.from_xywh(0.0, 0.0, 10.0, 10.0)
expect(r.contains_point(15.0, 5.0)).to_equal(false)
```

</details>

### SkRect — center

#### center of rect is correct

- center of rect is correct
   - Expected: c.x > 4.99 is true
   - Expected: c.x < 5.01 is true
   - Expected: c.y > 9.99 is true
   - Expected: c.y < 10.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("center of rect is correct")
val r = SkRect.from_xywh(0.0, 0.0, 10.0, 20.0)
val c = r.center()
expect(c.x > 4.99).to_equal(true)
expect(c.x < 5.01).to_equal(true)
expect(c.y > 9.99).to_equal(true)
expect(c.y < 10.01).to_equal(true)
```

</details>

### PathPoint — linear

#### linear point has_controls is false

- linear point has_controls is false
   - Expected: pp.has_controls is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("linear point has_controls is false")
val pos = SkPoint(x: 1.0, y: 2.0)
val pp = PathPoint.linear(pos)
expect(pp.has_controls).to_equal(false)
```

</details>

### Matrix3x3 — identity

#### identity diagonal is 1.0

- identity diagonal is 1.0
   - Expected: m.m00 > 0.99 is true
   - Expected: m.m00 < 1.01 is true
   - Expected: m.m11 > 0.99 is true
   - Expected: m.m11 < 1.01 is true
   - Expected: m.m22 > 0.99 is true
   - Expected: m.m22 < 1.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity diagonal is 1.0")
val m = Matrix3x3.identity()
expect(m.m00 > 0.99).to_equal(true)
expect(m.m00 < 1.01).to_equal(true)
expect(m.m11 > 0.99).to_equal(true)
expect(m.m11 < 1.01).to_equal(true)
expect(m.m22 > 0.99).to_equal(true)
expect(m.m22 < 1.01).to_equal(true)
```

</details>

#### identity off-diagonal is 0.0

- identity off-diagonal is 0.0
   - Expected: m.m01 > -0.01 is true
   - Expected: m.m01 < 0.01 is true
   - Expected: m.m10 > -0.01 is true
   - Expected: m.m10 < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity off-diagonal is 0.0")
val m = Matrix3x3.identity()
expect(m.m01 > -0.01).to_equal(true)
expect(m.m01 < 0.01).to_equal(true)
expect(m.m10 > -0.01).to_equal(true)
expect(m.m10 < 0.01).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/vector_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SkPoint — zero, SkPoint — distance_to, SkRect — contains_point, SkRect — center, PathPoint — linear, Matrix3x3 — identity.
- SkPoint — zero
- SkPoint — distance_to
- SkRect — contains_point
- SkRect — center
- PathPoint — linear
- Matrix3x3 — identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1946c53780ffdfd1d471afb45cf50c969e64dda44ae3136820bb8bcaca6d8608`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1946c53780ffdfd1d471afb45cf50c969e64dda44ae3136820bb8bcaca6d8608`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1946c53780ffdfd1d471afb45cf50c969e64dda44ae3136820bb8bcaca6d8608`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/stdlib/vector_spec.spl
mirror: doc/06_spec/03_system/stdlib/vector_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/vector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/vector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/vector_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero point has x equals 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/vector_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero point has y equals 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/vector_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distance between known points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
