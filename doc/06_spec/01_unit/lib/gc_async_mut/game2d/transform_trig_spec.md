# Transform Trig Specification

> Tests covering Transform2D rotation matrix uses real trig.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transform Trig Specification

## Scenarios

### Transform2D rotation matrix uses real trig

#### identity rotation gives cos=1, sin=0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- identity rotation gives cos=1, sin=0
   - Expected: approx(m[0], 1.0) is true
   - Expected: approx(m[3], 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identity rotation gives cos=1, sin=0")
val t = Transform2D.create_full(0.0, 0.0, 0.0, 1.0, 1.0)
val m = t.world_matrix()
expect(approx(m[0], 1.0)).to_equal(true)
expect(approx(m[3], 0.0)).to_equal(true)
```

</details>

#### quarter turn gives cos=0, sin=1

- quarter turn gives cos=0, sin=1
   - Expected: approx(m[0], 0.0) is true
   - Expected: approx(m[3], 1.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quarter turn gives cos=0, sin=1")
val t = Transform2D.create_full(0.0, 0.0, 1.5707963267948966, 1.0, 1.0)
val m = t.world_matrix()
expect(approx(m[0], 0.0)).to_equal(true)
expect(approx(m[3], 1.0)).to_equal(true)
```

</details>

#### half turn gives cos=-1, sin=0

- half turn gives cos=-1, sin=0
   - Expected: approx(m[0], -1.0) is true
   - Expected: approx(m[3], 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("half turn gives cos=-1, sin=0")
val t = Transform2D.create_full(0.0, 0.0, 3.141592653589793, 1.0, 1.0)
val m = t.world_matrix()
expect(approx(m[0], -1.0)).to_equal(true)
expect(approx(m[3], 0.0)).to_equal(true)
```

</details>

#### rotation is not a constant — two distinct angles differ

- rotation is not a constant — two distinct angles differ
   - Expected: approx(ma[0], mb[0]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotation is not a constant — two distinct angles differ")
val a = Transform2D.create_full(0.0, 0.0, 0.0, 1.0, 1.0)
val b = Transform2D.create_full(0.0, 0.0, 1.5707963267948966, 1.0, 1.0)
val ma = a.world_matrix()
val mb = b.world_matrix()
# A silent nil/0 extern makes every angle produce the same matrix.
expect(approx(ma[0], mb[0])).to_equal(false)
```

</details>

#### rotation preserves length (cos^2 + sin^2 == 1)

- rotation preserves length (cos^2 + sin^2 == 1)
   - Expected: approx(c * c + s * s, 1.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotation preserves length (cos^2 + sin^2 == 1)")
val t = Transform2D.create_full(0.0, 0.0, 0.7853981633974483, 1.0, 1.0)
val m = t.world_matrix()
val c = m[0]
val s = m[3]
expect(approx(c * c + s * s, 1.0)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Transform2D rotation matrix uses real trig.
- Transform2D rotation matrix uses real trig

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

- Canonical SPipe generation for source `290d9146f5a59c95e8ed500d2fa9990e5b4b81106f34018d1d65446cde2aa9ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `290d9146f5a59c95e8ed500d2fa9990e5b4b81106f34018d1d65446cde2aa9ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `290d9146f5a59c95e8ed500d2fa9990e5b4b81106f34018d1d65446cde2aa9ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identity rotation gives cos=1, sin=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'quarter turn gives cos=0, sin=1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'half turn gives cos=-1, sin=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
