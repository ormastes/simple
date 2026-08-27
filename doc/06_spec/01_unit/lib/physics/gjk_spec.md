# Gjk Specification

> Tests covering GJK Collision Detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gjk Specification

## Scenarios

### GJK Collision Detection

#### detects sphere-sphere collision

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects sphere-sphere collision


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sphere-sphere collision")
val detector = GJKCollisionDetector.new()
val s1 = Sphere.new(cx=0.0, cy=0.0, cz=0.0, r=1.0)
val s2 = Sphere.new(cx=1.5, cy=0.0, cz=0.0, r=1.0)
check(detector.detect_sphere_sphere(s1=s1, s2=s2) == true)
```

</details>

#### detects box-box collision

- detects box-box collision


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects box-box collision")
val detector = GJKCollisionDetector.new()
val b1 = Box.new(cx=0.0, cy=0.0, cz=0.0, w=2.0, h=2.0, d=2.0)
val b2 = Box.new(cx=1.5, cy=0.0, cz=0.0, w=2.0, h=2.0, d=2.0)
check(detector.detect_box_box(b1=b1, b2=b2) == true)
```

</details>

#### detects convex hull collision

- detects convex hull collision


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects convex hull collision")
val detector = GJKCollisionDetector.new()
val s = Sphere.new(cx=0.0, cy=0.0, cz=0.0, r=1.0)
val b = Box.new(cx=1.5, cy=0.0, cz=0.0, w=2.0, h=2.0, d=2.0)
check(detector.detect_convex_collision(s1=s, b1=b) == true)
```

</details>

#### handles non-colliding shapes

- handles non-colliding shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles non-colliding shapes")
val detector = GJKCollisionDetector.new()
val s1 = Sphere.new(cx=0.0, cy=0.0, cz=0.0, r=1.0)
val s2 = Sphere.new(cx=10.0, cy=10.0, cz=10.0, r=1.0)
check(detector.detect_sphere_sphere(s1=s1, s2=s2) == false)
```

</details>

#### calculates penetration depth

- calculates penetration depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates penetration depth")
val detector = GJKCollisionDetector.new()
val s1 = Sphere.new(cx=0.0, cy=0.0, cz=0.0, r=1.0)
val s2 = Sphere.new(cx=1.0, cy=0.0, cz=0.0, r=1.0)
val penetration = detector.calculate_penetration(s1=s1, s2=s2)
check(penetration > 0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/physics/gjk_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GJK Collision Detection.
- GJK Collision Detection

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

- Canonical SPipe generation for source `6ce4febc2155b3ef5aed5691c521bcfabd0c2c82ec644105070dd121da5325ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ce4febc2155b3ef5aed5691c521bcfabd0c2c82ec644105070dd121da5325ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ce4febc2155b3ef5aed5691c521bcfabd0c2c82ec644105070dd121da5325ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/physics/gjk_spec.spl
mirror: doc/06_spec/01_unit/lib/physics/gjk_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/physics/gjk_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/physics/gjk_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/physics/gjk_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects sphere-sphere collision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/physics/gjk_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects box-box collision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/physics/gjk_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects convex hull collision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
