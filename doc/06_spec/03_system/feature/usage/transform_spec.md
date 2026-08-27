# Transform Specification

> Purpose: creates identity transform

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transform Specification

Purpose: creates identity transform

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-004 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/transform_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: creates identity transform
Audience: compiler and tooling engineers who maintain this spec

# Transform Specification

**Feature IDs:** #MATH-004
**Category:** Stdlib
**Difficulty:** 3/5
**Status:** Implemented

## Overview
Transform (f32) and Transformd (f64) combining position, rotation, and scale.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Transform | Position + rotation + scale |
| Composition | Parent-child transform combining |
| to_mat4 | Convert to 4x4 matrix |

## Behavior
- Identity transform: origin, no rotation, unit scale
- Compose transforms for hierarchy
- Convert to matrix for GPU upload
- SLERP-based interpolation

## Scenarios

### Transform Construction

#### creates identity transform

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates identity transform
- Verify: creates identity transform
   - Expected: t.position.is_zero() is true
   - Expected: t.rotation.w equals `1.0`
   - Expected: t.scale.x equals `1.0`
   - Expected: t.scale.y equals `1.0`
   - Expected: t.scale.z equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates identity transform")
step("Verify: creates identity transform")
# @req: REQ-FEATURE-Tran-001
val t = Transform.identity()
expect(t.position.is_zero()).to_equal(true)
expect(t.rotation.w).to_equal(1.0)
expect(t.scale.x).to_equal(1.0)
expect(t.scale.y).to_equal(1.0)
expect(t.scale.z).to_equal(1.0)
```

</details>

#### converts to mat4

- converts to mat4
- Verify: converts to mat4
   - Expected: m.data[0] equals `1.0`
   - Expected: m.data[5] equals `1.0`
   - Expected: m.data[10] equals `1.0`
   - Expected: m.data[15] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts to mat4")
step("Verify: converts to mat4")
# @req: REQ-FEATURE-Tran-001
val t = Transform.identity()
val m = t.to_mat4()
expect(m.data[0]).to_equal(1.0)
expect(m.data[5]).to_equal(1.0)
expect(m.data[10]).to_equal(1.0)
expect(m.data[15]).to_equal(1.0)
```

</details>

### Transform Direction Vectors

#### identity forward is +Z

- identity forward is +Z
- Verify: identity forward is +Z
   - Expected: fwd.z equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity forward is +Z")
step("Verify: identity forward is +Z")
# @req: REQ-FEATURE-Tran-001
val t = Transform.identity()
val fwd = t.forward()
expect(fwd.z).to_equal(1.0)
```

</details>

#### identity right is +X

- identity right is +X
- Verify: identity right is +X
   - Expected: r.x equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity right is +X")
step("Verify: identity right is +X")
# @req: REQ-FEATURE-Tran-001
val t = Transform.identity()
val r = t.right()
expect(r.x).to_equal(1.0)
```

</details>

#### identity up is +Y

- identity up is +Y
- Verify: identity up is +Y
   - Expected: u.y equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity up is +Y")
step("Verify: identity up is +Y")
# @req: REQ-FEATURE-Tran-001
val t = Transform.identity()
val u = t.up()
expect(u.y).to_equal(1.0)
```

</details>

### Transform Composition

#### combines identity transforms

- combines identity transforms
- Verify: combines identity transforms
   - Expected: combined.position.is_zero() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines identity transforms")
step("Verify: combines identity transforms")
# @req: REQ-FEATURE-Tran-001
val parent = Transform.identity()
val child = Transform.identity()
val combined = parent.combine(child)
expect(combined.position.is_zero()).to_equal(true)
```

</details>

#### combines translation

- combines translation
- Verify: combines translation
   - Expected: combined.position.x equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines translation")
step("Verify: combines translation")
# @req: REQ-FEATURE-Tran-001
val parent = Transform(position: Vec3(x: 10.0, y: 0.0, z: 0.0), rotation: Quat.identity(), scale: Vec3.one())
val child = Transform(position: Vec3(x: 5.0, y: 0.0, z: 0.0), rotation: Quat.identity(), scale: Vec3.one())
val combined = parent.combine(child)
expect(combined.position.x).to_equal(15.0)
```

</details>

#### transforms a point

- transforms a point
- Verify: transforms a point
   - Expected: result.x equals `11.0`
   - Expected: result.y equals `22.0`
   - Expected: result.z equals `33.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transforms a point")
step("Verify: transforms a point")
# @req: REQ-FEATURE-Tran-001
val t = Transform(position: Vec3(x: 10.0, y: 20.0, z: 30.0), rotation: Quat.identity(), scale: Vec3.one())
val p = Vec3(x: 1.0, y: 2.0, z: 3.0)
val result = t.transform_point(p)
expect(result.x).to_equal(11.0)
expect(result.y).to_equal(22.0)
expect(result.z).to_equal(33.0)
```

</details>

### Transform Interpolation

#### lerps between transforms

- lerps between transforms
- Verify: lerps between transforms
   - Expected: mid.position.x equals `5.0`
   - Expected: mid.position.y equals `5.0`
   - Expected: mid.position.z equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lerps between transforms")
step("Verify: lerps between transforms")
# @req: REQ-FEATURE-Tran-001
val a = Transform(position: Vec3.zero(), rotation: Quat.identity(), scale: Vec3.one())
val b = Transform(position: Vec3(x: 10.0, y: 10.0, z: 10.0), rotation: Quat.identity(), scale: Vec3.one())
val mid = a.lerp(b, 0.5)
expect(mid.position.x).to_equal(5.0)
expect(mid.position.y).to_equal(5.0)
expect(mid.position.z).to_equal(5.0)
```

</details>

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
- `REQ-FEATURE-Tran-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3cdddcfe1321a525f23977c820a114a55880e35361aa047259b26fd1307e85d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3cdddcfe1321a525f23977c820a114a55880e35361aa047259b26fd1307e85d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3cdddcfe1321a525f23977c820a114a55880e35361aa047259b26fd1307e85d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/transform_spec.spl
mirror: doc/06_spec/03_system/feature/usage/transform_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/transform_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/transform_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/transform_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/transform_spec.spl:177:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates identity transform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/transform_spec.spl:189:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to mat4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/transform_spec.spl:206:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identity forward is +Z' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
