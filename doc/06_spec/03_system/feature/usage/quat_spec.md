# Quaternion Specification

> Purpose: creates identity quaternion

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quaternion Specification

Purpose: creates identity quaternion

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-003 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/quat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: creates identity quaternion
Audience: compiler and tooling engineers who maintain this spec

# Quaternion Specification


**Feature IDs:** #MATH-003
**Category:** Stdlib
**Difficulty:** 3/5
**Status:** Implemented

## Overview
Quat (f32) and Quatd (f64) quaternion types for 3D rotations.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Quat | Quaternion with f32 precision |
| SLERP | Spherical linear interpolation |
| Composition | Rotation composition via multiplication |

## Behavior
- Identity quaternion represents no rotation
- from_axis_angle and from_euler constructors
- SLERP interpolation for smooth rotation
- Quaternion-vector rotation

## Scenarios

### Quaternion Construction

#### creates identity quaternion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates identity quaternion
- Verify: creates identity quaternion
   - Expected: q.w equals `1.0`
   - Expected: q.x equals `0.0`
   - Expected: q.y equals `0.0`
   - Expected: q.z equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates identity quaternion")
step("Verify: creates identity quaternion")
# @req: REQ-FEATURE-Quat-001
val q = Quat.identity()
expect(q.w).to_equal(1.0)
expect(q.x).to_equal(0.0)
expect(q.y).to_equal(0.0)
expect(q.z).to_equal(0.0)
```

</details>

#### creates from axis-angle

- creates from axis-angle
- Verify: creates from axis-angle
   - Expected: q.w equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates from axis-angle")
step("Verify: creates from axis-angle")
# @req: REQ-FEATURE-Quat-001
val axis = Vec3(x: 0.0, y: 1.0, z: 0.0)
val q = Quat.from_axis_angle(axis, 0.0)
# Zero rotation = identity
expect(q.w).to_equal(1.0)
```

</details>

#### normalizes a quaternion

- normalizes a quaternion
- Verify: normalizes a quaternion
   - Expected: n.w equals `1.0`
   - Expected: n.x equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes a quaternion")
step("Verify: normalizes a quaternion")
# @req: REQ-FEATURE-Quat-001
val q = Quat(w: 2.0, x: 0.0, y: 0.0, z: 0.0)
val n = q.normalize()
expect(n.w).to_equal(1.0)
expect(n.x).to_equal(0.0)
```

</details>

### Quaternion Rotation

#### identity rotation leaves vector unchanged

- identity rotation leaves vector unchanged
- Verify: identity rotation leaves vector unchanged
   - Expected: r.x equals `1.0`
   - Expected: r.y equals `2.0`
   - Expected: r.z equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity rotation leaves vector unchanged")
step("Verify: identity rotation leaves vector unchanged")
# @req: REQ-FEATURE-Quat-001
val q = Quat.identity()
val v = Vec3(x: 1.0, y: 2.0, z: 3.0)
val r = q.rotate_vector(v)
expect(r.x).to_equal(1.0)
expect(r.y).to_equal(2.0)
expect(r.z).to_equal(3.0)
```

</details>

#### composes rotations via multiplication

- composes rotations via multiplication
- Verify: composes rotations via multiplication
   - Expected: q3.w equals `1.0`
   - Expected: q3.x equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("composes rotations via multiplication")
step("Verify: composes rotations via multiplication")
# @req: REQ-FEATURE-Quat-001
val q1 = Quat.identity()
val q2 = Quat.identity()
val q3 = q1.mul(q2)
expect(q3.w).to_equal(1.0)
expect(q3.x).to_equal(0.0)
```

</details>

#### conjugate negates vector part

- conjugate negates vector part
- Verify: conjugate negates vector part
   - Expected: c.w equals `1.0`
   - Expected: c.x equals `-2.0`
   - Expected: c.y equals `-3.0`
   - Expected: c.z equals `-4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("conjugate negates vector part")
step("Verify: conjugate negates vector part")
# @req: REQ-FEATURE-Quat-001
val q = Quat(w: 1.0, x: 2.0, y: 3.0, z: 4.0)
val c = q.conjugate()
expect(c.w).to_equal(1.0)
expect(c.x).to_equal(-2.0)
expect(c.y).to_equal(-3.0)
expect(c.z).to_equal(-4.0)
```

</details>

### Quaternion SLERP

#### slerp at t=0 returns start

- slerp at t=0 returns start
- Verify: slerp at t=0 returns start
   - Expected: diff_w < 0.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slerp at t=0 returns start")
step("Verify: slerp at t=0 returns start")
# @req: REQ-FEATURE-Quat-001
val a = Quat.identity()
val b = Quat.from_axis_angle(Vec3.up(), 1.57)
val r = a.slerp(b, 0.0)
# Should be close to a (floating-point tolerance)
var diff_w = r.w - a.w
if diff_w < 0.0:
    diff_w = 0.0 - diff_w
expect(diff_w < 0.1).to_equal(true)
```

</details>

#### slerp at t=1 returns end

- slerp at t=1 returns end
- Verify: slerp at t=1 returns end
   - Expected: diff < 0.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("slerp at t=1 returns end")
step("Verify: slerp at t=1 returns end")
# @req: REQ-FEATURE-Quat-001
val a = Quat.identity()
val axis = Vec3(x: 0.0, y: 1.0, z: 0.0)
val b = Quat.from_axis_angle(axis, 1.57)
val r = a.slerp(b, 1.0)
# Should be close to b (relaxed tolerance for interpreter precision)
var diff = r.w - b.w
if diff < 0.0:
    diff = 0.0 - diff
expect(diff < 0.1).to_equal(true)
```

</details>

### Quaternion Conversions

<details>
<summary>Advanced: converts to rotation matrix</summary>

#### converts to rotation matrix

- converts to rotation matrix
- Verify: converts to rotation matrix
   - Expected: m.data[0] equals `1.0`
   - Expected: m.data[5] equals `1.0`
   - Expected: m.data[10] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts to rotation matrix")
step("Verify: converts to rotation matrix")
# @req: REQ-FEATURE-Quat-001
val q = Quat.identity()
val m = q.to_mat4()
expect(m.data[0]).to_equal(1.0)
expect(m.data[5]).to_equal(1.0)
expect(m.data[10]).to_equal(1.0)
```

</details>


</details>

#### converts between f32 and f64

- converts between f32 and f64
- Verify: converts between f32 and f64
   - Expected: q64.w equals `1.0`
   - Expected: q32b.w equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts between f32 and f64")
step("Verify: converts between f32 and f64")
# @req: REQ-FEATURE-Quat-001
val q32 = Quat(w: 1.0, x: 0.0, y: 0.0, z: 0.0)
val q64 = q32.to_f64()
expect(q64.w).to_equal(1.0)
val q32b = q64.to_f32()
expect(q32b.w).to_equal(1.0)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-FEATURE-Quat-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `73d350a70c4d1f2de446a534ba6eb18bb1ee9c6e61e16602504991219fbb7bbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73d350a70c4d1f2de446a534ba6eb18bb1ee9c6e61e16602504991219fbb7bbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73d350a70c4d1f2de446a534ba6eb18bb1ee9c6e61e16602504991219fbb7bbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/quat_spec.spl
mirror: doc/06_spec/03_system/feature/usage/quat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/quat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/quat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/quat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/quat_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates identity quaternion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/quat_spec.spl:179:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates from axis-angle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/quat_spec.spl:189:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes a quaternion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
