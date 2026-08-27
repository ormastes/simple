# Vec3 Specification

> Purpose: creates a vector with components

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vec3 Specification

Purpose: creates a vector with components

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/vec3_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: creates a vector with components
Audience: compiler and tooling engineers who maintain this spec

# Vec3 Specification


**Feature IDs:** #MATH-001
**Category:** Stdlib
**Difficulty:** 2/5
**Status:** Implemented

## Overview
Vec3 (f32) and Vec3d (f64) 3D vector types with arithmetic, geometric, and utility methods.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Vec3 | 3D vector with f32 precision |
| Vec3d | 3D vector with f64 precision |
| Dual precision | All types in both f32 and f64 |

## Behavior
- Supports add, sub, scale, dot, cross operations
- Magnitude/length aliases
- Static factory methods for common directions
- Conversion between f32 and f64

## Scenarios

### Vec3 Construction

#### creates a vector with components

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a vector with components
- Verify: creates a vector with components
   - Expected: v.x equals `1.0`
   - Expected: v.y equals `2.0`
   - Expected: v.z equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a vector with components")
step("Verify: creates a vector with components")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3(x: 1.0, y: 2.0, z: 3.0)
expect(v.x).to_equal(1.0)
expect(v.y).to_equal(2.0)
expect(v.z).to_equal(3.0)
```

</details>

#### creates zero vector

- creates zero vector
- Verify: creates zero vector
   - Expected: v.x equals `0.0`
   - Expected: v.y equals `0.0`
   - Expected: v.z equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates zero vector")
step("Verify: creates zero vector")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3.zero()
expect(v.x).to_equal(0.0)
expect(v.y).to_equal(0.0)
expect(v.z).to_equal(0.0)
```

</details>

#### creates one vector

- creates one vector
- Verify: creates one vector
   - Expected: v.x equals `1.0`
   - Expected: v.y equals `1.0`
   - Expected: v.z equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates one vector")
step("Verify: creates one vector")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3.one()
expect(v.x).to_equal(1.0)
expect(v.y).to_equal(1.0)
expect(v.z).to_equal(1.0)
```

</details>

#### creates directional vectors

- creates directional vectors
- Verify: creates directional vectors
   - Expected: Vec3.up().y equals `1.0`
   - Expected: Vec3.down().y equals `-1.0`
   - Expected: Vec3.left().x equals `-1.0`
   - Expected: Vec3.right().x equals `1.0`
   - Expected: Vec3.forward().z equals `1.0`
   - Expected: Vec3.back().z equals `-1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates directional vectors")
step("Verify: creates directional vectors")
# @req: REQ-FEATURE-Vec3-001
expect(Vec3.up().y).to_equal(1.0)
expect(Vec3.down().y).to_equal(-1.0)
expect(Vec3.left().x).to_equal(-1.0)
expect(Vec3.right().x).to_equal(1.0)
expect(Vec3.forward().z).to_equal(1.0)
expect(Vec3.back().z).to_equal(-1.0)
```

</details>

### Vec3 Arithmetic

#### adds two vectors

- adds two vectors
- Verify: adds two vectors
   - Expected: c.x equals `5.0`
   - Expected: c.y equals `7.0`
   - Expected: c.z equals `9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds two vectors")
step("Verify: adds two vectors")
# @req: REQ-FEATURE-Vec3-001
val a = Vec3(x: 1.0, y: 2.0, z: 3.0)
val b = Vec3(x: 4.0, y: 5.0, z: 6.0)
val c = a.add(b)
expect(c.x).to_equal(5.0)
expect(c.y).to_equal(7.0)
expect(c.z).to_equal(9.0)
```

</details>

#### subtracts two vectors

- subtracts two vectors
- Verify: subtracts two vectors
   - Expected: c.x equals `3.0`
   - Expected: c.y equals `3.0`
   - Expected: c.z equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("subtracts two vectors")
step("Verify: subtracts two vectors")
# @req: REQ-FEATURE-Vec3-001
val a = Vec3(x: 4.0, y: 5.0, z: 6.0)
val b = Vec3(x: 1.0, y: 2.0, z: 3.0)
val c = a.sub(b)
expect(c.x).to_equal(3.0)
expect(c.y).to_equal(3.0)
expect(c.z).to_equal(3.0)
```

</details>

#### scales a vector

- scales a vector
- Verify: scales a vector
   - Expected: s.x equals `2.0`
   - Expected: s.y equals `4.0`
   - Expected: s.z equals `6.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scales a vector")
step("Verify: scales a vector")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3(x: 1.0, y: 2.0, z: 3.0)
val s = v.scale(2.0)
expect(s.x).to_equal(2.0)
expect(s.y).to_equal(4.0)
expect(s.z).to_equal(6.0)
```

</details>

#### computes dot product

- computes dot product
- Verify: computes dot product
   - Expected: a.dot(b) equals `0.0`
   - Expected: c.dot(d) equals `32.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes dot product")
step("Verify: computes dot product")
# @req: REQ-FEATURE-Vec3-001
val a = Vec3(x: 1.0, y: 0.0, z: 0.0)
val b = Vec3(x: 0.0, y: 1.0, z: 0.0)
expect(a.dot(b)).to_equal(0.0)

val c = Vec3(x: 1.0, y: 2.0, z: 3.0)
val d = Vec3(x: 4.0, y: 5.0, z: 6.0)
expect(c.dot(d)).to_equal(32.0)
```

</details>

#### computes cross product

- computes cross product
- Verify: computes cross product
   - Expected: zv.x equals `0.0`
   - Expected: zv.y equals `0.0`
   - Expected: zv.z equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes cross product")
step("Verify: computes cross product")
# @req: REQ-FEATURE-Vec3-001
val xv = Vec3(x: 1.0, y: 0.0, z: 0.0)
val yv = Vec3(x: 0.0, y: 1.0, z: 0.0)
val zv = xv.cross(yv)
expect(zv.x).to_equal(0.0)
expect(zv.y).to_equal(0.0)
expect(zv.z).to_equal(1.0)
```

</details>

### Vec3 Geometric Methods

#### computes magnitude

- computes magnitude
- Verify: computes magnitude
   - Expected: v.magnitude() equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes magnitude")
step("Verify: computes magnitude")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3(x: 3.0, y: 4.0, z: 0.0)
expect(v.magnitude()).to_equal(5.0)
```

</details>

#### magnitude and length are aliases

- magnitude and length are aliases
- Verify: magnitude and length are aliases
   - Expected: v.magnitude() equals `v.length()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("magnitude and length are aliases")
step("Verify: magnitude and length are aliases")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3(x: 3.0, y: 4.0, z: 0.0)
expect(v.magnitude()).to_equal(v.length())
```

</details>

#### normalizes a vector

- normalizes a vector
- Verify: normalizes a vector
   - Expected: n.x equals `1.0`
   - Expected: n.y equals `0.0`
   - Expected: n.z equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes a vector")
step("Verify: normalizes a vector")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3(x: 3.0, y: 0.0, z: 0.0)
val n = v.normalize()
expect(n.x).to_equal(1.0)
expect(n.y).to_equal(0.0)
expect(n.z).to_equal(0.0)
```

</details>

#### computes distance

- computes distance
- Verify: computes distance
   - Expected: a.distance(b) equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes distance")
step("Verify: computes distance")
# @req: REQ-FEATURE-Vec3-001
val a = Vec3(x: 0.0, y: 0.0, z: 0.0)
val b = Vec3(x: 3.0, y: 4.0, z: 0.0)
expect(a.distance(b)).to_equal(5.0)
```

</details>

#### distance and distance_to are aliases

- distance and distance_to are aliases
- Verify: distance and distance_to are aliases
   - Expected: a.distance(b) equals `a.distance_to(b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("distance and distance_to are aliases")
step("Verify: distance and distance_to are aliases")
# @req: REQ-FEATURE-Vec3-001
val a = Vec3(x: 0.0, y: 0.0, z: 0.0)
val b = Vec3(x: 3.0, y: 4.0, z: 0.0)
expect(a.distance(b)).to_equal(a.distance_to(b))
```

</details>

#### interpolates linearly

- interpolates linearly
- Verify: interpolates linearly
   - Expected: mid.x equals `5.0`
   - Expected: mid.y equals `5.0`
   - Expected: mid.z equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates linearly")
step("Verify: interpolates linearly")
# @req: REQ-FEATURE-Vec3-001
val a = Vec3(x: 0.0, y: 0.0, z: 0.0)
val b = Vec3(x: 10.0, y: 10.0, z: 10.0)
val mid = a.lerp(b, 0.5)
expect(mid.x).to_equal(5.0)
expect(mid.y).to_equal(5.0)
expect(mid.z).to_equal(5.0)
```

</details>

### Vec3 Utility Methods

#### detects zero vector

- detects zero vector
- Verify: detects zero vector
   - Expected: Vec3.zero().is_zero() is true
   - Expected: Vec3(x: 1.0, y: 0.0, z: 0.0).is_zero() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects zero vector")
step("Verify: detects zero vector")
# @req: REQ-FEATURE-Vec3-001
expect(Vec3.zero().is_zero()).to_equal(true)
expect(Vec3(x: 1.0, y: 0.0, z: 0.0).is_zero()).to_equal(false)
```

</details>

#### detects near-zero vector

- detects near-zero vector
- Verify: detects near-zero vector
   - Expected: v.is_near_zero() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects near-zero vector")
step("Verify: detects near-zero vector")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3(x: 0.0000001, y: 0.0, z: 0.0)
expect(v.is_near_zero()).to_equal(true)
```

</details>

#### checks unit vector

- checks unit vector
- Verify: checks unit vector
   - Expected: Vec3(x: 1.0, y: 0.0, z: 0.0).is_unit() is true
   - Expected: Vec3(x: 2.0, y: 0.0, z: 0.0).is_unit() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks unit vector")
step("Verify: checks unit vector")
# @req: REQ-FEATURE-Vec3-001
expect(Vec3(x: 1.0, y: 0.0, z: 0.0).is_unit()).to_equal(true)
expect(Vec3(x: 2.0, y: 0.0, z: 0.0).is_unit()).to_equal(false)
```

</details>

#### computes component min/max

- computes component min/max
- Verify: computes component min/max
   - Expected: mn.x equals `1.0`
   - Expected: mn.y equals `2.0`
   - Expected: mn.z equals `3.0`
   - Expected: mx.x equals `4.0`
   - Expected: mx.y equals `5.0`
   - Expected: mx.z equals `6.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes component min/max")
step("Verify: computes component min/max")
# @req: REQ-FEATURE-Vec3-001
val a = Vec3(x: 1.0, y: 5.0, z: 3.0)
val b = Vec3(x: 4.0, y: 2.0, z: 6.0)
val mn = a.component_min(b)
val mx = a.component_max(b)
expect(mn.x).to_equal(1.0)
expect(mn.y).to_equal(2.0)
expect(mn.z).to_equal(3.0)
expect(mx.x).to_equal(4.0)
expect(mx.y).to_equal(5.0)
expect(mx.z).to_equal(6.0)
```

</details>

### Vec3d and Conversions

#### creates Vec3d with f64 precision

- creates Vec3d with f64 precision
- Verify: creates Vec3d with f64 precision
   - Expected: v.x equals `1.0`
   - Expected: v.y equals `2.0`
   - Expected: v.z equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates Vec3d with f64 precision")
step("Verify: creates Vec3d with f64 precision")
# @req: REQ-FEATURE-Vec3-001
val v = Vec3d(x: 1.0, y: 2.0, z: 3.0)
expect(v.x).to_equal(1.0)
expect(v.y).to_equal(2.0)
expect(v.z).to_equal(3.0)
```

</details>

#### converts Vec3 to Vec3d

- converts Vec3 to Vec3d
- Verify: converts Vec3 to Vec3d
   - Expected: v64.x equals `1.0`
   - Expected: v64.y equals `2.0`
   - Expected: v64.z equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts Vec3 to Vec3d")
step("Verify: converts Vec3 to Vec3d")
# @req: REQ-FEATURE-Vec3-001
val v32 = Vec3(x: 1.0, y: 2.0, z: 3.0)
val v64 = v32.to_f64()
expect(v64.x).to_equal(1.0)
expect(v64.y).to_equal(2.0)
expect(v64.z).to_equal(3.0)
```

</details>

#### converts Vec3d to Vec3

- converts Vec3d to Vec3
- Verify: converts Vec3d to Vec3
   - Expected: v32.x equals `1.0`
   - Expected: v32.y equals `2.0`
   - Expected: v32.z equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts Vec3d to Vec3")
step("Verify: converts Vec3d to Vec3")
# @req: REQ-FEATURE-Vec3-001
val v64 = Vec3d(x: 1.0, y: 2.0, z: 3.0)
val v32 = v64.to_f32()
expect(v32.x).to_equal(1.0)
expect(v32.y).to_equal(2.0)
expect(v32.z).to_equal(3.0)
```

</details>

#### Vec3d has all Vec3 methods

- Vec3d has all Vec3 methods
- Verify: Vec3d has all Vec3 methods
   - Expected: a.dot(b) equals `32.0`
   - Expected: c.x equals `-3.0`
   - Expected: c.y equals `6.0`
   - Expected: c.z equals `-3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Vec3d has all Vec3 methods")
step("Verify: Vec3d has all Vec3 methods")
# @req: REQ-FEATURE-Vec3-001
val a = Vec3d(x: 1.0, y: 2.0, z: 3.0)
val b = Vec3d(x: 4.0, y: 5.0, z: 6.0)
expect(a.dot(b)).to_equal(32.0)
val c = a.cross(b)
expect(c.x).to_equal(-3.0)
expect(c.y).to_equal(6.0)
expect(c.z).to_equal(-3.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FEATURE-Vec3-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f76a89bec66c6924397ff6eaa186fd7e5017e7de7e21ee237f661402d2616526`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f76a89bec66c6924397ff6eaa186fd7e5017e7de7e21ee237f661402d2616526`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f76a89bec66c6924397ff6eaa186fd7e5017e7de7e21ee237f661402d2616526`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/vec3_spec.spl
mirror: doc/06_spec/03_system/feature/usage/vec3_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/vec3_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/vec3_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/vec3_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 56 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/vec3_spec.spl:180:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a vector with components' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/vec3_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates zero vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/vec3_spec.spl:200:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates one vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
