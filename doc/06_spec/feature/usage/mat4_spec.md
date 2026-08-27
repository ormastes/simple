# Mat4 Specification

> Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mat4 Specification

Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-002 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/mat4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Column-major | GPU/Vulkan standard storage order |
| Transform | Translation, rotation, scale factories |
| Projection | Perspective and orthographic projection |

## Behavior
- Column-major storage for GPU compatibility
- Factory methods for common transforms
- Matrix multiplication and inverse
- Point and vector transformation

## Scenarios

### Mat4 Identity and Factories

<details>
<summary>Advanced: creates identity matrix</summary>

#### creates identity matrix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates identity matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates identity matrix")
val m = math.Mat4.identity()
expect m.data[0] == 1.0
expect m.data[5] == 1.0
expect m.data[10] == 1.0
expect m.data[15] == 1.0
expect m.data[1] == 0.0
```

</details>


</details>

<details>
<summary>Advanced: creates translation matrix</summary>

#### creates translation matrix

- creates translation matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates translation matrix")
val m = math.Mat4.translation(1.0, 2.0, 3.0)
# Column-major: translation in column 3 (indices 12, 13, 14)
expect m.data[12] == 1.0
expect m.data[13] == 2.0
expect m.data[14] == 3.0
```

</details>


</details>

<details>
<summary>Advanced: creates scale matrix</summary>

#### creates scale matrix

- creates scale matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates scale matrix")
val m = math.Mat4.scale(2.0, 3.0, 4.0)
expect m.data[0] == 2.0
expect m.data[5] == 3.0
expect m.data[10] == 4.0
```

</details>


</details>

### Mat4 Operations

#### multiplies identity by identity

- multiplies identity by identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies identity by identity")
val a = math.Mat4.identity()
val b = math.Mat4.identity()
val c = a.mul(b)
expect c.data[0] == 1.0
expect c.data[5] == 1.0
expect c.data[10] == 1.0
expect c.data[15] == 1.0
```

</details>

#### multiplies translation matrices

- multiplies translation matrices


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies translation matrices")
val a = math.Mat4.translation(1.0, 0.0, 0.0)
val b = math.Mat4.translation(0.0, 2.0, 0.0)
val c = a.mul(b)
# Combined translation: (1, 2, 0)
expect c.data[12] == 1.0
expect c.data[13] == 2.0
expect c.data[14] == 0.0
```

</details>

#### transforms a point

- transforms a point


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transforms a point")
val m = math.Mat4.translation(10.0, 20.0, 30.0)
val p = math.Vec3(1.0, 2.0, 3.0)
val result = m.transform_point(p)
expect result.x == 11.0
expect result.y == 22.0
expect result.z == 33.0
```

</details>

#### transforms a direction vector (ignores translation)

- transforms a direction vector (ignores translation)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transforms a direction vector (ignores translation)")
val m = math.Mat4.translation(10.0, 20.0, 30.0)
val v = math.Vec3(1.0, 0.0, 0.0)
val result = m.transform_vec3(v)
expect result.x == 1.0
expect result.y == 0.0
expect result.z == 0.0
```

</details>

<details>
<summary>Advanced: extracts 3x3 submatrix</summary>

#### extracts 3x3 submatrix

- extracts 3x3 submatrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("extracts 3x3 submatrix")
val m = math.Mat4.scale(2.0, 3.0, 4.0)
val m3 = m.to_mat3()
expect m3.data[0] == 2.0
expect m3.data[4] == 3.0
expect m3.data[8] == 4.0
```

</details>


</details>

### Mat4 Inverse

#### inverts identity to identity

- inverts identity to identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inverts identity to identity")
val m = math.Mat4.identity()
val inv = m.inverse()
expect inv.data[0] == 1.0
expect inv.data[5] == 1.0
```

</details>

#### inverts translation

- inverts translation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inverts translation")
val m = math.Mat4.translation(5.0, 10.0, 15.0)
val inv = m.inverse()
# Inverse translation should negate
expect inv.data[12] == -5.0
expect inv.data[13] == -10.0
expect inv.data[14] == -15.0
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f85d6f7f2220dd7ac7ed048783d8fbad5376f9eb0437275a90544f90399c9379`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f85d6f7f2220dd7ac7ed048783d8fbad5376f9eb0437275a90544f90399c9379`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f85d6f7f2220dd7ac7ed048783d8fbad5376f9eb0437275a90544f90399c9379`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/mat4_spec.spl
mirror: doc/06_spec/feature/usage/mat4_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/mat4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/mat4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/mat4_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates identity matrix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/mat4_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates translation matrix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/mat4_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates scale matrix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
