# math3d trig precision

> Reproducing + class-detection spec for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math3d trig precision

Reproducing + class-detection spec for

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-ENGINE-MATH3D-TRIG |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/engine/math3d_trig_precision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproducing + class-detection spec for
`doc/08_tracking/bug/math3d_cos_taylor_precision_2026-07-20.md`.

`_sin` range-reduced only to [-pi, pi] and then evaluated a short Taylor
series. The series is accurate near 0 but not near +/-pi, and `_cos(x)` was
`_sin(x + pi/2)`, which pushes an argument that started near 0 out to the
worst part of the domain. `Quaternion.from_axis_angle` is the public path:
its `w` component is `_cos(angle/2)`, so a 180-degree rotation must yield
`w == 0`, and `.normalize()` hides the magnitude error but not the wrong
component ratio -- the result is a silently wrong rotation, not a crash.

## Scenarios

### math3d trig precision

#### 180-degree rotation via from_axis_angle

#### has a zero scalar component (w = cos(pi/2))

- has a zero scalar component (w = cos(pi/2))


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has a zero scalar component (w = cos(pi/2))")
val q = Quaternion.from_axis_angle(
    axis: Vec3(x: 0.0, y: 0.0, z: 1.0),
    angle: Angle(radians: 3.141592653589793))
expect(abs_f(q.w) < 0.000001).to_be_true()
```

</details>

#### maps +x onto -x

- maps +x onto -x


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps +x onto -x")
val q = Quaternion.from_axis_angle(
    axis: Vec3(x: 0.0, y: 0.0, z: 1.0),
    angle: Angle(radians: 3.141592653589793))
val r = q.rotate_vector(Vec3(x: 1.0, y: 0.0, z: 0.0))
expect(abs_f(r.x + 1.0) < 0.000001).to_be_true()
expect(abs_f(r.y) < 0.000001).to_be_true()
```

</details>

#### rotation identities hold across the whole domain

#### a full turn is the identity rotation for every axis sample

- a full turn is the identity rotation for every axis sample


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a full turn is the identity rotation for every axis sample")
val two_pi = 6.283185307179586
var k = 0
var worst = 0.0
while k <= 24:
    val ang = two_pi * (0.0 + k) / 24.0
    val q = Quaternion.from_axis_angle(
        axis: Vec3(x: 0.0, y: 0.0, z: 1.0),
        angle: Angle(radians: ang))
    # x^2 + w^2 must be 1 already; the informative check is that
    # z = sin(ang/2) and w = cos(ang/2) agree with each other.
    val ss = q.z * q.z + q.w * q.w
    val e = abs_f(ss - 1.0)
    if e > worst:
        worst = e
    k = k + 1
expect(worst < 0.000001).to_be_true()
```

</details>

#### composing two half rotations equals one full rotation

- composing two half rotations equals one full rotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composing two half rotations equals one full rotation")
val axis = Vec3(x: 0.0, y: 0.0, z: 1.0)
val h = Quaternion.from_axis_angle(axis: axis, angle: Angle(radians: 1.5707963267948966))
val f = Quaternion.from_axis_angle(axis: axis, angle: Angle(radians: 3.141592653589793))
val c = h.mul(h)
expect(abs_f(c.z - f.z) < 0.000001).to_be_true()
expect(abs_f(c.w - f.w) < 0.000001).to_be_true()
```

</details>

#### rotating by 2pi restores the original vector

- rotating by 2pi restores the original vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotating by 2pi restores the original vector")
val q = Quaternion.from_axis_angle(
    axis: Vec3(x: 0.0, y: 0.0, z: 1.0),
    angle: Angle(radians: 6.283185307179586))
val r = q.rotate_vector(Vec3(x: 1.0, y: 2.0, z: 3.0))
expect(abs_f(r.x - 1.0) < 0.000001).to_be_true()
expect(abs_f(r.y - 2.0) < 0.000001).to_be_true()
```

</details>

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

- Canonical SPipe generation for source `abfcb652438ed7aa8cd9919f462025daec66fc2e2c4dc619d4d92404c569fb83`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abfcb652438ed7aa8cd9919f462025daec66fc2e2c4dc619d4d92404c569fb83`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abfcb652438ed7aa8cd9919f462025daec66fc2e2c4dc619d4d92404c569fb83`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/engine/math3d_trig_precision_spec.spl
mirror: doc/06_spec/01_unit/lib/engine/math3d_trig_precision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/engine/math3d_trig_precision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/engine/math3d_trig_precision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/engine/math3d_trig_precision_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a zero scalar component (w = cos(pi/2))' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/math3d_trig_precision_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps +x onto -x' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/math3d_trig_precision_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a full turn is the identity rotation for every axis sample' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
