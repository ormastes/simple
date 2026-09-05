# math3d_trig_precision_repro_spec

> Reproducer for `math3d_cos_taylor_precision_2026-07-20`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math3d_trig_precision_repro_spec

Reproducer for `math3d_cos_taylor_precision_2026-07-20`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/engine/math3d_trig_precision_repro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproducer for `math3d_cos_taylor_precision_2026-07-20`.

`src/lib/common/engine/math3d.spl` implements `_sin` as a raw Taylor series
truncated after the x^7 term, applied over the whole range (-pi, pi] after a
crude 2*pi range reduction. The series is only accurate near zero; at the ends
of the reduced range it is catastrophically wrong:

    _sin(pi)    -> -0.0752   (true value 0.0)
    _cos(pi/2)  -> -0.0752   (true value 0.0, since _cos(x) = _sin(x + pi/2))
    _tan(pi/4)  ->  1.0107   (true value 1.0)

`_sin`/`_cos`/`_tan` are module-private, so this spec observes them through the
two public surfaces that consume them:

  * `Quaternion.from_axis_angle` — w is cos(angle/2), y is sin(angle/2)
  * `Mat4.perspective`          — data[0] is 1/(tan(fov/2) * aspect)

Both compile clean, exit 0, and hand back a silently wrong number.

## Scenarios

### math3d trig precision (repro: math3d_cos_taylor_precision_2026-07-20)

### Quaternion.from_axis_angle w = cos(angle/2)

#### gives w == 0 for a 180 degree rotation (cos(pi/2) == 0)

- gives w == 0 for a 180 degree rotation (cos(pi/2) == 0)
   - Expected: abs_f(q.w) < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives w == 0 for a 180 degree rotation (cos(pi/2) == 0)")
# half-angle is pi/2, the worst point of the truncated series:
# the buggy _cos returns -0.0752 here instead of 0.0.
val q = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(180.0))
expect(abs_f(q.w) < 0.000000001).to_equal(true)
```

</details>

#### gives y == 1 for a 180 degree rotation (sin(pi/2) == 1)

- gives y == 1 for a 180 degree rotation (sin(pi/2) == 1)
   - Expected: abs_f(q.y - 1.0) < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives y == 1 for a 180 degree rotation (sin(pi/2) == 1)")
val q = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(180.0))
expect(abs_f(q.y - 1.0) < 0.000000001).to_equal(true)
```

</details>

#### gives w == -1 for a 360 degree rotation (cos(pi) == -1)

- gives w == -1 for a 360 degree rotation (cos(pi) == -1)
   - Expected: abs_f(q.w + 1.0) < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives w == -1 for a 360 degree rotation (cos(pi) == -1)")
# half-angle is pi. The buggy _sin(pi + pi/2) reduces to -pi/2 and
# returns -1.0013, so normalisation cannot hide the error either.
val q = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(360.0))
expect(abs_f(q.w + 1.0) < 0.000000001).to_equal(true)
```

</details>

#### gives y == 0 for a 360 degree rotation (sin(pi) == 0)

- gives y == 0 for a 360 degree rotation (sin(pi) == 0)
   - Expected: abs_f(q.y) < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives y == 0 for a 360 degree rotation (sin(pi) == 0)")
# This is the headline number: sin(pi) must be 0, the truncated
# series returns -0.0752 -- a 7.5% error on a unit quaternion.
val q = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(360.0))
expect(abs_f(q.y) < 0.000000001).to_equal(true)
```

</details>

#### gives w == cos(45 deg) for a 90 degree rotation

- gives w == cos(45 deg) for a 90 degree rotation
   - Expected: abs_f(q.w - 0.7071067811865476) < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives w == cos(45 deg) for a 90 degree rotation")
val q = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(90.0))
expect(abs_f(q.w - 0.7071067811865476) < 0.000000001).to_equal(true)
```

</details>

### Mat4.perspective data[0] = 1/(tan(fov/2) * aspect)

#### gives exactly 1.0 for a 90 degree fov at aspect 1.0

- gives exactly 1.0 for a 90 degree fov at aspect 1.0
   - Expected: abs_f(m.data[0] - 1.0) < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives exactly 1.0 for a 90 degree fov at aspect 1.0")
# tan(pi/4) is exactly 1, so data[0] must be exactly 1.
# The buggy _tan returns 1.0107, a 1% projection error.
val m = Mat4.perspective(Angle.from_degrees(90.0), 1.0, 0.1, 100.0)
expect(abs_f(m.data[0] - 1.0) < 0.000000001).to_equal(true)
```

</details>

#### gives 1/tan(30 deg) for a 60 degree fov at aspect 1.0

- gives 1/tan(30 deg) for a 60 degree fov at aspect 1.0
   - Expected: abs_f(m.data[0] - 1.7320508075688772) < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives 1/tan(30 deg) for a 60 degree fov at aspect 1.0")
val m = Mat4.perspective(Angle.from_degrees(60.0), 1.0, 0.1, 100.0)
expect(abs_f(m.data[0] - 1.7320508075688772) < 0.000000001).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `bda516cb72fe3c91ac11580abfa28026a8db0b33161ab1352dbc1ac1d0e30c0c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bda516cb72fe3c91ac11580abfa28026a8db0b33161ab1352dbc1ac1d0e30c0c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bda516cb72fe3c91ac11580abfa28026a8db0b33161ab1352dbc1ac1d0e30c0c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/engine/math3d_trig_precision_repro_spec.spl
mirror: doc/06_spec/01_unit/lib/common/engine/math3d_trig_precision_repro_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/engine/math3d_trig_precision_repro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/engine/math3d_trig_precision_repro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/engine/math3d_trig_precision_repro_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives w == 0 for a 180 degree rotation (cos(pi/2) == 0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/math3d_trig_precision_repro_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives y == 1 for a 180 degree rotation (sin(pi/2) == 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/math3d_trig_precision_repro_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives w == -1 for a 360 degree rotation (cos(pi) == -1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
