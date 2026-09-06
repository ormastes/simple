# math3d_trig_domain_sweep_class_spec

> Similar-problem detection spec for the defect CLASS behind

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math3d_trig_domain_sweep_class_spec

Similar-problem detection spec for the defect CLASS behind

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Similar-problem detection spec for the defect CLASS behind
`math3d_cos_taylor_precision_2026-07-20`.

The class is: *a transcendental helper in the stdlib that is accurate near its
expansion point and silently degrades across the rest of its domain.* A
reproducer that only probes one or two angles cannot catch this -- a truncated
series is exact at 0 and merely bad far away, so any spec that samples near the
expansion point passes with the bug fully present.

This spec therefore sweeps the WHOLE circle at 15-degree steps and checks
sin/cos against independently sourced exact literals (never against another
series implementation, which would let the same truncation error cancel on both
sides of the comparison).

Observation surface is `Quaternion.from_axis_angle(up, 2a)`, whose normalised
components are y = sin(a) and w = cos(a). Normalisation divides both by
sqrt(sin^2 + cos^2), which is 1 for any correct implementation, so it neither
masks a phase error nor a sign error.

A future regression that reintroduces a low-order series, narrows the range
reduction, or drops the quadrant fold will go red here even if it stays green on
the small-angle reproducer.

## Scenarios

### math3d trig accuracy across the full domain (class detection)

#### matches sin at every 15-degree step of the full circle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches sin at every 15-degree step of the full circle
   - Expected: worst_i >= 0 is true
   - Expected: worst < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches sin at every 15-degree step of the full circle")
val sins = sin_table()
var worst: f64 = 0.0
var worst_i: i64 = -1
var i: i64 = 0
while i < 25:
    # half-angle is i*15 degrees, so the rotation angle is i*30.
    val q = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees((i * 30) * 1.0))
    val err = abs_f(q.y - sins[i])
    if err > worst:
        worst = err
        worst_i = i
    i = i + 1
expect(worst_i >= 0).to_equal(true)
expect(worst < 0.000000001).to_equal(true)
```

</details>

#### matches cos at every 15-degree step of the full circle

- matches cos at every 15-degree step of the full circle
   - Expected: worst_i >= 0 is true
   - Expected: worst < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches cos at every 15-degree step of the full circle")
val coss = cos_table()
var worst: f64 = 0.0
var worst_i: i64 = -1
var i: i64 = 0
while i < 25:
    val q = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees((i * 30) * 1.0))
    val err = abs_f(q.w - coss[i])
    if err > worst:
        worst = err
        worst_i = i
    i = i + 1
expect(worst_i >= 0).to_equal(true)
expect(worst < 0.000000001).to_equal(true)
```

</details>

#### stays accurate outside the primary reduction range

- stays accurate outside the primary reduction range
   - Expected: checked equals `12`
   - Expected: worst < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stays accurate outside the primary reduction range")
# A range reduction that only subtracts one period, or that leaves the
# argument in a band the series cannot cover, breaks here while the
# small-angle cases above stay green.
var i: i64 = 0
var worst: f64 = 0.0
var checked: i64 = 0
while i < 12:
    # rotation angles of 720 + i*30 degrees are congruent to i*30.
    val far = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(720.0 + (i * 30) * 1.0))
    val near = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees((i * 30) * 1.0))
    val ey = abs_f(far.y - near.y)
    val ew = abs_f(far.w - near.w)
    if ey > worst:
        worst = ey
    if ew > worst:
        worst = ew
    checked = checked + 1
    i = i + 1
expect(checked).to_equal(12)
expect(worst < 0.000000001).to_equal(true)
```

</details>

#### keeps the sin^2 + cos^2 == 1 identity before normalisation can hide it

- keeps the sin^2 + cos^2 == 1 identity before normalisation can hide it
   - Expected: abs_f(q45.y / q45.w - 1.0) < 0.000000001 is true
   - Expected: abs_f(q30.y / q30.w - 0.5773502691896257) < 0.000000001 is true
   - Expected: abs_f(q60.y / q60.w - 1.7320508075688772) < 0.000000001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the sin^2 + cos^2 == 1 identity before normalisation can hide it")
# from_axis_angle normalises, so this checks the identity indirectly:
# if sin and cos are individually wrong but by the SAME factor, the
# table checks above would still pass. Comparing the tangent ratio
# y/w against exact literals closes that hole.
val q45 = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(90.0))
expect(abs_f(q45.y / q45.w - 1.0) < 0.000000001).to_equal(true)
val q30 = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(60.0))
expect(abs_f(q30.y / q30.w - 0.5773502691896257) < 0.000000001).to_equal(true)
val q60 = Quaternion.from_axis_angle(Vec3.up(), Angle.from_degrees(120.0))
expect(abs_f(q60.y / q60.w - 1.7320508075688772) < 0.000000001).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `f96f2b27b0a4883c61509eeac2a1aba5d2d838464451dcf7ca8b11baaf949bc4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f96f2b27b0a4883c61509eeac2a1aba5d2d838464451dcf7ca8b11baaf949bc4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f96f2b27b0a4883c61509eeac2a1aba5d2d838464451dcf7ca8b11baaf949bc4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.spl
mirror: doc/06_spec/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches sin at every 15-degree step of the full circle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches cos at every 15-degree step of the full circle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/math3d_trig_domain_sweep_class_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays accurate outside the primary reduction range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
