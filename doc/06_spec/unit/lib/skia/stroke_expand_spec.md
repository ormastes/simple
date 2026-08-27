# Skia Stroke Expansion Specification

> Tests for expand_stroke — the stroke-to-fill expansion helper mirroring Skia's SkStroke::strokePath. Given a stroked path plus width + cap + join, produces a closed fillable outline that, when filled, approximates the original stroked pixels.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Stroke Expansion Specification

Tests for expand_stroke — the stroke-to-fill expansion helper mirroring Skia's SkStroke::strokePath. Given a stroked path plus width + cap + join, produces a closed fillable outline that, when filled, approximates the original stroked pixels.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-STROKE-EXPAND |
| Category | Stdlib |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/unit/lib/skia/stroke_expand_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for expand_stroke — the stroke-to-fill expansion helper mirroring
Skia's SkStroke::strokePath. Given a stroked path plus width + cap + join,
produces a closed fillable outline that, when filled, approximates the
original stroked pixels.

These tests avoid asserting exact vertex coordinates (which depend on the
join/cap polyline tessellation choices) and instead validate geometry via
SkPath.contains() point queries plus bounding-box comparisons.

## Scenarios

### stroke_expand

#### expand_stroke: width 0 produces empty-ish path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- expand_stroke: width 0 produces empty-ish path
   - Expected: out.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_stroke: width 0 produces empty-ish path")
val input = sk_path_new().move_to(0.0, 0.0).line_to(10.0, 0.0)
val params = stroke_params_new(0.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val out = expand_stroke(input, params)
# Width <= 0 short-circuits to an empty path.
expect(out.is_empty()).to_equal(true)
```

</details>

#### expand_stroke: single horizontal line with Butt caps produces a rectangle

- expand_stroke: single horizontal line with Butt caps produces a rectangle
   - Expected: out contains `10.0, 10.0`
   - Expected: out does not contain `10.0, 20.0`
   - Expected: out does not contain `-5.0, 10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_stroke: single horizontal line with Butt caps produces a rectangle")
# Line from (0, 10) to (20, 10), width 4 -> expected filled rect (0,8,20,12).
val input = sk_path_new().move_to(0.0, 10.0).line_to(20.0, 10.0)
val params = stroke_params_new(4.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val out = expand_stroke(input, params)
# A point on the centerline must be inside.
expect(out.contains(10.0, 10.0)).to_equal(true)
# A point just outside the stroke band (y > 12) must be outside.
expect(out.contains(10.0, 20.0)).to_equal(false)
# A point well before the start cap (x < 0) must be outside.
expect(out.contains(-5.0, 10.0)).to_equal(false)
```

</details>

#### expand_stroke: right-angle L-shape with Miter join extends to the corner

- expand_stroke: right-angle L-shape with Miter join extends to the corner


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_stroke: right-angle L-shape with Miter join extends to the corner")
# L-shape: (0, 0) -> (10, 0) -> (10, 10), width 4.
# With a Miter join at (10, 0), the outside corner of the stroke
# should extend beyond the centerline corner into (12, -2) region.
val input = sk_path_new().move_to(0.0, 0.0).line_to(10.0, 0.0).line_to(10.0, 10.0)
val params = stroke_params_new(4.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val out = expand_stroke(input, params)
# The miter tip sits at roughly (12, -2).
val bounds = out.bounds()
# right edge should reach ~12 (stroke right side of vertical segment).
expect(bounds.right).to_be_greater_than(11.5)
```

</details>

#### expand_stroke: right-angle L-shape with Bevel join is shorter than Miter

- expand_stroke: right-angle L-shape with Bevel join is shorter than Miter


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_stroke: right-angle L-shape with Bevel join is shorter than Miter")
val input = sk_path_new().move_to(0.0, 0.0).line_to(10.0, 0.0).line_to(10.0, 10.0)
val miter_params = stroke_params_new(4.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val bevel_params = stroke_params_new(4.0, StrokeCap.Butt, StrokeJoin.Bevel, 4.0)
val miter_out = expand_stroke(input, miter_params)
val bevel_out = expand_stroke(input, bevel_params)
# The bevel outline's outer boundary is chamfered, so its outer corner
# does not reach as far as the miter tip. Verb count differs (bevel
# inserts one line_to for the chamfer; miter inserts two — miter tip + b).
val miter_verbs = miter_out.count_verbs()
val bevel_verbs = bevel_out.count_verbs()
expect(bevel_verbs).to_be_less_than(miter_verbs)
```

</details>

#### expand_stroke: closed square input produces a frame (outer + inner outlines)

- expand_stroke: closed square input produces a frame (outer + inner outlines)
   - Expected: out contains `5.0, 0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_stroke: closed square input produces a frame (outer + inner outlines)")
# Square (0,0)-(10,10), closed. Width 2.
# Expect an outer outline reaching ~(-1,-1)-(11,11) and an inner
# outline around (1,1)-(9,9). A point at the center (5,5) is NOT
# inside the stroke band (it's the interior hole); a point on an
# edge midline (5, 0) IS inside.
val input = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(10.0, 0.0)
    .line_to(10.0, 10.0)
    .line_to(0.0, 10.0)
    .close()
val params = stroke_params_new(2.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val out = expand_stroke(input, params)
# A point on the top edge centerline must be inside.
expect(out.contains(5.0, 0.0)).to_equal(true)
# The frame's outer bounds extend at least a half-width past the corner.
val bounds = out.bounds()
expect(bounds.right).to_be_greater_than(10.5)
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

- Canonical SPipe generation for source `7a8694371b3de13526a7dd1e668dc1053163435299fd144be13ed33ca697844a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a8694371b3de13526a7dd1e668dc1053163435299fd144be13ed33ca697844a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a8694371b3de13526a7dd1e668dc1053163435299fd144be13ed33ca697844a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/skia/stroke_expand_spec.spl
mirror: doc/06_spec/unit/lib/skia/stroke_expand_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/stroke_expand_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/stroke_expand_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/stroke_expand_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expand_stroke: width 0 produces empty-ish path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/stroke_expand_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expand_stroke: single horizontal line with Butt caps produces a rectangle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/stroke_expand_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expand_stroke: right-angle L-shape with Miter join extends to the corner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
