# Skia Stroke Dash Specification

> Tests for dash_path and DashPattern — the stroke-dashing helpers mirroring Skia's SkDashPathEffect. A dash pattern alternates on/off intervals along the arc length of a flattened path; this spec validates that the output path contains the expected number of Move/Line verb pairs for representative patterns.

<!-- sdn-diagram:id=stroke_dash_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stroke_dash_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stroke_dash_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stroke_dash_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Stroke Dash Specification

Tests for dash_path and DashPattern — the stroke-dashing helpers mirroring Skia's SkDashPathEffect. A dash pattern alternates on/off intervals along the arc length of a flattened path; this spec validates that the output path contains the expected number of Move/Line verb pairs for representative patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-STROKE-DASH |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/stroke_dash_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for dash_path and DashPattern — the stroke-dashing helpers mirroring
Skia's SkDashPathEffect. A dash pattern alternates on/off intervals along
the arc length of a flattened path; this spec validates that the output
path contains the expected number of Move/Line verb pairs for representative
patterns.

## Scenarios

### stroke_dash

#### dash_path: uniform dash on a long horizontal line produces N sub-segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Line of length 100, pattern [10 on, 10 off] -> expect 5 on-sub-segments.
val input = sk_path_new().move_to(0.0, 0.0).line_to(100.0, 0.0)
val pat = dash_pattern_new([10.0, 10.0], 0.0)
val out = dash_path(input, pat)
# Each on-sub-segment contributes one Move + one Line verb = 2 verbs.
# 5 on-intervals -> 10 verbs.
val verbs = out.count_verbs()
expect(verbs).to_equal(10)
```

</details>

#### dash_path: zero-length phase preserves dash alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = sk_path_new().move_to(0.0, 0.0).line_to(40.0, 0.0)
val pat_a = dash_pattern_new([10.0, 10.0], 0.0)
val pat_b = dash_pattern_new([10.0, 10.0], 0.0)
val out_a = dash_path(input, pat_a)
val out_b = dash_path(input, pat_b)
expect(out_a.count_verbs()).to_equal(out_b.count_verbs())
expect(out_a.count_verbs()).to_be_greater_than(0)
```

</details>

#### dash_path: pattern [10, 0] (all-on) produces the original line length worth of draws

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Off-interval of 0 means every tick flips pattern back to on,
# so the output should cover the full length and have at least one
# Move+Line emitted.
val input = sk_path_new().move_to(0.0, 0.0).line_to(30.0, 0.0)
val pat = dash_pattern_new([10.0, 0.0], 0.0)
val out = dash_path(input, pat)
val verbs = out.count_verbs()
expect(verbs).to_be_greater_than(0)
# All emitted pairs must be Move+Line, so verb count is even.
val even = (verbs % 2) == 0
expect(even).to_equal(true)
```

</details>

#### dash_path: pattern [0, 10] (all-off) produces empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = sk_path_new().move_to(0.0, 0.0).line_to(50.0, 0.0)
val pat = dash_pattern_new([0.0, 10.0], 0.0)
val out = dash_path(input, pat)
expect(out.is_empty()).to_equal(true)
```

</details>

#### dash_path: empty input path produces empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = sk_path_new()
val pat = dash_pattern_new([5.0, 5.0], 0.0)
val out = dash_path(input, pat)
expect(out.is_empty()).to_equal(true)
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
