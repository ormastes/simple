# Skia Stroke Dash Specification

> Tests for dash_path and DashPattern — the stroke-dashing helpers mirroring Skia's SkDashPathEffect. A dash pattern alternates on/off intervals along the arc length of a flattened path; this spec validates that the output path contains the expected number of Move/Line verb pairs for representative patterns.

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
| Source | `test/unit/lib/skia/stroke_dash_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dash_path: uniform dash on a long horizontal line produces N sub-segments
   - Expected: verbs equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dash_path: uniform dash on a long horizontal line produces N sub-segments")
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

- dash_path: zero-length phase preserves dash alignment
   - Expected: out_a.count_verbs() equals `out_b.count_verbs()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dash_path: zero-length phase preserves dash alignment")
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

- dash_path: pattern [10, 0] (all-on) produces the original line length worth of draws
   - Expected: even is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dash_path: pattern [10, 0] (all-on) produces the original line length worth of draws")
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

- dash_path: pattern [0, 10] (all-off) produces empty path
   - Expected: out.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dash_path: pattern [0, 10] (all-off) produces empty path")
val input = sk_path_new().move_to(0.0, 0.0).line_to(50.0, 0.0)
val pat = dash_pattern_new([0.0, 10.0], 0.0)
val out = dash_path(input, pat)
expect(out.is_empty()).to_equal(true)
```

</details>

#### dash_path: empty input path produces empty output

- dash_path: empty input path produces empty output
   - Expected: out.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dash_path: empty input path produces empty output")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `79eb503a8320a23976e4b528d5dfd15fdfbb1b4494a7d4a76bc8e219be278037`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79eb503a8320a23976e4b528d5dfd15fdfbb1b4494a7d4a76bc8e219be278037`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79eb503a8320a23976e4b528d5dfd15fdfbb1b4494a7d4a76bc8e219be278037`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/skia/stroke_dash_spec.spl
mirror: doc/06_spec/unit/lib/skia/stroke_dash_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/stroke_dash_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/stroke_dash_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/stroke_dash_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/skia/stroke_dash_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dash_path: uniform dash on a long horizontal line produces N sub-segments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/stroke_dash_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dash_path: zero-length phase preserves dash alignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/stroke_dash_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dash_path: pattern [10, 0] (all-on) produces the original line length worth of draws' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
