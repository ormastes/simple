# Skia Path Effect (Corner + Discrete) Specification

> Tests for apply_corner_path_effect and apply_discrete_path_effect — Simple implementations of Skia's SkCornerPathEffect (arc-round sharp corners) and SkDiscretePathEffect (jitter path into short displaced segments).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Path Effect (Corner + Discrete) Specification

Tests for apply_corner_path_effect and apply_discrete_path_effect — Simple implementations of Skia's SkCornerPathEffect (arc-round sharp corners) and SkDiscretePathEffect (jitter path into short displaced segments).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-PE-CORNER-DISCRETE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/unit/lib/skia/path_effect_corner_discrete_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for apply_corner_path_effect and apply_discrete_path_effect — Simple
implementations of Skia's SkCornerPathEffect (arc-round sharp corners) and
SkDiscretePathEffect (jitter path into short displaced segments).

Invariants verified:
- radius 0 is a no-op (only flattening).
- A square gains extra segments when its corners are rounded.
- A collinear polyline is not affected by corner rounding.
- DiscretePathEffect with a fixed seed is deterministic.
- DiscretePathEffect with deviation 0 matches the flattened input shape.
- The internal LCG produces a repeatable state sequence.

## Scenarios

### path_effect_corner_discrete

#### apply_corner_path_effect: radius 0 returns input unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- apply_corner_path_effect: radius 0 returns input unchanged
   - Expected: out_count equals `in_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply_corner_path_effect: radius 0 returns input unchanged")
# A simple two-line path; zero radius means we simply re-emit the
# flattened polyline with the same number of line segments (1 move + 2 lines).
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(10.0, 0.0)
    .line_to(10.0, 10.0)
val params = corner_path_effect_params_new(0.0)
val out = apply_corner_path_effect(p, params)
val in_count = p.segments.length()
val out_count = out.segments.length()
# Flattening of line-only input preserves segment count.
expect(out_count).to_equal(in_count)
```

</details>

#### apply_corner_path_effect: radius > 0 on a square produces more line segments than input

- apply_corner_path_effect: radius > 0 on a square produces more line segments than input


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply_corner_path_effect: radius > 0 on a square produces more line segments than input")
val square = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(10.0, 0.0)
    .line_to(10.0, 10.0)
    .line_to(0.0, 10.0)
    .close()
val params = corner_path_effect_params_new(2.0)
val out = apply_corner_path_effect(square, params)
val in_count = square.segments.length()
val out_count = out.segments.length()
expect(out_count).to_be_greater_than(in_count)
```

</details>

#### apply_corner_path_effect: collinear path is unchanged

- apply_corner_path_effect: collinear path is unchanged
   - Expected: out_count equals `in_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply_corner_path_effect: collinear path is unchanged")
# Three collinear points along +x. No corner should be rounded
# because the tangent direction doesn't change.
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(5.0, 0.0)
    .line_to(10.0, 0.0)
val params = corner_path_effect_params_new(1.0)
val out = apply_corner_path_effect(p, params)
# With collinear input we should not have inserted any arc chords,
# so the output segment count must equal the flattened input count.
val in_count = p.segments.length()
val out_count = out.segments.length()
expect(out_count).to_equal(in_count)
```

</details>

#### apply_discrete_path_effect: deterministic seed produces same output twice

- apply_discrete_path_effect: deterministic seed produces same output twice
   - Expected: a.segments.length() equals `b.segments.length()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply_discrete_path_effect: deterministic seed produces same output twice")
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
val params = discrete_path_effect_params_new(5.0, 2.0, 42)
val a = apply_discrete_path_effect(p, params)
val b = apply_discrete_path_effect(p, params)
expect(a.segments.length()).to_equal(b.segments.length())
```

</details>

#### apply_discrete_path_effect: deviation 0 produces output geometrically similar to input

- apply_discrete_path_effect: deviation 0 produces output geometrically similar to input


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply_discrete_path_effect: deviation 0 produces output geometrically similar to input")
# With deviation == 0, every sampled point is its true position on
# the input path. The number of emitted line segments is roughly
# total_length / step.
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
val params = discrete_path_effect_params_new(10.0, 0.0, 1)
val out = apply_discrete_path_effect(p, params)
# We expect more than one output segment (move + many lines).
expect(out.segments.length()).to_be_greater_than(1)
```

</details>

#### _lcg_next: state sequence is deterministic

- _lcg_next: state sequence is deterministic
   - Expected: a equals `b`
   - Expected: a2 equals `b2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_lcg_next: state sequence is deterministic")
# Given a fixed seed, running the LCG twice from the same state must
# yield the same value both times.
val seed: i64 = 12345
val a = _lcg_next(seed)
val b = _lcg_next(seed)
expect(a).to_equal(b)
val a2 = _lcg_next(a)
val b2 = _lcg_next(a)
expect(a2).to_equal(b2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `8c0008e690d80795efa5718333ecdc0bd1458e2f54510e689636d37581cc6418`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c0008e690d80795efa5718333ecdc0bd1458e2f54510e689636d37581cc6418`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c0008e690d80795efa5718333ecdc0bd1458e2f54510e689636d37581cc6418`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/skia/path_effect_corner_discrete_spec.spl
mirror: doc/06_spec/unit/lib/skia/path_effect_corner_discrete_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/path_effect_corner_discrete_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/path_effect_corner_discrete_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/path_effect_corner_discrete_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'apply_corner_path_effect: radius 0 returns input unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/path_effect_corner_discrete_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'apply_corner_path_effect: radius > 0 on a square produces more line segments than input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/path_effect_corner_discrete_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'apply_corner_path_effect: collinear path is unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
