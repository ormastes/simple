# Damage Plan Specification

> Tests covering shared CPU/Vulkan damage-frame planning, SABOTAGE: local damage plans never omit or widen tile coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Damage Plan Specification

## Scenarios

### shared CPU/Vulkan damage-frame planning

#### REQ-101 REQ-105 returns an empty receipt for an idle frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = plan(grid(256, 256, 64))
expect(p.mode).to_equal(DAMAGE_PLAN_NONE)
expect(p.rects.len()).to_equal(0)
expect(p.source_tile_count).to_equal(0)
expect(p.tiles_examined).to_equal(0)
```

</details>

#### REQ-101 REQ-102 merges three horizontal tiles into one exact rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = grid(256, 128, 64)
d.mark_rect(0, 0, 192, 64)
val p = plan(d)
expect(p.mode).to_equal(DAMAGE_PLAN_LOCAL)
expect(p.rects).to_equal([0, 0, 192, 64])
expect(p.source_tile_count).to_equal(3)
expect(p.output_rect_count).to_equal(1)
expect(p.merged_tile_count).to_equal(2)
expect(p.planned_pixels).to_equal(p.dirty_pixels)
```

</details>

#### REQ-102 merges a solid two-by-three tile block vertically

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = grid(256, 256, 64)
d.mark_rect(64, 0, 128, 192)
val p = plan(d)
expect(p.rects).to_equal([64, 0, 128, 192])
expect(p.source_tile_count).to_equal(6)
expect(p.output_rect_count).to_equal(1)
```

</details>

#### REQ-102 merges both separated columns instead of only the last run

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = grid(256, 128, 64)
d.mark_rect(0, 0, 64, 128)
d.mark_rect(192, 0, 64, 128)
val p = plan(d)
expect(p.rects).to_equal([0, 0, 64, 128, 192, 0, 64, 128])
expect(p.output_rect_count).to_equal(2)
```

</details>

#### REQ-102 does not merge or widen when the next row run changes shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = grid(256, 128, 64)
d.mark_rect(0, 0, 128, 64)
d.mark_rect(0, 64, 64, 64)
val p = plan(d)
expect(p.rects).to_equal([0, 0, 128, 64, 0, 64, 64, 64])
expect(p.planned_pixels).to_equal(12288)
```

</details>

#### REQ-101 is deterministic regardless of first-mark order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = grid(256, 128, 64)
a.mark_rect(192, 64, 64, 64)
a.mark_rect(0, 0, 64, 64)
val b = grid(256, 128, 64)
b.mark_rect(0, 0, 64, 64)
b.mark_rect(192, 64, 64, 64)
expect(plan(a).rects).to_equal(plan(b).rects)
```

</details>

#### REQ-104 clips the ragged 8K bottom-right CPU tile

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = grid(7680, 4320, 64)
d.mark_rect(7679, 4319, 1, 1)
val p = plan(d)
expect(p.rects).to_equal([7616, 4288, 64, 32])
expect(p.dirty_pixels).to_equal(2048)
```

</details>

#### REQ-103 REQ-104 falls back at exact area threshold using i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = grid(7680, 4320, 64)
d.mark_rect(0, 0, 7680, 2592)
val p = plan(d, 10000, 60)
expect(p.mode).to_equal(DAMAGE_PLAN_FULL)
expect(p.fallback_reason).to_equal(DAMAGE_FALLBACK_AREA)
expect(p.rects).to_equal([0, 0, 7680, 4320])
expect(p.planned_pixels).to_equal(33177600)
```

</details>

#### REQ-103 keeps exactly-cap local and makes cap-plus-one full

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exact = grid(320, 64, 64)
exact.mark_rect(0, 0, 64, 64)
exact.mark_rect(128, 0, 64, 64)
expect(plan(exact, 2, 100).mode).to_equal(DAMAGE_PLAN_LOCAL)
val over = grid(320, 64, 64)
over.mark_rect(0, 0, 64, 64)
over.mark_rect(128, 0, 64, 64)
over.mark_rect(256, 0, 64, 64)
val p = plan(over, 2, 100)
expect(p.mode).to_equal(DAMAGE_PLAN_FULL)
expect(p.fallback_reason).to_equal(DAMAGE_FALLBACK_CAP)
expect(p.rects).to_equal([0, 0, 320, 64])
expect(p.full_fallback_count).to_equal(1)
```

</details>

#### REQ-103 fails closed to full viewport for invalid policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = grid(256, 256, 64)
d.mark_rect(0, 0, 64, 64)
val p = plan(d, 0, 60)
expect(p.mode).to_equal(DAMAGE_PLAN_FULL)
expect(p.fallback_reason).to_equal(DAMAGE_FALLBACK_INVALID)
expect(p.rects).to_equal([0, 0, 256, 256])
```

</details>

### SABOTAGE: local damage plans never omit or widen tile coverage

#### REQ-102 planned pixels equal the exact disjoint dirty-tile union

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = grid(256, 256, 64)
d.mark_rect(0, 0, 64, 64)
d.mark_rect(128, 128, 64, 64)
val p = plan(d)
expect(p.mode).to_equal(DAMAGE_PLAN_LOCAL)
expect(p.dirty_pixels).to_equal(8192)
expect(p.planned_pixels).to_equal(8192)
assert_true(p.planned_pixels != 4096)
assert_true(p.planned_pixels != 16384)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering shared CPU/Vulkan damage-frame planning, SABOTAGE: local damage plans never omit or widen tile coverage.
- shared CPU/Vulkan damage-frame planning
- SABOTAGE: local damage plans never omit or widen tile coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3e5ded3bc7458f58f24941d67e319f1518e9d317329d99a57221ccf1d86098f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3e5ded3bc7458f58f24941d67e319f1518e9d317329d99a57221ccf1d86098f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3e5ded3bc7458f58f24941d67e319f1518e9d317329d99a57221ccf1d86098f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **79/100**; blockers: **0**.

SSpec documentization score: 79/100
source: test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/render_opt/damage_plan_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/render_opt/damage_plan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/render_opt/damage_plan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl:26:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-101 REQ-105 returns an empty receipt for an idle frame' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl:33:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-101 REQ-102 merges three horizontal tiles into one exact rect' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl:44:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-102 merges a solid two-by-three tile block vertically' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/render_opt/damage_plan_spec.spl:52:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-102 merges both separated columns instead of only the last run' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
