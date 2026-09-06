# Draw Ir Damage Plan Specification

> Tests covering DrawIR consumes the shared CPU/Vulkan damage plan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Damage Plan Specification

## Scenarios

### DrawIR consumes the shared CPU/Vulkan damage plan

#### REQ-201 REQ-203 clips a full-surface command to one local damage rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val damage = DirtyTilePyramid.create(128, 64, [64], [64])
damage.mark_rect(0, 0, 64, 64)
val plan = build_damage_frame_plan(damage, 0, 8, 100)
expect(plan.mode).to_equal(DAMAGE_PLAN_LOCAL)
var engine = Engine2D.create_with_backend(128, 64, "cpu")
engine.clear(BG)
val outcome = engine2d_draw_ir_render_damage_plan(
    engine, [draw_ir_rect("full", 0, 0, 128, 64, RED)], plan)
var rendered = outcome.engine
val pixels = rendered.read_pixels()
expect(outcome.rects_rendered).to_equal(1)
expect(pixels[0]).to_equal(RED)
expect(pixels[63]).to_equal(RED)
expect(pixels[64]).to_equal(BG)
expect(pixels[127]).to_equal(BG)
rendered.shutdown()
```

</details>

#### REQ-202 leaves an idle retained frame byte-identical without submit

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val damage = DirtyTilePyramid.create(64, 64, [64], [64])
val plan = build_damage_frame_plan(damage, 0, 8, 100)
expect(plan.mode).to_equal(DAMAGE_PLAN_NONE)
var engine = Engine2D.create_with_backend(64, 64, "cpu")
engine.clear(BG)
val outcome = engine2d_draw_ir_render_damage_plan(
    engine, [draw_ir_rect("full", 0, 0, 64, 64, RED)], plan)
var retained = outcome.engine
expect(outcome.rects_rendered).to_equal(0)
expect(outcome.ops_rendered).to_equal(0)
expect(outcome.submitted).to_equal(false)
expect(retained.read_pixels()[0]).to_equal(BG)
retained.shutdown()
```

</details>

#### REQ-201 REQ-203 replays two disjoint damage rects in one batch

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val damage = DirtyTilePyramid.create(192, 64, [64], [64])
damage.mark_rect(0, 0, 64, 64)
damage.mark_rect(128, 0, 64, 64)
val plan = build_damage_frame_plan(damage, 0, 8, 100)
var engine = Engine2D.create_with_backend(192, 64, "cpu")
engine.clear(BG)
val outcome = engine2d_draw_ir_render_damage_plan(
    engine, [draw_ir_rect("full", 0, 0, 192, 64, RED)], plan)
var rendered = outcome.engine
val pixels = rendered.read_pixels()
expect(outcome.rects_rendered).to_equal(2)
expect(pixels[0]).to_equal(RED)
expect(pixels[64]).to_equal(BG)
expect(pixels[128]).to_equal(RED)
rendered.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DrawIR consumes the shared CPU/Vulkan damage plan.
- DrawIR consumes the shared CPU/Vulkan damage plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2c70ea9a57083bbdacaa24cfeb4d4b9d620887bc19758af6c5930403e9b1ab32`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c70ea9a57083bbdacaa24cfeb4d4b9d620887bc19758af6c5930403e9b1ab32`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c70ea9a57083bbdacaa24cfeb4d4b9d620887bc19758af6c5930403e9b1ab32`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **81/100**; blockers: **0**.

SSpec documentization score: 81/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.md (current)
findings: 9 blockers: 0
  narrative=80 structure=70 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl:21:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-201 REQ-203 clips a full-surface command to one local damage rect' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl:39:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-202 leaves an idle retained frame byte-identical without submit' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_spec.spl:54:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-201 REQ-203 replays two disjoint damage rects in one batch' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
