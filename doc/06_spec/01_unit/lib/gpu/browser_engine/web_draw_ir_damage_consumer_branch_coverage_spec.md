# Web DrawIR Damage Consumer — Branch Coverage Specification

> Drives `web_draw_ir_consume_damage` through both outcomes of each decision: retained NONE no-op vs full replan, LOCAL replay acceptance vs full fallback (unstable resources, unstable viewport, changed batch metadata), and the GPU-backend selection predicate. Every scenario asserts concrete effective plan modes, rects, and reasons.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web DrawIR Damage Consumer — Branch Coverage Specification

Drives `web_draw_ir_consume_damage` through both outcomes of each decision: retained NONE no-op vs full replan, LOCAL replay acceptance vs full fallback (unstable resources, unstable viewport, changed batch metadata), and the GPU-backend selection predicate. Every scenario asserts concrete effective plan modes, rects, and reasons.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/browser_engine/web_draw_ir_damage_consumer_branch_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Drives `web_draw_ir_consume_damage` through both outcomes of each decision:
retained NONE no-op vs full replan, LOCAL replay acceptance vs full
fallback (unstable resources, unstable viewport, changed batch metadata),
and the GPU-backend selection predicate. Every scenario asserts concrete
effective plan modes, rects, and reasons.

## Scenarios

### web_draw_ir_consume_damage branch coverage

#### keeps a retained NONE plan when compositions are identical and stable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a retained NONE plan when compositions are identical and stable


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a retained NONE plan when compositions are identical and stable")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val current = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val out = web_draw_ir_consume_damage(
    engine, prior, current, _images(), true, true)
expect out.effective_plan_mode == DAMAGE_PLAN_NONE
expect out.effective_plan_rects.len() == 0
expect out.reason == "composition-patch-empty"
expect out.result.fallback_required == false
# NONE is a retained no-op: no render, no readback.
expect out.result.rendered_command_count == 0
expect out.result.pixels.len() == 0
expect out.result.readback_source == "retained_none"
out.engine.shutdown()
```

</details>

#### executes a LOCAL clipped replay when one rect moves

- executes a LOCAL clipped replay when one rect moves


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a LOCAL clipped replay when one rect moves")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = _comp("c1", "scene", 4, 4, BOX)
val current = _comp("c1", "scene", 20, 12, BOX)
val seeded = _seed(engine, prior)
val out = web_draw_ir_consume_damage(
    seeded, prior, current, _images(), true, true)
expect out.effective_plan_mode == DAMAGE_PLAN_LOCAL
expect out.effective_plan_rects.len() > 0
expect out.effective_plan_rects.len() % 4 == 0
expect out.result.fallback_required == false
expect out.result.rendered_command_count >= 1
expect out.result.pixels.len() == (W * H).to_i64()
# new box position is painted
expect _px(out.result.pixels, 22, 14) == BOX
# old box position is repainted with the background
expect _px(out.result.pixels, 5, 5) == BG
# unchanged exterior pixels are preserved from the prior render
expect _px(out.result.pixels, 50, 40) == BG
expect _px(out.result.pixels, 0, 0) == BG
out.engine.shutdown()
```

</details>

#### executes a LOCAL replay when a rect is recolored in place

- executes a LOCAL replay when a rect is recolored in place


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a LOCAL replay when a rect is recolored in place")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = _comp("c1", "scene", 4, 4, BOX)
val current = _comp("c1", "scene", 4, 4, 0xfff04020u32)
val seeded = _seed(engine, prior)
val out = web_draw_ir_consume_damage(
    seeded, prior, current, _images(), true, true)
expect out.effective_plan_mode == DAMAGE_PLAN_LOCAL
expect out.effective_plan_rects.len() >= 4
# recolored box pixels updated in place
expect _px(out.result.pixels, 5, 5) == 0xfff04020u32
# unchanged exterior preserved
expect _px(out.result.pixels, 50, 40) == BG
out.engine.shutdown()
```

</details>

#### fails closed to FULL when resources are unstable

- fails closed to FULL when resources are unstable


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed to FULL when resources are unstable")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val current = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val out = web_draw_ir_consume_damage(
    engine, prior, current, _images(), true, false)
expect out.effective_plan_mode == DAMAGE_PLAN_FULL
expect out.reason == "resources-changed"
expect out.effective_plan_rects == [0, 0, W.to_i64(), H.to_i64()]
expect out.result.pixels.len() == (W * H).to_i64()
out.engine.shutdown()
```

</details>

#### fails closed to FULL when the viewport is unstable

- fails closed to FULL when the viewport is unstable


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed to FULL when the viewport is unstable")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val current = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val out = web_draw_ir_consume_damage(
    engine, prior, current, _images(), false, true)
expect out.effective_plan_mode == DAMAGE_PLAN_FULL
expect out.reason == "viewport-changed"
expect out.effective_plan_rects == [0, 0, W.to_i64(), H.to_i64()]
out.engine.shutdown()
```

</details>

#### fails closed to FULL when batch metadata changes

- fails closed to FULL when batch metadata changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed to FULL when batch metadata changes")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val current = draw_ir_composition(
    "c1", "scene", DRAW_IR_BACKEND_CPU,
    [draw_ir_batch(
        "b0", DRAW_IR_BACKEND_CPU,
        draw_ir_embedding_config(
            "surface", "root", 0, 0, W, H, 1, 900, true),
        [draw_ir_rect("box", 4, 4, 8, 8, 0xff2040f0u32)])])
val out = web_draw_ir_consume_damage(
    engine, prior, current, _images(), true, true)
expect out.effective_plan_mode == DAMAGE_PLAN_FULL
expect out.reason == "batch-metadata-changed"
expect out.effective_plan_rects == [0, 0, W.to_i64(), H.to_i64()]
out.engine.shutdown()
```

</details>

#### replans FULL when a batch is added to the composition

- replans FULL when a batch is added to the composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replans FULL when a batch is added to the composition")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val extra = draw_ir_batch(
    "b1", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "root2", 0, 0, W, H, 0, 1000, false),
    [draw_ir_rect("box2", 30, 30, 8, 8, 0xff00ff00u32)])
val cbatch = draw_ir_batch(
    "b0", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "root", 0, 0, W, H, 0, 1000, false),
    [draw_ir_rect("box", 4, 4, 8, 8, 0xff2040f0u32)])
val current = draw_ir_composition(
    "c1", "scene", DRAW_IR_BACKEND_CPU, [cbatch, extra])
val out = web_draw_ir_consume_damage(
    engine, prior, current, _images(), true, true)
expect out.effective_plan_mode == DAMAGE_PLAN_FULL
expect out.effective_plan_rects == [0, 0, W.to_i64(), H.to_i64()]
out.engine.shutdown()
```

</details>

#### consumes damage on a non-cpu backend selection path

- consumes damage on a non-cpu backend selection path


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("consumes damage on a non-cpu backend selection path")
var engine = Engine2D.create_with_backend(W, H, "software")
val prior = _comp("c1", "scene", 4, 4, BOX)
val current = _comp("c1", "scene", 12, 4, BOX)
val seeded = _seed(engine, prior)
val out = web_draw_ir_consume_damage(
    seeded, prior, current, _images(), true, true)
expect out.effective_plan_mode == DAMAGE_PLAN_LOCAL
expect out.result.pixels.len() == (W * H).to_i64()
# moved box painted at new x, old x repainted with background
expect _px(out.result.pixels, 13, 5) == BOX
expect _px(out.result.pixels, 5, 5) == BG
# unchanged exterior preserved from the prior render
expect _px(out.result.pixels, 50, 40) == BG
out.engine.shutdown()
```

</details>

#### handles an empty prior against a populated current

- handles an empty prior against a populated current


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles an empty prior against a populated current")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = draw_ir_composition(
    "c1", "scene", DRAW_IR_BACKEND_CPU, [])
val current = _comp("c1", "scene", 4, 4, BOX)
val out = web_draw_ir_consume_damage(
    engine, prior, current, _images(), true, true)
# batch count changed (0 -> 1), so this is exactly the
# batch-metadata-changed FULL replan
expect out.effective_plan_mode == DAMAGE_PLAN_FULL
expect out.reason == "batch-metadata-changed"
expect out.result.pixels.len() == (W * H).to_i64()
expect _px(out.result.pixels, 5, 5) == BOX
expect _px(out.result.pixels, 50, 40) == BG
out.engine.shutdown()
```

</details>

#### rejects LOCAL replay for a translucent batch and fails to FULL

- rejects LOCAL replay for a translucent batch and fails to FULL


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects LOCAL replay for a translucent batch and fails to FULL")
var engine = Engine2D.create_with_backend(W, H, "cpu")
fn tcomp(x: i32) -> DrawIrComposition:
    draw_ir_composition(
        "c1", "scene", DRAW_IR_BACKEND_CPU,
        [draw_ir_batch(
            "b0", DRAW_IR_BACKEND_CPU,
            draw_ir_embedding_config(
                "surface", "root", 0, 0, W, H, 0, 900, false),
            [draw_ir_rect("bg", 0, 0, W, H, 0xff101010u32),
             draw_ir_rect("box", x, 4, 8, 8, 0xff2040f0u32)])])
val out = web_draw_ir_consume_damage(
    engine, tcomp(4), tcomp(20), _images(), true, true)
expect out.effective_plan_mode == DAMAGE_PLAN_FULL
expect out.reason.contains("fresh-device")
expect out.effective_plan_rects == [0, 0, W.to_i64(), H.to_i64()]
out.engine.shutdown()
```

</details>

#### publishes an empty FULL plan on a zero-size viewport

- publishes an empty FULL plan on a zero-size viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes an empty FULL plan on a zero-size viewport")
var engine = Engine2D.create_with_backend(0, 0, "cpu")
val prior = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val current = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val out = web_draw_ir_consume_damage(
    engine, prior, current, _images(), true, true)
expect out.effective_plan_mode == DAMAGE_PLAN_FULL
expect out.reason == "invalid-viewport"
expect out.effective_plan_rects.len() == 0
out.engine.shutdown()
```

</details>

#### removing the only command yields a concrete non-NONE plan

- removing the only command yields a concrete non-NONE plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removing the only command yields a concrete non-NONE plan")
var engine = Engine2D.create_with_backend(W, H, "cpu")
val prior = _comp("c1", "scene", 4, 4, 0xff2040f0u32)
val current = draw_ir_composition(
    "c1", "scene", DRAW_IR_BACKEND_CPU,
    [draw_ir_batch(
        "b0", DRAW_IR_BACKEND_CPU,
        draw_ir_embedding_config(
            "surface", "root", 0, 0, W, H, 0, 1000, false),
        [])])
val out = web_draw_ir_consume_damage(
    engine, prior, current, _images(), true, true)
expect out.effective_plan_mode != DAMAGE_PLAN_NONE
expect out.effective_plan_rects.len() >= 4
out.engine.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `cb00e903715db89a95290be2d633c440b24c1d2f8efa2839587a1ae2c52db693`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb00e903715db89a95290be2d633c440b24c1d2f8efa2839587a1ae2c52db693`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb00e903715db89a95290be2d633c440b24c1d2f8efa2839587a1ae2c52db693`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/browser_engine/web_draw_ir_damage_consumer_branch_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/browser_engine/web_draw_ir_damage_consumer_branch_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/browser_engine/web_draw_ir_damage_consumer_branch_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/browser_engine/web_draw_ir_damage_consumer_branch_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/browser_engine/web_draw_ir_damage_consumer_branch_coverage_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a retained NONE plan when compositions are identical and stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/browser_engine/web_draw_ir_damage_consumer_branch_coverage_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a LOCAL clipped replay when one rect moves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/browser_engine/web_draw_ir_damage_consumer_branch_coverage_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a LOCAL replay when a rect is recolored in place' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
