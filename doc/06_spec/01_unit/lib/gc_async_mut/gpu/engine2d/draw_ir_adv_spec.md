# Draw Ir Adv Specification

> 1. var engine = Engine2D create with backend

<!-- sdn-diagram:id=draw_ir_adv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_adv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_adv_spec -> std
draw_ir_adv_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_ir_adv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Adv Specification

## Scenarios

### Engine2D advanced Draw IR executor

#### executes a Draw IR batch through the Simple2D advanced interface with embedding offsets

1. var engine = Engine2D create with backend

2. engine clear

3. draw ir rect
   - Expected: result.unit_id equals `batch-rect`
   - Expected: result.selected_backend equals `cpu`
   - Expected: result.fallback_required is true
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[8 * 32 + 6] equals `RED`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val embedding = draw_ir_embedding_config("surf1", "win1", 4, 5, 20, 16, 10, 1000, true)
val batch = draw_ir_batch("batch-rect", DRAW_IR_BACKEND_GPU, embedding, [
    draw_ir_rect("body", 2, 3, 6, 5, RED)
])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.unit_id).to_equal("batch-rect")
expect(result.selected_backend).to_equal("cpu")
expect(result.fallback_required).to_equal(true)
expect(result.fallback_reason).to_contain("gpu backend unavailable")
expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels[8 * 32 + 6]).to_equal(RED)
engine.shutdown()
```

</details>

#### executes a composed Draw IR scene in batch order

1. var engine = Engine2D create with backend

2. engine clear

3. draw ir rect

4. draw ir rect
   - Expected: result.unit_id equals `wm-composite`
   - Expected: result.rendered_command_count equals `2`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[1 * 32 + 1] equals `RED`
   - Expected: result.pixels[8 * 32 + 7] equals `GREEN`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val desktop = draw_ir_batch("desktop", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("wm", "desktop", 0, 0, 32, 24, 0, 1000, false), [
    draw_ir_rect("bg", 0, 0, 32, 24, RED)
])
val window = draw_ir_batch("window", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 6, 7, 12, 10, 10, 1000, true), [
    draw_ir_rect("body", 0, 0, 4, 4, GREEN)
])
val composition = draw_ir_composition("wm-composite", "scene-key", DRAW_IR_BACKEND_GPU, [desktop, window])

val result = engine2d_draw_ir_adv_composition(engine, composition, false)

expect(result.unit_id).to_equal("wm-composite")
expect(result.rendered_command_count).to_equal(2)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels[1 * 32 + 1]).to_equal(RED)
expect(result.pixels[8 * 32 + 7]).to_equal(GREEN)
engine.shutdown()
```

</details>

#### reports unsupported Draw IR commands without rendering them

1. var engine = Engine2D create with backend

2. engine clear
   - Expected: result.rendered_command_count equals `0`
   - Expected: result.skipped_command_count equals `1`
   - Expected: result.pixels[1 * 16 + 1] equals `BG`

3. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(BG)
val unsupported = DrawIrCommand(kind: "future-path", component_id: "path", x: 1, y: 1, width: 5, height: 5, color: RED, text_value: "", border_rect: draw_ir_no_rect(), content_rect: draw_ir_no_rect(), hit_rect: draw_ir_no_rect(), clip_rect: draw_ir_no_rect(), computed_style: [], edge: nil, parent_id: "", image_uri: "", points: [])
val batch = draw_ir_batch("unsupported", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 16, 16, 1, 1000, false), [unsupported])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(0)
expect(result.skipped_command_count).to_equal(1)
expect(result.pixels[1 * 16 + 1]).to_equal(BG)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D advanced Draw IR executor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
