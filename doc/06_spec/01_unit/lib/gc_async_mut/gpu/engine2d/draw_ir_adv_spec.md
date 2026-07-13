# Engine2D Draw IR Advanced Executor Specification

> This unit spec covers the Simple2D-facing Draw IR executor. It proves Draw IR batches and compositions choose the CPU fallback when GPU execution is unavailable, render supported rectangle commands into the Engine2D pixel buffer, skip unsupported future commands, and expose the same Draw IR batch through SGTTI before raster so semantic assertions and pixel readback are paired.

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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Draw IR Advanced Executor Specification

This unit spec covers the Simple2D-facing Draw IR executor. It proves Draw IR batches and compositions choose the CPU fallback when GPU execution is unavailable, render supported rectangle commands into the Engine2D pixel buffer, skip unsupported future commands, and expose the same Draw IR batch through SGTTI before raster so semantic assertions and pixel readback are paired.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md |
| Design | doc/04_architecture/ui/ui_test_architecture.md |
| Research | doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This unit spec covers the Simple2D-facing Draw IR executor. It proves Draw IR
batches and compositions choose the CPU fallback when GPU execution is
unavailable, render supported rectangle commands into the Engine2D pixel buffer,
skip unsupported future commands, and expose the same Draw IR batch through
SGTTI before raster so semantic assertions and pixel readback are paired.

## Evidence Model

The first scenario is the SGTTI Phase 5 gate: it builds a Draw IR batch, asserts
the pre-raster semantic node with `SgttiTestDriver`, then renders the same batch
through Engine2D and checks pixel output.

**Requirements:** N/A

This is implementation evidence for the active SGTTI and Draw IR plans rather
than a numbered product requirement.

**Plan:** doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md

**Design:** doc/04_architecture/ui/ui_test_architecture.md

**Research:** doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md

## Syntax

The spec uses normal `std.spec` scenarios. Assertions stay on the canonical
SPipe matcher set; SGTTI is used as a helper inside an `it` block, not as a
replacement test framework.

## Scenarios

### Engine2D advanced Draw IR executor

#### executes a Draw IR batch through the Simple2D advanced interface with embedding offsets

- var engine = Engine2D create with backend
- engine clear
- draw ir rect
   - Expected: semantic.check_exists("body").unwrap() is true
   - Expected: semantic.check_visible("body").unwrap() is true
   - Expected: body.kind equals `rect`
   - Expected: body.widget_id equals `body`
   - Expected: result.unit_id equals `batch-rect`
   - Expected: result.selected_backend equals `cpu`
   - Expected: result.fallback_required is true
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[8 * 32 + 6] equals `RED`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val embedding = draw_ir_embedding_config("surf1", "win1", 4, 5, 20, 16, 10, 1000, true)
val batch = draw_ir_batch("batch-rect", DRAW_IR_BACKEND_GPU, embedding, [
    draw_ir_rect("body", 2, 3, 6, 5, RED)
])

val semantic = SgttiTestDriver.new(sgtti_snapshot_from_draw_ir_batch(batch, 1000, 5000, 1000))
val body = semantic.get_element("body").unwrap()
expect(semantic.check_exists("body").unwrap()).to_equal(true)
expect(semantic.check_visible("body").unwrap()).to_equal(true)
expect(body.kind).to_equal("rect")
expect(body.widget_id).to_equal("body")

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

#### submits a GPU-selected Draw IR batch through the runtime host GPU queue

- engine2d host gpu runtime reset
- var engine = Engine2D create with backend
- engine clear
- draw ir rect
   - Expected: result.render.unit_id equals `runtime-batch-runtime`
   - Expected: result.render.selected_backend equals `gpu`
   - Expected: result.render.rendered_command_count equals `1`
   - Expected: result.runtime_submit.packet_id equals `1`
   - Expected: result.runtime_drain.drained equals `1`
   - Expected: result.runtime_drain.status equals `completed`
   - Expected: result.render.pixels[3 * 32 + 2] equals `GREEN`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
engine2d_host_gpu_runtime_reset()
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("batch-runtime", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 0, 0, 20, 16, 10, 1000, false), [
    draw_ir_rect("body", 2, 3, 6, 5, GREEN)
])
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 7, 7, true, 4096)

val result = engine2d_draw_ir_adv_batch_runtime_queue(engine, batch, true, queue)

expect(result.render.unit_id).to_equal("runtime-batch-runtime")
expect(result.render.selected_backend).to_equal("gpu")
expect(result.render.rendered_command_count).to_equal(1)
expect(result.runtime_submit.submitted).to_be(true)
expect(result.runtime_submit.packet_id).to_equal(1)
expect(result.runtime_drain.drained).to_equal(1)
expect(result.runtime_drain.status).to_equal("completed")
expect(result.queued_for_gpu).to_be(true)
expect(result.render.pixels[3 * 32 + 2]).to_equal(GREEN)
engine.shutdown()
```

</details>

#### executes a composed Draw IR scene in batch order

- var engine = Engine2D create with backend
- engine clear
- draw ir rect
- draw ir rect
   - Expected: result.unit_id equals `wm-composite`
   - Expected: result.rendered_command_count equals `2`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[1 * 32 + 1] equals `RED`
   - Expected: result.pixels[8 * 32 + 7] equals `GREEN`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

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

- var engine = Engine2D create with backend
- engine clear
   - Expected: result.rendered_command_count equals `0`
   - Expected: result.skipped_command_count equals `1`
   - Expected: result.pixels[1 * 16 + 1] equals `BG`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

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

#### preflights a composition before any supported command can paint

<details>
<summary>Executable SSpec</summary>

```simple
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(BG)
val unsupported = DrawIrCommand(kind: "future-path", component_id: "path", x: 1, y: 1, width: 5, height: 5, color: RED, text_value: "", border_rect: draw_ir_no_rect(), content_rect: draw_ir_no_rect(), hit_rect: draw_ir_no_rect(), clip_rect: draw_ir_no_rect(), computed_style: [], edge: nil, parent_id: "", image_uri: "", points: [])
val batch = draw_ir_batch("transactional", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 16, 16, 1, 1000, false), [draw_ir_rect("would-paint", 0, 0, 16, 16, RED), unsupported])
val composition = draw_ir_composition("transactional", "scene", DRAW_IR_BACKEND_GPU, [batch])
val result = engine2d_draw_ir_adv_composition(engine, composition, false)
expect(result.rendered_command_count).to_equal(0)
expect(result.skipped_command_count).to_equal(1)
expect(result.pixels[0]).to_equal(BG)
engine.shutdown()
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


## Related Documentation

- **Plan:** [doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md](doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md)
- **Design:** [doc/04_architecture/ui/ui_test_architecture.md](doc/04_architecture/ui/ui_test_architecture.md)
- **Research:** [doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md](doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md)


</details>
