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
| 7 | 7 | 0 | 0 |

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

1. var engine = Engine2D create with backend
2. engine clear
3. draw ir rect
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
4. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val embedding = draw_ir_embedding_config("surf1", "win1", 4, 5, 20, 16, 10, 1000, true)
val batch = draw_ir_batch("batch-rect", DRAW_IR_TEST_BACKEND_GPU, embedding, [
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
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val desktop = draw_ir_batch("desktop", DRAW_IR_TEST_BACKEND_GPU, draw_ir_embedding_config("wm", "desktop", 0, 0, 32, 24, 0, 1000, false), [
    draw_ir_rect("bg", 0, 0, 32, 24, RED)
])
val window = draw_ir_batch("window", DRAW_IR_TEST_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 6, 7, 12, 10, 10, 1000, true), [
    draw_ir_rect("body", 0, 0, 4, 4, GREEN)
])
val composition = draw_ir_composition("wm-composite", "scene-key", DRAW_IR_TEST_BACKEND_GPU, [desktop, window])

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
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(BG)
val unsupported = DrawIrCommand(kind: "future-path", component_id: "path", x: 1, y: 1, width: 5, height: 5, color: RED, text_value: "", border_rect: draw_ir_no_rect(), content_rect: draw_ir_no_rect(), hit_rect: draw_ir_no_rect(), clip_rect: draw_ir_no_rect(), computed_style: [], edge: nil, parent_id: "", image_uri: "", points: [])
val batch = draw_ir_batch("unsupported", DRAW_IR_TEST_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 16, 16, 1, 1000, false), [unsupported])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(0)
expect(result.skipped_command_count).to_equal(1)
expect(result.pixels[1 * 16 + 1]).to_equal(BG)
engine.shutdown()
```

</details>

#### renders Draw IR text with command font metadata and vector-font evidence

1. var engine = Engine2D create with backend
2. engine clear
3. border rect: draw ir no rect
4. content rect: draw ir no rect
5. hit rect: draw ir no rect
6. clip rect: draw ir no rect
7. draw ir style prop
8. draw ir style prop
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.text_command_count equals `1`
   - Expected: result.last_text_font_size equals `16`
   - Expected: result.font_offload_status equals `cpu-fallback`
   - Expected: result.font_offload_reason equals `production-gpu-dispatch-not-wired`
   - Expected: result.font_gpu_glyph_returned is false
   - Expected: result.font_production_ready is false
9. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(64, 32, "cpu")
engine.clear(BG)
val text_cmd = DrawIrCommand(
    kind: "text",
    component_id: "title",
    x: 2,
    y: 3,
    width: 48,
    height: 18,
    color: GREEN,
    text_value: "HI",
    border_rect: draw_ir_no_rect(),
    content_rect: draw_ir_no_rect(),
    hit_rect: draw_ir_no_rect(),
    clip_rect: draw_ir_no_rect(),
    computed_style: [
        draw_ir_style_prop("font-size", "16px"),
        draw_ir_style_prop("font-rendering", "bitmap-vector-backend-preferred")
    ],
    edge: nil,
    parent_id: "window",
    image_uri: "",
    points: []
)
val batch = draw_ir_batch("text-batch", DRAW_IR_TEST_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 64, 32, 1, 1000, false), [text_cmd])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.text_command_count).to_equal(1)
expect(result.last_text_font_size).to_equal(16)
expect(result.font_offload_status).to_equal("cpu-fallback")
expect(result.font_offload_reason).to_equal("production-gpu-dispatch-not-wired")
expect(result.font_gpu_glyph_returned).to_equal(false)
expect(result.font_production_ready).to_equal(false)
expect(_count_not_color(result.pixels, BG)).to_be_greater_than(0)
engine.shutdown()
```

</details>

#### reuses text blit buffers across repeated Draw IR text commands

1. var engine = Engine2D create with backend
2. engine clear
3.  draw ir text command
4.  draw ir text command
   - Expected: result.rendered_command_count equals `2`
   - Expected: result.text_command_count equals `2`
   - Expected: result.font_text_cache_hits equals `1`
   - Expected: result.font_text_cache_misses equals `1`
   - Expected: stats.attempts equals `1`
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(64, 32, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("text-cache-batch", DRAW_IR_TEST_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 64, 32, 1, 1000, false), [
    _draw_ir_text_command("title-a", 2, 3, "A"),
    _draw_ir_text_command("title-b", 28, 3, "A")
])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)
val stats = vector_font_accelerator_stats()

expect(result.rendered_command_count).to_equal(2)
expect(result.text_command_count).to_equal(2)
expect(result.font_text_cache_hits).to_equal(1)
expect(result.font_text_cache_misses).to_equal(1)
expect(stats.attempts).to_equal(1)
expect(_count_not_color(result.pixels, BG)).to_be_greater_than(0)
engine.shutdown()
```

</details>

#### reports gpu glyph return when backend rasterizer supplies vector glyph pixels

1.  set cuda vector font probe glyph
2. var engine = Engine2D create with backend
3. engine clear
4.  draw ir text command
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.text_command_count equals `1`
   - Expected: result.font_offload_status equals `gpu-glyph-returned`
   - Expected: result.font_offload_reason equals `cuda-vector-font-glyph-pixels-returned`
   - Expected: result.font_gpu_glyph_returned is true
   - Expected: result.font_production_ready is true
   - Expected: stats.gpu_returned_glyphs equals `1`
   - Expected: stats.gpu_returned_glyph_pixels equals `1`
5. engine shutdown
6.  clear cuda vector font probe glyph


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_set_cuda_vector_font_probe_glyph()
var engine = Engine2D.create_with_backend(64, 32, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("text-gpu-glyph-batch", DRAW_IR_TEST_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 64, 32, 1, 1000, false), [
    _draw_ir_text_command("title-a", 2, 3, "A")
])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)
val stats = vector_font_accelerator_stats()

expect(result.rendered_command_count).to_equal(1)
expect(result.text_command_count).to_equal(1)
expect(result.font_offload_status).to_equal("gpu-glyph-returned")
expect(result.font_offload_reason).to_equal("cuda-vector-font-glyph-pixels-returned")
expect(result.font_gpu_glyph_returned).to_equal(true)
expect(result.font_production_ready).to_equal(true)
expect(stats.gpu_returned_glyphs).to_equal(1)
expect(stats.gpu_returned_glyph_pixels).to_equal(1)
expect(_count_not_color(result.pixels, BG)).to_be_greater_than(0)
engine.shutdown()
_clear_cuda_vector_font_probe_glyph()
```

</details>

#### reports gpu glyph return when backend rasterizer supplies bitmap glyph pixels

1.  set cuda bitmap font probe glyph
2. var engine = Engine2D create with backend
3. engine clear
4.  draw ir text command
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.text_command_count equals `1`
   - Expected: result.font_offload_status equals `gpu-glyph-returned`
   - Expected: result.font_offload_reason equals `cuda-bitmap-font-glyph-pixels-returned`
   - Expected: result.font_gpu_glyph_returned is true
   - Expected: result.font_production_ready is true
   - Expected: stats.gpu_returned_glyphs equals `1`
   - Expected: stats.gpu_returned_glyph_pixels equals `1`
5. engine shutdown
6.  clear cuda bitmap font probe glyph


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_set_cuda_bitmap_font_probe_glyph()
var engine = Engine2D.create_with_backend(64, 32, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("text-bitmap-gpu-glyph-batch", DRAW_IR_TEST_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 64, 32, 1, 1000, false), [
    _draw_ir_text_command("title-bitmap", 2, 3, "~")
])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)
val stats = bitmap_font_accelerator_stats()

expect(result.rendered_command_count).to_equal(1)
expect(result.text_command_count).to_equal(1)
expect(result.font_offload_status).to_equal("gpu-glyph-returned")
expect(result.font_offload_reason).to_equal("cuda-bitmap-font-glyph-pixels-returned")
expect(result.font_gpu_glyph_returned).to_equal(true)
expect(result.font_production_ready).to_equal(true)
expect(stats.gpu_returned_glyphs).to_equal(1)
expect(stats.gpu_returned_glyph_pixels).to_equal(1)
expect(_count_not_color(result.pixels, BG)).to_be_greater_than(0)
engine.shutdown()
_clear_cuda_bitmap_font_probe_glyph()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md](doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md)
- **Design:** [doc/04_architecture/ui/ui_test_architecture.md](doc/04_architecture/ui/ui_test_architecture.md)
- **Research:** [doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md](doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md)


</details>
