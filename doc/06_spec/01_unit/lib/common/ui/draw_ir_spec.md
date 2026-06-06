# Draw Ir Specification

> <details>

<!-- sdn-diagram:id=draw_ir_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_spec -> std
draw_ir_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_ir_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Specification

## Scenarios

### shared Draw IR advanced Simple 2D contract

#### uses the additive v2 schema while keeping v1 rect and text constructors compatible

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = draw_ir_rect("body", 1, 2, 30, 40, 0xff202428u32)
val text_cmd = draw_ir_text("label", 4, 18, "Ready", 0xffffffffu32)

expect(DRAW_IR_SCHEMA_VERSION).to_equal("simple-draw-ir-v2")
expect(rect.kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(text_cmd.kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(rect.border_rect.present).to_equal(false)
expect(rect.content_rect.present).to_equal(false)
expect(rect.hit_rect.present).to_equal(false)
expect(rect.clip_rect.present).to_equal(false)
expect(rect.computed_style.len()).to_equal(0)
expect(rect.edge == nil).to_equal(true)
```

</details>

#### embeds window size location layer and transparency metadata

1. draw ir rect

2. draw ir text
   - Expected: batch.schema equals `DRAW_IR_SCHEMA_VERSION`
   - Expected: batch.embedding.surface_id equals `surface-1`
   - Expected: batch.embedding.component_id equals `window-1`
   - Expected: batch.embedding.x equals `10`
   - Expected: batch.embedding.y equals `20`
   - Expected: batch.embedding.width equals `640`
   - Expected: batch.embedding.height equals `360`
   - Expected: batch.embedding.layer equals `7`
   - Expected: batch.embedding.opacity_milli equals `720`
   - Expected: batch.embedding.clip is true
   - Expected: batch.commands.len() equals `2`
   - Expected: batch.commands[0].kind equals `DRAW_IR_COMMAND_RECT`
   - Expected: batch.commands[1].kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: batch.source.source_kind equals `DRAW_IR_SOURCE_MANUAL`


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface-1", "window-1", 10, 20, 640, 360, 7, 720, true)
val batch = draw_ir_batch("batch-1", DRAW_IR_BACKEND_CPU, embedding, [
    draw_ir_rect("titlebar", 0, 0, 640, 28, 0xff101418u32),
    draw_ir_text("title", 12, 18, "Terminal", 0xffffffffu32)
])

expect(batch.schema).to_equal(DRAW_IR_SCHEMA_VERSION)
expect(batch.embedding.surface_id).to_equal("surface-1")
expect(batch.embedding.component_id).to_equal("window-1")
expect(batch.embedding.x).to_equal(10)
expect(batch.embedding.y).to_equal(20)
expect(batch.embedding.width).to_equal(640)
expect(batch.embedding.height).to_equal(360)
expect(batch.embedding.layer).to_equal(7)
expect(batch.embedding.opacity_milli).to_equal(720)
expect(batch.embedding.clip).to_equal(true)
expect(batch.commands.len()).to_equal(2)
expect(batch.commands[0].kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(batch.commands[1].kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(batch.source.source_kind).to_equal(DRAW_IR_SOURCE_MANUAL)
```

</details>

#### keeps GUI and HTML AST source metadata with CSS style identity

1. draw ir rect

2. draw ir text
   - Expected: html_batch.source.source_kind equals `DRAW_IR_SOURCE_HTML_AST`
   - Expected: html_batch.source.source_id equals `html-node-42`
   - Expected: html_batch.source.html_tag equals `button`
   - Expected: html_batch.source.html_node_id equals `ok-button`
   - Expected: html_batch.source.css_selector equals `#dialog button.primary`
   - Expected: html_batch.source.css_class equals `primary`
   - Expected: html_batch.source.style_key equals `button.primary`
   - Expected: html_batch.source.style_revision equals `css-rev-7`
   - Expected: gui_source.source_kind equals `DRAW_IR_SOURCE_GUI_AST`
   - Expected: gui_source.source_id equals `gui-node-9`
   - Expected: gui_source.style_key equals `dialog.button.primary`
   - Expected: gui_source.style_revision equals `gui-style-2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface-html", "button-ok", 24, 32, 180, 44, 3, 1000, true)
val html_source = draw_ir_source_html_ast("html-node-42", "button", "ok-button", "#dialog button.primary", "primary", "button.primary", "css-rev-7")
val html_batch = draw_ir_batch_with_source("button-ok", DRAW_IR_BACKEND_GPU, embedding, [
    draw_ir_rect("button-bg", 0, 0, 180, 44, 0xff2f80edu32),
    draw_ir_text("button-label", 16, 27, "OK", 0xffffffffu32)
], html_source)
val gui_source = draw_ir_source_gui_ast("gui-node-9", "dialog.button.primary", "gui-style-2")

expect(html_batch.source.source_kind).to_equal(DRAW_IR_SOURCE_HTML_AST)
expect(html_batch.source.source_id).to_equal("html-node-42")
expect(html_batch.source.html_tag).to_equal("button")
expect(html_batch.source.html_node_id).to_equal("ok-button")
expect(html_batch.source.css_selector).to_equal("#dialog button.primary")
expect(html_batch.source.css_class).to_equal("primary")
expect(html_batch.source.style_key).to_equal("button.primary")
expect(html_batch.source.style_revision).to_equal("css-rev-7")
expect(gui_source.source_kind).to_equal(DRAW_IR_SOURCE_GUI_AST)
expect(gui_source.source_id).to_equal("gui-node-9")
expect(gui_source.style_key).to_equal("dialog.button.primary")
expect(gui_source.style_revision).to_equal("gui-style-2")
```

</details>

#### plans CPU-compatible Simple 2D advanced rendering for Draw IR batches

1. draw ir rect
   - Expected: plan.schema equals `DRAW_IR_SCHEMA_VERSION`
   - Expected: plan.batch_id equals `batch-cpu`
   - Expected: plan.backend_target equals `DRAW_IR_BACKEND_CPU`
   - Expected: plan.selected_backend equals `DRAW_IR_BACKEND_CPU`
   - Expected: plan.command_count equals `1`
   - Expected: plan.width equals `320`
   - Expected: plan.height equals `240`
   - Expected: plan.layer equals `2`
   - Expected: plan.opacity_milli equals `1000`
   - Expected: plan.fallback_required is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface-1", "window-1", 0, 0, 320, 240, 2, 1000, false)
val batch = draw_ir_batch("batch-cpu", DRAW_IR_BACKEND_CPU, embedding, [
    draw_ir_rect("body", 0, 0, 320, 240, 0xff202428u32)
])

val plan = simple_2d_draw_ir_adv_plan(batch, false)

expect(plan.schema).to_equal(DRAW_IR_SCHEMA_VERSION)
expect(plan.batch_id).to_equal("batch-cpu")
expect(plan.backend_target).to_equal(DRAW_IR_BACKEND_CPU)
expect(plan.selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
expect(plan.command_count).to_equal(1)
expect(plan.width).to_equal(320)
expect(plan.height).to_equal(240)
expect(plan.layer).to_equal(2)
expect(plan.opacity_milli).to_equal(1000)
expect(plan.fallback_required).to_equal(false)
```

</details>

#### keeps GPU migration behind explicit target metadata and CPU fallback

1. draw ir rect

2. draw ir rect
   - Expected: gpu_unavailable.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: gpu_unavailable.selected_backend equals `DRAW_IR_BACKEND_CPU`
   - Expected: gpu_unavailable.fallback_required is true
   - Expected: gpu_available.selected_backend equals `DRAW_IR_BACKEND_GPU`
   - Expected: gpu_available.fallback_required is false
   - Expected: auto_unavailable.selected_backend equals `DRAW_IR_BACKEND_CPU`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface-2", "window-2", 100, 80, 480, 300, 9, 860, true)
val gpu_batch = draw_ir_batch("batch-gpu", DRAW_IR_BACKEND_GPU, embedding, [
    draw_ir_rect("body", 0, 0, 480, 300, 0xff000000u32)
])
val auto_batch = draw_ir_batch("batch-auto", DRAW_IR_BACKEND_AUTO, embedding, [
    draw_ir_rect("body", 0, 0, 480, 300, 0xff000000u32)
])

val gpu_unavailable = simple_2d_draw_ir_adv_plan(gpu_batch, false)
val gpu_available = simple_2d_draw_ir_adv_plan(gpu_batch, true)
val auto_unavailable = simple_2d_draw_ir_adv_plan(auto_batch, false)

expect(gpu_unavailable.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(gpu_unavailable.selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
expect(gpu_unavailable.fallback_required).to_equal(true)
expect(gpu_unavailable.fallback_reason).to_contain("gpu backend unavailable")
expect(gpu_available.selected_backend).to_equal(DRAW_IR_BACKEND_GPU)
expect(gpu_available.fallback_required).to_equal(false)
expect(auto_unavailable.selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
```

</details>

#### plans composed Draw IR batches for the Simple 2D advanced interface

1. draw ir batch

2. draw ir rect

3. draw ir text
   - Expected: plan.composition_id equals `wm-composite`
   - Expected: plan.scene_key equals `scene-key-1`
   - Expected: plan.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: plan.selected_backend equals `DRAW_IR_BACKEND_CPU`
   - Expected: plan.batch_count equals `2`
   - Expected: plan.command_count equals `3`
   - Expected: plan.fallback_required is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = draw_ir_embedding_config("wm", "desktop", 0, 0, 800, 600, 0, 1000, false)
val win = draw_ir_embedding_config("surf1", "win1", 20, 40, 300, 200, 10, 930, true)
val composition = draw_ir_composition("wm-composite", "scene-key-1", DRAW_IR_BACKEND_GPU, [
    draw_ir_batch("desktop", DRAW_IR_BACKEND_GPU, root, [draw_ir_rect("bg", 0, 0, 800, 600, 0xff101418u32)]),
    draw_ir_batch("win1", DRAW_IR_BACKEND_GPU, win, [
        draw_ir_rect("body", 0, 0, 300, 200, 0xff20262du32),
        draw_ir_text("title", 12, 19, "Terminal", 0xffffffffu32)
    ])
])

val plan = simple_2d_draw_ir_adv_composition_plan(composition, false)

expect(plan.composition_id).to_equal("wm-composite")
expect(plan.scene_key).to_equal("scene-key-1")
expect(plan.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(plan.selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
expect(plan.batch_count).to_equal(2)
expect(plan.command_count).to_equal(3)
expect(plan.fallback_required).to_equal(true)
expect(plan.fallback_reason).to_contain("gpu backend unavailable")
```

</details>

#### maps event target metadata to a Draw IR batch and rejects stale scenes

1. draw ir batch

2. draw ir rect
   - Expected: resolved.resolved is true
   - Expected: resolved.stale_scene_rejected is false
   - Expected: resolved.batch_id equals `window-win2`
   - Expected: resolved.surface_id equals `surf2`
   - Expected: resolved.component_id equals `win2`
   - Expected: resolved.batch_local_x equals `10`
   - Expected: resolved.batch_local_y equals `10`
   - Expected: resolved.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: stale.resolved is false
   - Expected: stale.stale_scene_rejected is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desktop = draw_ir_embedding_config("wm", "desktop", 0, 0, 800, 600, 0, 1000, false)
val win = draw_ir_embedding_config("surf2", "win2", 80, 120, 300, 200, 11, 1000, true)
val composition = draw_ir_composition("wm-composite", "scene-key-2", DRAW_IR_BACKEND_GPU, [
    draw_ir_batch("desktop", DRAW_IR_BACKEND_GPU, desktop, [draw_ir_rect("background", 0, 0, 800, 600, 0xff101418u32)]),
    draw_ir_batch("window-win2", DRAW_IR_BACKEND_GPU, win, [
        draw_ir_rect("win2-body", 0, 0, 300, 200, 0xff20262du32)
    ])
])

val resolved = draw_ir_event_target_context(composition, "scene-key-2", "x=90;y=130", "focus_window", "win2", "window", 10, 10, DRAW_IR_BACKEND_GPU)
val stale = draw_ir_event_target_context(composition, "old-scene", "x=90;y=130", "focus_window", "win2", "window", 10, 10, DRAW_IR_BACKEND_GPU)

expect(resolved.resolved).to_equal(true)
expect(resolved.stale_scene_rejected).to_equal(false)
expect(resolved.batch_id).to_equal("window-win2")
expect(resolved.surface_id).to_equal("surf2")
expect(resolved.component_id).to_equal("win2")
expect(resolved.batch_local_x).to_equal(10)
expect(resolved.batch_local_y).to_equal(10)
expect(resolved.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(stale.resolved).to_equal(false)
expect(stale.stale_scene_rejected).to_equal(true)
```

</details>

#### constructs v2 box geometry, computed style, and edge commands

1. draw ir rect bounds

2. draw ir rect bounds

3. draw ir rect bounds

4. draw ir no rect

5. [draw ir style prop

6. [draw ir point

7. [draw ir style prop
   - Expected: styled.border_rect.present is true
   - Expected: styled.content_rect.width equals `92`
   - Expected: styled.hit_rect.height equals `44`
   - Expected: styled.computed_style.len() equals `2`
   - Expected: styled.computed_style[0].key equals `border-radius`
   - Expected: edge_cmd.kind equals `DRAW_IR_COMMAND_EDGE`
   - Expected: edge_cmd.component_id equals `edge-1`
   - Expected: edge_cmd.edge.source equals `button-bg`
   - Expected: edge_cmd.edge.target equals `label`
   - Expected: edge_cmd.edge.routing equals `DRAW_IR_EDGE_ORTHOGONAL`


<details>
<summary>Executable SPipe</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val styled = draw_ir_box_with_style(
    "button-bg",
    10,
    20,
    100,
    40,
    0xff2f80edu32,
    draw_ir_rect_bounds(10, 20, 100, 40),
    draw_ir_rect_bounds(14, 24, 92, 32),
    draw_ir_rect_bounds(8, 18, 104, 44),
    draw_ir_no_rect(),
    [draw_ir_style_prop("border-radius", "6"), draw_ir_style_prop("display", "flex")]
)
val edge = draw_edge(
    "edge-1",
    "button-bg",
    "label",
    DRAW_IR_EDGE_ORTHOGONAL,
    [draw_ir_point(10, 20), draw_ir_point(110, 20)],
    [draw_ir_style_prop("stroke", "#2f80ed")]
)
val edge_cmd = draw_ir_edge_command(edge)

expect(styled.border_rect.present).to_equal(true)
expect(styled.content_rect.width).to_equal(92)
expect(styled.hit_rect.height).to_equal(44)
expect(styled.computed_style.len()).to_equal(2)
expect(styled.computed_style[0].key).to_equal("border-radius")
expect(edge_cmd.kind).to_equal(DRAW_IR_COMMAND_EDGE)
expect(edge_cmd.component_id).to_equal("edge-1")
expect(edge_cmd.edge.source).to_equal("button-bg")
expect(edge_cmd.edge.target).to_equal("label")
expect(edge_cmd.edge.routing).to_equal(DRAW_IR_EDGE_ORTHOGONAL)
```

</details>

#### constructs path image group and port command kinds

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = draw_ir_path_command("path-1", [draw_ir_point(0, 0), draw_ir_point(20, 10)], [draw_ir_style_prop("stroke", "#111")])
val image = draw_ir_image_command("image-1", 4, 5, 64, 32, "asset://logo", [])
val group = draw_ir_group_command("group-1", "root")
val port = draw_ir_port_command("port-1", "group-1", 12, 16)

expect(path.kind).to_equal(DRAW_IR_COMMAND_PATH)
expect(path.points.len()).to_equal(2)
expect(path.computed_style[0].key).to_equal("stroke")
expect(image.kind).to_equal(DRAW_IR_COMMAND_IMAGE)
expect(image.image_uri).to_equal("asset://logo")
expect(image.hit_rect.present).to_equal(true)
expect(group.kind).to_equal(DRAW_IR_COMMAND_GROUP)
expect(group.parent_id).to_equal("root")
expect(port.kind).to_equal(DRAW_IR_COMMAND_PORT)
expect(port.parent_id).to_equal("group-1")
expect(port.hit_rect.x).to_equal(12)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared Draw IR advanced Simple 2D contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
