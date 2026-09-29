# draw_ir_spec

> Purpose: Prove that shared Draw IR advanced Simple 2D contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# draw_ir_spec

Purpose: Prove that shared Draw IR advanced Simple 2D contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that shared Draw IR advanced Simple 2D contract.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### shared Draw IR advanced Simple 2D contract

#### uses the additive v2 schema while keeping v1 rect and text constructors compatible

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the additive v2 schema while keeping v1 rect and text constructors compatible
- Verify: uses the additive v2 schema while keeping v1 rect and text constructors compatible
   - Expected: DRAW_IR_SCHEMA_VERSION equals `simple-draw-ir-v2`
   - Expected: rect.kind equals `DRAW_IR_COMMAND_RECT`
   - Expected: text_cmd.kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: rect.border_rect.present is false
   - Expected: rect.content_rect.present is false
   - Expected: rect.hit_rect.present is false
   - Expected: rect.clip_rect.present is false
   - Expected: rect.computed_style.len() equals `0`
   - Expected: rect.edge equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses the additive v2 schema while keeping v1 rect and text constructors compatible")
step("Verify: uses the additive v2 schema while keeping v1 rect and text constructors compatible")
# @req: REQ-LIB-COMMON-001
val rect = draw_ir_rect("body", 1, 2, 30, 40, 0xff202428u32)
val text_cmd = draw_ir_text("label", 4, 18, "Ready", 0xffffffffu32)

expect(DRAW_IR_SCHEMA_VERSION).to_equal("simple-draw-ir-v2")
expect(rect.kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(text_cmd.kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(rect.border_rect.present).to_equal(false)
expect(rect.content_rect.present).to_equal(false)
expect(rect.hit_rect.present).to_equal(false)
expect(rect.clip_rect.present).to_equal(false)
expect(rect.computed_style.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(rect.edge).to_equal(nil)
```

</details>

#### translates and intersects command clips through the shared Draw IR contract

- translates and intersects command clips through the shared Draw IR contract
- Verify: translates and intersects command clips through the shared Draw IR contract
   - Expected: clipped.x equals `18`
   - Expected: clipped.y equals `27`
   - Expected: clipped.width equals `4`
   - Expected: clipped.height equals `12`
   - Expected: disjoint.width equals `0`
   - Expected: disjoint.height equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("translates and intersects command clips through the shared Draw IR contract")
step("Verify: translates and intersects command clips through the shared Draw IR contract")
val translated = draw_ir_rect_translate(
    draw_ir_rect_bounds(5, 7, 20, 12), 10, 20
)
val clipped = draw_ir_rect_intersection(
    translated, draw_ir_rect_bounds(18, 25, 4, 20)
)
val disjoint = draw_ir_rect_intersection(
    translated, draw_ir_rect_bounds(100, 100, 5, 5)
)

expect(clipped.x).to_equal(18)  # oracle: 18 — named expected value from the requirement
expect(clipped.y).to_equal(27)  # oracle: 27 — named expected value from the requirement
expect(clipped.width).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(clipped.height).to_equal(12)  # oracle: 12 — named expected value from the requirement
expect(disjoint.width).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(disjoint.height).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(draw_ir_rect_intersection(
    translated, draw_ir_no_rect()
)).to_equal(translated)
expect(draw_ir_rect_intersection(
    draw_ir_no_rect(), translated
)).to_equal(translated)
expect(draw_ir_rect_translate(
    draw_ir_no_rect(), 10, 20
).present).to_equal(false)
```

</details>

#### stores resolved advances as typed Draw IR without CSV style bytes

- stores resolved advances as typed Draw IR without CSV style bytes
- Verify: stores resolved advances as typed Draw IR without CSV style bytes
   - Expected: plain.computed_style.len() equals `0`
   - Expected: mismatched.computed_style.len() equals `0`
   - Expected: styled.width equals `plain.width`
   - Expected: styled.height equals `plain.height`
   - Expected: styled.computed_style[0].value equals `Noto Sans Mono`
   - Expected: styled.computed_style[1].key equals `font-identity`
   - Expected: styled.advance_widths equals `[7]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores resolved advances as typed Draw IR without CSV style bytes")
step("Verify: stores resolved advances as typed Draw IR without CSV style bytes")
val plain = draw_ir_text("plain", 1, 2, "A", 0xffffffffu32)
val styled = draw_ir_text_resolved_font("styled", 1, 2, "A", 0xffffffffu32, "Noto Sans Mono", "sha256=test;axes=wght=400,wdth=100", [7], 7, 14, 12)
val mismatched = draw_ir_text_resolved_font("mismatch", 1, 2, "A", 0xffffffffu32, "Noto Sans Mono", "sha256=test", [6], 7, 14, 12)
expect_typed_draw_ir_font_advances(styled)

expect(plain.computed_style.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(mismatched.computed_style.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
if styled.computed_style.len() == 0:
    expect(styled.width).to_equal(plain.width)
    expect(styled.height).to_equal(plain.height)
else:
    expect(styled.computed_style[0].value).to_equal("Noto Sans Mono")
    expect(styled.computed_style[1].key).to_equal("font-identity")
    expect(styled.computed_style[1].value).to_start_with("sha256=")
    expect(styled.advance_widths).to_equal([7])
    expect(styled.width).to_be_greater_than(0)
    expect(styled.height).to_be_greater_than(0)
```

</details>

#### keeps shaped Unicode glyph positions and logical clusters semantic

- keeps shaped Unicode glyph positions and logical clusters semantic
- Verify: keeps shaped Unicode glyph positions and logical clusters semantic
   - Expected: shaped.glyph_run.valid is true
   - Expected: shaped.glyph_run.glyph_ids equals `[288u32, 85u32, 319u32]`
   - Expected: shaped.glyph_run.xs equals `[3, 0, 17]`
   - Expected: shaped.glyph_run.ys equals `[2, 0, 0]`
   - Expected: shaped.glyph_run.clusters equals `[1, 1, 0]`
   - Expected: shaped.advance_widths equals `[8, 12]`
   - Expected: shaped.computed_style[4].value equals `selected-pure-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps shaped Unicode glyph positions and logical clusters semantic")
step("Verify: keeps shaped Unicode glyph positions and logical clusters semantic")
val payload = draw_ir_glyph_run_payload(
    [288u32, 85u32, 319u32], [3, 0, 17], [2, 0, 0], [1, 1, 0], true
)
val shaped = draw_ir_text_shaped_font(
    "arabic", 4, 5, "اب", 0xffffffffu32, "Noto Sans Arabic",
    "sha256=test;axes=wght=400,wdth=100", [8, 12], 20, 32, 32, payload
)

expect(shaped.glyph_run.valid).to_equal(true)
expect(shaped.glyph_run.glyph_ids).to_equal([288u32, 85u32, 319u32])
expect(shaped.glyph_run.xs).to_equal([3, 0, 17])
expect(shaped.glyph_run.ys).to_equal([2, 0, 0])
expect(shaped.glyph_run.clusters).to_equal([1, 1, 0])
expect(shaped.advance_widths).to_equal([8, 12])
expect(shaped.computed_style[4].value).to_equal("selected-pure-simple")
```

</details>

#### embeds window size location layer and transparency metadata

- embeds window size location layer and transparency metadata
- Verify: embeds window size location layer and transparency metadata
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
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("embeds window size location layer and transparency metadata")
step("Verify: embeds window size location layer and transparency metadata")
val embedding = draw_ir_embedding_config("surface-1", "window-1", 10, 20, 640, 360, 7, 720, true)
val batch = draw_ir_batch("batch-1", DRAW_IR_BACKEND_CPU, embedding, [
    draw_ir_rect("titlebar", 0, 0, 640, 28, 0xff101418u32),
    draw_ir_text("title", 12, 18, "Terminal", 0xffffffffu32)
])

expect(batch.schema).to_equal(DRAW_IR_SCHEMA_VERSION)
expect(batch.embedding.surface_id).to_equal("surface-1")
expect(batch.embedding.component_id).to_equal("window-1")
expect(batch.embedding.x).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(batch.embedding.y).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(batch.embedding.width).to_equal(640)  # oracle: 640 — named expected value from the requirement
expect(batch.embedding.height).to_equal(360)  # oracle: 360 — named expected value from the requirement
expect(batch.embedding.layer).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(batch.embedding.opacity_milli).to_equal(720)  # oracle: 720 — named expected value from the requirement
expect(batch.embedding.clip).to_equal(true)
expect(batch.commands.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(batch.commands[0].kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(batch.commands[1].kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(batch.source.source_kind).to_equal(DRAW_IR_SOURCE_MANUAL)
```

</details>

#### keeps GUI and HTML AST source metadata with CSS style identity

- keeps GUI and HTML AST source metadata with CSS style identity
- Verify: keeps GUI and HTML AST source metadata with CSS style identity
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
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps GUI and HTML AST source metadata with CSS style identity")
step("Verify: keeps GUI and HTML AST source metadata with CSS style identity")
val embedding = draw_ir_embedding_config("surface-html", "button-ok", 24, 32, 180, 44, 3, 1000, true)
val html_source = draw_ir_source_html_ast("html-node-42", "button", "ok-button", "#dialog button.primary", "primary", "button.primary", "css-rev-7")
val html_batch = draw_ir_batch_with_source("button-ok", DRAW_IR_BACKEND_GPU, embedding, [
    draw_ir_rect("button-bg", 0, 0, 180, 44, 0xffdceafbu32),
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

- plans CPU-compatible Simple 2D advanced rendering for Draw IR batches
- Verify: plans CPU-compatible Simple 2D advanced rendering for Draw IR batches
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
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("plans CPU-compatible Simple 2D advanced rendering for Draw IR batches")
step("Verify: plans CPU-compatible Simple 2D advanced rendering for Draw IR batches")
val embedding = draw_ir_embedding_config("surface-1", "window-1", 0, 0, 320, 240, 2, 1000, false)
val batch = draw_ir_batch("batch-cpu", DRAW_IR_BACKEND_CPU, embedding, [
    draw_ir_rect("body", 0, 0, 320, 240, 0xff202428u32)
])

val plan = simple_2d_draw_ir_adv_plan(batch, false)

expect(plan.schema).to_equal(DRAW_IR_SCHEMA_VERSION)
expect(plan.batch_id).to_equal("batch-cpu")
expect(plan.backend_target).to_equal(DRAW_IR_BACKEND_CPU)
expect(plan.selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
expect(plan.command_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(plan.width).to_equal(320)  # oracle: 320 — named expected value from the requirement
expect(plan.height).to_equal(240)  # oracle: 240 — named expected value from the requirement
expect(plan.layer).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(plan.opacity_milli).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
expect(plan.fallback_required).to_equal(false)
```

</details>

#### keeps GPU migration behind explicit target metadata and CPU fallback

- keeps GPU migration behind explicit target metadata and CPU fallback
- Verify: keeps GPU migration behind explicit target metadata and CPU fallback
   - Expected: gpu_unavailable.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: gpu_unavailable.selected_backend equals `DRAW_IR_BACKEND_CPU`
   - Expected: gpu_unavailable.fallback_required is true
   - Expected: gpu_available.selected_backend equals `DRAW_IR_BACKEND_GPU`
   - Expected: gpu_available.fallback_required is false
   - Expected: auto_unavailable.selected_backend equals `DRAW_IR_BACKEND_CPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps GPU migration behind explicit target metadata and CPU fallback")
step("Verify: keeps GPU migration behind explicit target metadata and CPU fallback")
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

- plans composed Draw IR batches for the Simple 2D advanced interface
- Verify: plans composed Draw IR batches for the Simple 2D advanced interface
   - Expected: plan.composition_id equals `wm-composite`
   - Expected: plan.scene_key equals `scene-key-1`
   - Expected: plan.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: plan.selected_backend equals `DRAW_IR_BACKEND_CPU`
   - Expected: plan.batch_count equals `2`
   - Expected: plan.command_count equals `3`
   - Expected: plan.fallback_required is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("plans composed Draw IR batches for the Simple 2D advanced interface")
step("Verify: plans composed Draw IR batches for the Simple 2D advanced interface")
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
expect(plan.batch_count).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(plan.command_count).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(plan.fallback_required).to_equal(true)
expect(plan.fallback_reason).to_contain("gpu backend unavailable")
```

</details>

#### maps event target metadata to a Draw IR batch and rejects stale scenes

- maps event target metadata to a Draw IR batch and rejects stale scenes
- Verify: maps event target metadata to a Draw IR batch and rejects stale scenes
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
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps event target metadata to a Draw IR batch and rejects stale scenes")
step("Verify: maps event target metadata to a Draw IR batch and rejects stale scenes")
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
expect(resolved.batch_local_x).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(resolved.batch_local_y).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(resolved.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(stale.resolved).to_equal(false)
expect(stale.stale_scene_rejected).to_equal(true)
```

</details>

#### constructs v2 box geometry, computed style, and edge commands

- constructs v2 box geometry, computed style, and edge commands
- Verify: constructs v2 box geometry, computed style, and edge commands
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
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs v2 box geometry, computed style, and edge commands")
step("Verify: constructs v2 box geometry, computed style, and edge commands")
val styled = draw_ir_box_with_style(
    "button-bg",
    10,
    20,
    100,
    40,
    0xffdceafbu32,
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
expect(styled.content_rect.width).to_equal(92)  # oracle: 92 — named expected value from the requirement
expect(styled.hit_rect.height).to_equal(44)  # oracle: 44 — named expected value from the requirement
expect(styled.computed_style.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(styled.computed_style[0].key).to_equal("border-radius")
expect(edge_cmd.kind).to_equal(DRAW_IR_COMMAND_EDGE)
expect(edge_cmd.component_id).to_equal("edge-1")
expect(edge_cmd.edge.source).to_equal("button-bg")
expect(edge_cmd.edge.target).to_equal("label")
expect(edge_cmd.edge.routing).to_equal(DRAW_IR_EDGE_ORTHOGONAL)
```

</details>

#### constructs path image group and port command kinds

- constructs path image group and port command kinds
- Verify: constructs path image group and port command kinds
   - Expected: path.kind equals `DRAW_IR_COMMAND_PATH`
   - Expected: path.points.len() equals `2`
   - Expected: path.computed_style[0].key equals `stroke`
   - Expected: image.kind equals `DRAW_IR_COMMAND_IMAGE`
   - Expected: image.image_uri equals `asset://logo`
   - Expected: image.hit_rect.present is true
   - Expected: group.kind equals `DRAW_IR_COMMAND_GROUP`
   - Expected: group.parent_id equals `root`
   - Expected: port.kind equals `DRAW_IR_COMMAND_PORT`
   - Expected: port.parent_id equals `group-1`
   - Expected: port.hit_rect.x equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs path image group and port command kinds")
step("Verify: constructs path image group and port command kinds")
val path = draw_ir_path_command("path-1", [draw_ir_point(0, 0), draw_ir_point(20, 10)], [draw_ir_style_prop("stroke", "#111")])
val image = draw_ir_image_command("image-1", 4, 5, 64, 32, "asset://logo", [])
val group = draw_ir_group_command("group-1", "root")
val port = draw_ir_port_command("port-1", "group-1", 12, 16)

expect(path.kind).to_equal(DRAW_IR_COMMAND_PATH)
expect(path.points.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(path.computed_style[0].key).to_equal("stroke")
expect(image.kind).to_equal(DRAW_IR_COMMAND_IMAGE)
expect(image.image_uri).to_equal("asset://logo")
expect(image.hit_rect.present).to_equal(true)
expect(group.kind).to_equal(DRAW_IR_COMMAND_GROUP)
expect(group.parent_id).to_equal("root")
expect(port.kind).to_equal(DRAW_IR_COMMAND_PORT)
expect(port.parent_id).to_equal("group-1")
expect(port.hit_rect.x).to_equal(12)  # oracle: 12 — named expected value from the requirement
```

</details>

#### defaults parent_id to empty and threads a caller-supplied parent_id through every builder

- defaults parent_id to empty and threads a caller-supplied parent_id through every builder
- Verify: defaults parent_id to empty and threads a caller-supplied parent_id through every builder
   - Expected: plain_rect.parent_id equals ``
   - Expected: plain_text.parent_id equals ``
   - Expected: parented_rect.parent_id equals `owner-1`
   - Expected: parented_rect_clipped.parent_id equals `owner-1`
   - Expected: parented_text.parent_id equals `owner-1`
   - Expected: parented_text_styled.parent_id equals `owner-1`
   - Expected: parented_box.parent_id equals `owner-1`
   - Expected: parented_path.parent_id equals `owner-1`
   - Expected: parented_image.parent_id equals `owner-1`
   - Expected: parented_edge.parent_id equals `owner-1`
   - Expected: resolved_fallback.parent_id equals `owner-2`
   - Expected: resolved_measured.parent_id equals `owner-2`
   - Expected: shaped.parent_id equals `owner-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults parent_id to empty and threads a caller-supplied parent_id through every builder")
step("Verify: defaults parent_id to empty and threads a caller-supplied parent_id through every builder")
# Every DrawIrCommand builder defaults parent_id to "" when the
# caller does not know its owning node (matching the pre-existing
# draw_ir_group_command/draw_ir_port_command contract), and now
# accepts a real parent_id as a trailing optional argument.
val plain_rect = draw_ir_rect("leaf-rect", 0, 0, 10, 10, 0u32)
val plain_text = draw_ir_text("leaf-text", 0, 0, "x", 0u32)
expect(plain_rect.parent_id).to_equal("")
expect(plain_text.parent_id).to_equal("")

val parented_rect = draw_ir_rect("child-rect", 0, 0, 10, 10, 0u32, "owner-1")
val parented_rect_clipped = draw_ir_rect_clipped("child-rect-2", 0, 0, 10, 10, 0u32, draw_ir_no_rect(), "owner-1")
val parented_text = draw_ir_text("child-text", 0, 0, "x", 0u32, "owner-1")
val parented_text_styled = draw_ir_text_styled("child-text-styled", 0, 0, "x", 0u32, [], "owner-1")
val parented_box = draw_ir_box_with_style(
    "child-box", 0, 0, 10, 10, 0u32,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), [], "owner-1"
)
val parented_path = draw_ir_path_command("child-path", [], [], "owner-1")
val parented_image = draw_ir_image_command("child-image", 0, 0, 10, 10, "asset://x", [], "owner-1")
val parented_edge = draw_ir_edge_command(
    draw_edge("edge-2", "a", "b", DRAW_IR_EDGE_STRAIGHT, [], []), "owner-1"
)

expect(parented_rect.parent_id).to_equal("owner-1")
expect(parented_rect_clipped.parent_id).to_equal("owner-1")
expect(parented_text.parent_id).to_equal("owner-1")
expect(parented_text_styled.parent_id).to_equal("owner-1")
expect(parented_box.parent_id).to_equal("owner-1")
expect(parented_path.parent_id).to_equal("owner-1")
expect(parented_image.parent_id).to_equal("owner-1")
expect(parented_edge.parent_id).to_equal("owner-1")

# draw_ir_text_resolved_font/draw_ir_text_shaped_font must forward
# parent_id through every return path, including the early-return
# fallback to draw_ir_text when the measured metrics do not qualify.
val resolved_fallback = draw_ir_text_resolved_font(
    "font-fallback", 0, 0, "x", 0u32, "sans", "", [], 0, 0, 0, "owner-2"
)
expect(resolved_fallback.parent_id).to_equal("owner-2")
val resolved_measured = draw_ir_text_resolved_font(
    "font-measured", 0, 0, "AB", 0u32, "sans", "font-id", [5, 5], 10, 12, 12, "owner-2"
)
expect(resolved_measured.parent_id).to_equal("owner-2")
val shaped = draw_ir_text_shaped_font(
    "font-shaped", 0, 0, "AB", 0u32, "sans", "font-id", [5, 5], 10, 12, 12,
    draw_ir_empty_glyph_run_payload(), "owner-2"
)
expect(shaped.parent_id).to_equal("owner-2")
```

</details>

#### rejects every malformed glyph payload and resolved metric class

- rejects every malformed glyph payload and resolved metric class
- Verify: malformed shaped text fails closed to semantic text
   - Expected: draw_ir_glyph_run_payload([], [], [], [], true).valid is false
   - Expected: draw_ir_glyph_run_payload([1u32], [], [0], [0], true).valid is false
   - Expected: draw_ir_glyph_run_payload([1u32], [0], [], [0], true).valid is false
   - Expected: draw_ir_glyph_run_payload([1u32], [0], [0], [], true).valid is false
   - Expected: draw_ir_glyph_run_payload([1u32], [0], [0], [0], false).valid is false
   - Expected: command.computed_style.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects every malformed glyph payload and resolved metric class")
step("Verify: malformed shaped text fails closed to semantic text")
expect(draw_ir_glyph_run_payload([], [], [], [], true).valid).to_equal(false)
expect(draw_ir_glyph_run_payload([1u32], [], [0], [0], true).valid).to_equal(false)
expect(draw_ir_glyph_run_payload([1u32], [0], [], [0], true).valid).to_equal(false)
expect(draw_ir_glyph_run_payload([1u32], [0], [0], [], true).valid).to_equal(false)
expect(draw_ir_glyph_run_payload([1u32], [0], [0], [0], false).valid).to_equal(false)

val empty_advances = draw_ir_text_resolved_font(
    "empty", 0, 0, "A", 0u32, "sans", "id", [], 1, 1, 1)
val zero_width = draw_ir_text_resolved_font(
    "width", 0, 0, "A", 0u32, "sans", "id", [1], 0, 1, 1)
val zero_line = draw_ir_text_resolved_font(
    "line", 0, 0, "A", 0u32, "sans", "id", [1], 1, 0, 1)
val zero_size = draw_ir_text_resolved_font(
    "size", 0, 0, "A", 0u32, "sans", "id", [1], 1, 1, 0)
val wrong_count = draw_ir_text_resolved_font(
    "count", 0, 0, "AB", 0u32, "sans", "id", [2], 2, 1, 1)
val negative = draw_ir_text_resolved_font(
    "negative", 0, 0, "A", 0u32, "sans", "id", [-1], 1, 1, 1)
val overflow = draw_ir_text_resolved_font(
    "overflow", 0, 0, "AB", 0u32, "sans", "id",
    [2147483647, 1], 1, 1, 1)
val shaped_fallback = draw_ir_text_shaped_font(
    "shaped-fallback", 0, 0, "A", 0u32, "sans", "", [], 0, 0, 0,
    draw_ir_empty_glyph_run_payload())
for command in [empty_advances, zero_width, zero_line, zero_size,
        wrong_count, negative, overflow, shaped_fallback]:
    expect(command.computed_style.len()).to_equal(0)
```

</details>

#### embeds child batches with prefixed identities clips and offsets

- embeds child batches with prefixed identities clips and offsets
- Verify: nested Draw IR remains handle-free and owner-prefixed
   - Expected: embedded.len() equals `2`
   - Expected: embedded[0].batch_id equals `frame:batch`
   - Expected: embedded[0].embedding.surface_id equals `frame:child-surface`
   - Expected: embedded[0].embedding.component_id equals `iframe`
   - Expected: embedded[0].embedding.x equals `10`
   - Expected: embedded[0].embedding.y equals `15`
   - Expected: embedded[0].embedding.layer equals `9`
   - Expected: embedded[0].commands[0].component_id equals `frame:leaf`
   - Expected: embedded[0].commands[0].parent_id equals ``
   - Expected: embedded[0].commands[1].parent_id equals `frame:owner`
   - Expected: embedded[0].commands[0].hit_rect.present is false
   - Expected: embedded[0].commands[1].clip_rect.present is true
   - Expected: embedded[1].batch_id equals `frame`
   - Expected: embedded[1].embedding.surface_id equals `frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("embeds child batches with prefixed identities clips and offsets")
step("Verify: nested Draw IR remains handle-free and owner-prefixed")
val clip = draw_ir_rect_bounds(10, 20, 100, 80)
val embedding = draw_ir_embedding_config(
    "child-surface", "child-root", 3, 4, 40, 30, 2, 900, true)
val plain = draw_ir_text("leaf", 1, 2, "é한😀", 0xffffffffu32)
val parented = draw_ir_text_styled_clipped(
    "nested", 1, 2, "مرحبا", 0xffffffffu32, [],
    draw_ir_rect_bounds(0, 0, 20, 20), "owner")
val child = draw_ir_composition(
    "child", "scene", DRAW_IR_BACKEND_CPU,
    [draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, embedding,
        [plain, parented]),
     draw_ir_batch("", DRAW_IR_BACKEND_CPU,
        draw_ir_embedding_config("", "empty", 0, 0, 1, 1, 0, 1000, false),
        [])])
val embedded = draw_ir_embed_composition(
    child, 7, 11, clip, "frame", "iframe", 9)
expect(embedded.len()).to_equal(2)
expect(embedded[0].batch_id).to_equal("frame:batch")
expect(embedded[0].embedding.surface_id).to_equal("frame:child-surface")
expect(embedded[0].embedding.component_id).to_equal("iframe")
expect(embedded[0].embedding.x).to_equal(10)
expect(embedded[0].embedding.y).to_equal(15)
expect(embedded[0].embedding.layer).to_equal(9)
expect(embedded[0].commands[0].component_id).to_equal("frame:leaf")
expect(embedded[0].commands[0].parent_id).to_equal("")
expect(embedded[0].commands[1].parent_id).to_equal("frame:owner")
expect(embedded[0].commands[0].hit_rect.present).to_equal(false)
expect(embedded[0].commands[1].clip_rect.present).to_equal(true)
expect(embedded[1].batch_id).to_equal("frame")
expect(embedded[1].embedding.surface_id).to_equal("frame")
```

</details>

#### resolves every event target class and unresolved current scene

- resolves every event target class and unresolved current scene
- Verify: event routing matches owners commands and WM semantic classes
   - Expected: context.resolved is true
   - Expected: context.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: unresolved.resolved is false
   - Expected: unresolved.stale_scene_rejected is false
   - Expected: unresolved.backend_target equals `DRAW_IR_BACKEND_GPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves every event target class and unresolved current scene")
step("Verify: event routing matches owners commands and WM semantic classes")
val desktop = draw_ir_embedding_config("desk-surface", "desktop", 0, 0, 10, 10, 0, 1000, false)
val chrome = draw_ir_embedding_config("chrome-surface", "wm-chrome", 0, 0, 10, 10, 1, 1000, false)
val normal = draw_ir_embedding_config("surface", "component", 0, 0, 10, 10, 2, 1000, false)
val composition = draw_ir_composition("events", "current", DRAW_IR_BACKEND_GPU, [
    draw_ir_batch("desktop-batch", DRAW_IR_BACKEND_CPU, desktop, []),
    draw_ir_batch("chrome-batch", DRAW_IR_BACKEND_CPU, chrome, []),
    draw_ir_batch("normal-batch", DRAW_IR_BACKEND_CPU, normal,
        [draw_ir_rect("command", 0, 0, 1, 1, 0u32)])
])
for context in [
    draw_ir_event_target_context(composition, "current", "i", "a", "normal-batch", "window", 0, 0, ""),
    draw_ir_event_target_context(composition, "current", "i", "a", "surface", "window", 0, 0, ""),
    draw_ir_event_target_context(composition, "current", "i", "a", "component", "window", 0, 0, ""),
    draw_ir_event_target_context(composition, "current", "i", "a", "command", "widget", 0, 0, ""),
    draw_ir_event_target_context(composition, "current", "i", "a", "none", "desktop", 0, 0, ""),
    draw_ir_event_target_context(composition, "current", "i", "a", "none", "command_lane", 0, 0, ""),
    draw_ir_event_target_context(composition, "current", "i", "a", "none", "taskbar", 0, 0, "")]:
    expect(context.resolved).to_equal(true)
    expect(context.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
val unresolved = draw_ir_event_target_context(
    composition, "current", "i", "a", "missing", "window", 3, 4, "")
expect(unresolved.resolved).to_equal(false)
expect(unresolved.stale_scene_rejected).to_equal(false)
expect(unresolved.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
```

</details>

#### selects CPU GPU auto and metal plans for batches and compositions

- selects CPU GPU auto and metal plans for batches and compositions
- Verify: backend plans expose every availability and fallback decision
   - Expected: simple_2d_draw_ir_adv_plan(auto, true).selected_backend equals `DRAW_IR_BACKEND_GPU`
   - Expected: simple_2d_draw_ir_adv_plan(metal, true).selected_backend equals `DRAW_IR_BACKEND_GPU`
   - Expected: simple_2d_draw_ir_adv_plan(metal, false).fallback_required is true
   - Expected: simple_2d_draw_ir_adv_plan(cpu, true).selected_backend equals `DRAW_IR_BACKEND_CPU`
   - Expected: simple_2d_draw_ir_adv_composition_plan(auto_composition, true).selected_backend equals `DRAW_IR_BACKEND_GPU`
   - Expected: simple_2d_draw_ir_adv_composition_plan(metal_composition, true).selected_backend equals `DRAW_IR_BACKEND_GPU`
   - Expected: simple_2d_draw_ir_adv_composition_plan(metal_composition, false).fallback_required is true
   - Expected: simple_2d_draw_ir_adv_composition_plan(cpu_composition, true).selected_backend equals `DRAW_IR_BACKEND_CPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selects CPU GPU auto and metal plans for batches and compositions")
step("Verify: backend plans expose every availability and fallback decision")
val embedding = draw_ir_embedding_config("s", "c", 0, 0, 1, 1, 0, 1000, false)
val cpu = draw_ir_batch("cpu", DRAW_IR_BACKEND_CPU, embedding, [])
val auto = draw_ir_batch("auto", DRAW_IR_BACKEND_AUTO, embedding, [])
val metal = draw_ir_batch("metal", "metal", embedding, [])
expect(simple_2d_draw_ir_adv_plan(auto, true).selected_backend).to_equal(DRAW_IR_BACKEND_GPU)
expect(simple_2d_draw_ir_adv_plan(metal, true).selected_backend).to_equal(DRAW_IR_BACKEND_GPU)
expect(simple_2d_draw_ir_adv_plan(metal, false).fallback_required).to_equal(true)
expect(simple_2d_draw_ir_adv_plan(cpu, true).selected_backend).to_equal(DRAW_IR_BACKEND_CPU)

val auto_composition = draw_ir_composition("auto", "s", DRAW_IR_BACKEND_AUTO, [auto])
val metal_composition = draw_ir_composition("metal", "s", "metal", [metal])
val cpu_composition = draw_ir_composition("cpu", "s", DRAW_IR_BACKEND_CPU, [cpu])
expect(simple_2d_draw_ir_adv_composition_plan(auto_composition, true).selected_backend).to_equal(DRAW_IR_BACKEND_GPU)
expect(simple_2d_draw_ir_adv_composition_plan(auto_composition, false).fallback_reason).to_contain("auto selected cpu")
expect(simple_2d_draw_ir_adv_composition_plan(metal_composition, true).selected_backend).to_equal(DRAW_IR_BACKEND_GPU)
expect(simple_2d_draw_ir_adv_composition_plan(metal_composition, false).fallback_required).to_equal(true)
expect(simple_2d_draw_ir_adv_composition_plan(cpu_composition, true).selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7192374b2f889cf4aa2d60863b9ded130780407f4ed0e1a4efa4703dd9e6c35`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7192374b2f889cf4aa2d60863b9ded130780407f4ed0e1a4efa4703dd9e6c35`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7192374b2f889cf4aa2d60863b9ded130780407f4ed0e1a4efa4703dd9e6c35`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/draw_ir_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/draw_ir_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/draw_ir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/draw_ir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/draw_ir_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/draw_ir_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the additive v2 schema while keeping v1 rect and text constructors compatible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates and intersects command clips through the shared Draw IR contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores resolved advances as typed Draw IR without CSV style bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
