# Window Scene Draw Ir Specification

> <details>

<!-- sdn-diagram:id=window_scene_draw_ir_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_scene_draw_ir_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_scene_draw_ir_spec -> std
window_scene_draw_ir_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_scene_draw_ir_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Draw Ir Specification

## Scenarios

### window scene Draw IR projection

#### projects the window manager chrome and windows into composed Draw IR batches

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = _scene()
val composition = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

expect(composition.composition_id).to_equal("wm-composite")
expect(composition.scene_key).to_equal(shared_wm_scene_layout_key(scene))
expect(composition.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(composition.batches.len()).to_equal(5)
expect(composition.batches[0].embedding.component_id).to_equal("desktop")
expect(composition.batches[1].embedding.component_id).to_equal("wm-chrome")
expect(composition.batches[2].embedding.surface_id).to_equal("surf1")
expect(composition.batches[3].embedding.surface_id).to_equal("surf2")
expect(composition.batches[4].embedding.component_id).to_equal("wm-taskbar-objects")
expect(composition.batches[0].source.source_kind).to_equal(DRAW_IR_SOURCE_WM_SCENE)
expect(composition.batches[1].source.source_id).to_equal("wm.chrome")
expect(composition.batches[2].source.source_id).to_equal("wm.window.win1")
expect(composition.batches[2].source.style_key).to_equal("wm.window")
expect(composition.batches[2].source.style_revision).to_contain("xy=10,40")
expect(composition.batches[2].source.style_revision).to_contain("size=300x200")
expect(composition.batches[2].embedding.x).to_equal(10)
expect(composition.batches[2].embedding.y).to_equal(40)
expect(composition.batches[3].embedding.x).to_equal(80)
expect(composition.batches[3].embedding.y).to_equal(120)
expect(composition.batches[3].commands[0].kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(composition.batches[3].commands[6].kind).to_equal(DRAW_IR_COMMAND_TEXT)
```

</details>

#### keeps Draw IR source revisions stable for unchanged scenes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = _scene()
val first = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val second = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

expect(second.batches[0].source.style_revision).to_equal(first.batches[0].source.style_revision)
expect(second.batches[1].source.style_revision).to_equal(first.batches[1].source.style_revision)
expect(second.batches[2].source.style_revision).to_equal(first.batches[2].source.style_revision)
expect(second.batches[3].source.style_revision).to_equal(first.batches[3].source.style_revision)
```

</details>

#### enriches WM window boxes with hit clip and z-index metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val window_batch = composition.batches[2]
val body = window_batch.commands[1]
val titlebar = window_batch.commands[2]

expect(body.hit_rect.present).to_equal(true)
expect(body.hit_rect.width).to_equal(300)
expect(body.clip_rect.present).to_equal(true)
expect(body.clip_rect.height).to_equal(200)
expect(body.computed_style[0].key).to_equal("source")
expect(body.computed_style[1].value).to_equal("body")
expect(body.computed_style[2].key).to_equal("z-index")
expect(titlebar.hit_rect.height).to_equal(28)
expect(titlebar.computed_style[1].value).to_equal("titlebar")
```

</details>

#### lets Simple 2D plan a GPU-targeted WM composition with CPU fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val plan = simple_2d_draw_ir_adv_composition_plan(composition, false)

expect(plan.composition_id).to_equal("wm-composite")
expect(plan.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(plan.selected_backend).to_equal("cpu")
expect(plan.batch_count).to_equal(5)
expect(plan.command_count).to_equal(34)
expect(plan.fallback_required).to_equal(true)
```

</details>

#### changes composition scene key after drag and rejects stale event translation cache

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = _scene()
val first = shared_wm_translate_pointer_event(scene, _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2, DRAW_IR_BACKEND_GPU)
val moved = shared_wm_drag_window(scene, "surf2", 100, 0)
val original_composition = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val moved_composition = shared_wm_scene_draw_ir_composition(moved, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val stale_checked = shared_wm_translate_pointer_event_cached(moved, _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2, DRAW_IR_BACKEND_GPU, first.cache)

expect(first.translation.scene_key).to_equal(shared_wm_scene_layout_key(scene))
expect(moved_composition.scene_key).to_equal(shared_wm_scene_layout_key(moved))
expect(moved_composition.batches[2].source.style_revision).to_equal(original_composition.batches[2].source.style_revision)
expect(original_composition.batches[3].source.style_revision).to_contain("xy=80,120")
expect(moved_composition.batches[3].source.style_revision).to_contain("xy=180,120")
expect(stale_checked.translation.cache_hit).to_equal(false)
expect(stale_checked.translation.stale_cache_rejected).to_equal(true)
expect(stale_checked.translation.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
```

</details>

#### maps translated WM events to draw processing batch context

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = _scene()
val composition = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val translation = shared_wm_translate_pointer_event(scene, _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2, DRAW_IR_BACKEND_GPU).translation
val context = draw_ir_event_target_context(
    composition,
    translation.scene_key,
    translation.input_key,
    translation.action,
    translation.target_id,
    translation.component_kind,
    translation.local_x,
    translation.local_y,
    translation.backend_target
)

expect(context.resolved).to_equal(true)
expect(context.stale_scene_rejected).to_equal(false)
expect(context.batch_id).to_equal("window-win2")
expect(context.surface_id).to_equal("surf2")
expect(context.component_id).to_equal("win2")
expect(context.component_kind).to_equal("window")
expect(context.batch_local_x).to_equal(10)
expect(context.batch_local_y).to_equal(5)
expect(context.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- window scene Draw IR projection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
