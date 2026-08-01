# Window Scene Draw Ir Layer Order Specification

> <details>

<!-- sdn-diagram:id=window_scene_draw_ir_layer_order_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_scene_draw_ir_layer_order_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_scene_draw_ir_layer_order_spec -> std
window_scene_draw_ir_layer_order_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_scene_draw_ir_layer_order_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Draw Ir Layer Order Specification

## Scenarios

### window scene Draw IR z-layer ordering

#### orders visible window batches by z-index with stable equal-layer order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = shared_wm_scene_draw_ir_composition(_layered_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

expect(composition.batches.len()).to_equal(7)
expect(composition.batches[2].embedding.surface_id).to_equal("bottom")
expect(composition.batches[3].embedding.surface_id).to_equal("middle-a")
expect(composition.batches[4].embedding.surface_id).to_equal("middle-b")
expect(composition.batches[5].embedding.surface_id).to_equal("top")
expect(composition.batches[6].embedding.component_id).to_equal("wm-taskbar-objects")
```

</details>

#### orders sparse z-index windows without losing stable equal-layer order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = shared_wm_scene_draw_ir_composition(_sparse_layered_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

expect(composition.batches.len()).to_equal(7)
expect(composition.batches[2].embedding.surface_id).to_equal("bottom")
expect(composition.batches[3].embedding.surface_id).to_equal("middle-a")
expect(composition.batches[4].embedding.surface_id).to_equal("middle-b")
expect(composition.batches[5].embedding.surface_id).to_equal("top")
expect(composition.batches[6].embedding.component_id).to_equal("wm-taskbar-objects")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- window scene Draw IR z-layer ordering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
