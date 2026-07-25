# Draw Ir Sdn Specification

> <details>

<!-- sdn-diagram:id=draw_ir_sdn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_sdn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_sdn_spec -> std
draw_ir_sdn_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_ir_sdn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Sdn Specification

## Scenarios

### Draw IR SDN skin

#### emits tab-indented SDN for a WM Draw IR composition

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = shared_wm_scene_draw_ir_composition(_sdn_scene(), _sdn_taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 1)
val sdn = draw_ir_to_sdn(composition)

expect(sdn).to_start_with("draw_ir schema=simple-draw-ir-v2")
expect(sdn).to_contain("\tcomposition id=wm-composite")
expect(sdn).to_contain("\tbatch id=wm-desktop")
expect(sdn).to_contain("\t\tcommand kind=rect")
expect(sdn).to_contain("source_kind=wm_scene")
```

</details>

#### round-trips all command variants and their serialized metadata

<details>
<summary>Executable SSpec</summary>

The executable source builds styled RECT, resolved-font TEXT, IMAGE, GROUP,
PORT, PATH, and EDGE commands, serializes one composition with
`draw_ir_to_sdn`, parses it with `sdn_to_draw_ir`, and checks the previously
dropped rectangles, styles, font metrics, URI, hierarchy, points, and edge
material. See the runnable source for the complete assertion set.

</details>

#### parses the legacy version-2 edge fields

<details>
<summary>Executable SSpec</summary>

The executable source parses a version-2 EDGE line using the original
`source`, `target`, and `routing` fields and verifies that all three values are
retained.

</details>

#### round-trips a WM Draw IR composition through SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition = shared_wm_scene_draw_ir_composition(_sdn_scene(), _sdn_taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 1)
val parsed = sdn_to_draw_ir(draw_ir_to_sdn(composition))

expect(parsed.schema).to_equal(composition.schema)
expect(parsed.composition_id).to_equal(composition.composition_id)
expect(parsed.scene_key).to_equal(composition.scene_key)
expect(parsed.backend_target).to_equal(composition.backend_target)
expect(parsed.batches.len()).to_equal(composition.batches.len())
expect(parsed.batches[2].batch_id).to_equal(composition.batches[2].batch_id)
expect(parsed.batches[2].embedding.surface_id).to_equal("surf1")
expect(parsed.batches[2].embedding.x).to_equal(10)
expect(parsed.batches[2].embedding.y).to_equal(40)
expect(parsed.batches[2].source.source_kind).to_equal("wm_scene")
expect(parsed.batches[2].source.source_id).to_equal("wm.window.win1")
expect(parsed.batches[2].commands.len()).to_equal(composition.batches[2].commands.len())
expect(parsed.batches[2].commands[3].kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(parsed.batches[2].commands[3].text_value).to_equal("Window One")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_sdn_spec.spl` |
| Updated | 2026-07-13 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Draw IR SDN skin

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
