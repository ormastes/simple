# DrawIrV3Scene & Showcase Host Gate Specification

> Verifies end-to-end `DrawIrV3Scene` generation, 1x/2x HiDPI raster parity across `raster_scene_argb`, `raster_scene_argb_scaled`, and `Screen2dHost`, and deterministic input/scale routing on `ScreenGuiHost`.

<!-- sdn-diagram:id=draw_ir_v3_scene_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_v3_scene_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_v3_scene_gate_spec -> showcase_core
draw_ir_v3_scene_gate_spec -> scene_raster
draw_ir_v3_scene_gate_spec -> host_2d
draw_ir_v3_scene_gate_spec -> host_gui
```

</details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SGUI-V3-GATE-001 |
| Category | GUI / Rendering |
| Status | Verified |
| Requirements | REQ-SGUI-006, REQ-SGUI-008, REQ-SGUI-009 |
| Plan | `doc/03_plan/sys_test/simple_gui_completion.md` |
| Design | `doc/05_design/simple_gui_completion.md` |
| Source | `test/03_system/gui/draw_ir_v3_scene_gate_spec.spl` |
| Updated | 2026-11-28 |

## Overview

Covers system-level `DrawIrV3Scene` verification across software and 2D hosts:
1. `showcase_scene` produces non-empty `DrawIrV3Scene` commands whose ARGB checksum is deterministic across repeated frames.
2. `raster_scene_argb_scaled(scene, w * 2, h * 2, 2)` preserves exact 2x2 device-block parity over `raster_scene_argb(scene, w, h)`.
3. `Screen2dHost` renders the showcase scene across scripted pointer/key inputs without regressions, matching `ScreenGuiHost` logical/physical scale conversion helpers.
