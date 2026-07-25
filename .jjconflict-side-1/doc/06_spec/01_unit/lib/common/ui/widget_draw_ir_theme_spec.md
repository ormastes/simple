# Widget Draw Ir Theme Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Draw Ir Theme Specification

## Scenarios

### widget Draw IR semantic theme handoff

#### projects the selected snapshot surface and accent into the same widget tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = panel("theme-panel", "", [button("theme-button", "", "activate")])
val first = _theme_snapshot("first", 0xff010203u32, 0xfff0f1f2u32, 0xff123456u32, 0xff202122u32, 0xff303132u32, 0xff404142u32, 0xff505152u32)
val second = _theme_snapshot("second", 0xff111213u32, 0xffe0e1e2u32, 0xffabcdefu32, 0xff606162u32, 0xff707172u32, 0xff808182u32, 0xff909192u32)

val first_draw = widget_tree_to_draw_ir_with_theme(root, 160, 80, DRAW_IR_BACKEND_CPU, first)
val second_draw = widget_tree_to_draw_ir_with_theme(root, 160, 80, DRAW_IR_BACKEND_CPU, second)

expect(_command_color(first_draw, "theme-panel")).to_equal(first.material.window_fill_rgba)
expect(_command_color(second_draw, "theme-panel")).to_equal(second.material.window_fill_rgba)
expect(_command_color(first_draw, "theme-button")).to_equal(first.accent_rgba)
expect(_command_color(second_draw, "theme-button")).to_equal(second.accent_rgba)
expect(_command_color(first_draw, "theme-button") != _command_color(second_draw, "theme-button")).to_equal(true)
```

</details>

#### uses existing hover and pressed widget state as semantic theme roles

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = _theme_snapshot("states", 0xff010203u32, 0xfff0f1f2u32, 0xff123456u32, 0xff202122u32, 0xff303132u32, 0xff404142u32, 0xff505152u32)
val hovered = button("hover-button", "", "activate").set_prop("ui_hover", "true")
val pressed = button("pressed-button", "", "activate").set_prop("ui_pressed", "true")
val root = panel("state-panel", "", [hovered, pressed])

val draw = widget_tree_to_draw_ir_with_theme(root, 160, 100, DRAW_IR_BACKEND_CPU, snapshot)

expect(_command_color(draw, "hover-button")).to_equal(snapshot.material.active_title_fill_rgba)
expect(_command_color(draw, "pressed-button")).to_equal(snapshot.material.inactive_title_fill_rgba)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- widget Draw IR semantic theme handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
