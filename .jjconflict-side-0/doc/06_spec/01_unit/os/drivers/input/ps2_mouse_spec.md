# PS/2 Mouse Driver Specification

> Tests PS/2 mouse state construction, driver creation, packet parsing with sign extension and bounds clamping, button edge detection, and cursor bitmap dimensions.

<!-- sdn-diagram:id=ps2_mouse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ps2_mouse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ps2_mouse_spec -> std
ps2_mouse_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ps2_mouse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PS/2 Mouse Driver Specification

Tests PS/2 mouse state construction, driver creation, packet parsing with sign extension and bounds clamping, button edge detection, and cursor bitmap dimensions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-PS2-MOUSE |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/os/drivers/input/ps2_mouse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests PS/2 mouse state construction, driver creation, packet parsing
with sign extension and bounds clamping, button edge detection, and
cursor bitmap dimensions.

## Scenarios

### PS/2 Mouse

### MouseState

#### constructs with default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = MouseState(
    x: 400, y: 300,
    left_button: false, right_button: false, middle_button: false,
    dx: 0, dy: 0,
    screen_width: 800, screen_height: 600
)
expect(state.x).to_equal(400)
expect(state.y).to_equal(300)
expect(state.screen_width).to_equal(800)
expect(state.screen_height).to_equal(600)
expect(state.left_button).to_equal(false)
expect(state.right_button).to_equal(false)
expect(state.middle_button).to_equal(false)
```

</details>

### MouseEvent

#### constructs with edge-triggered fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = MouseEvent(
    x: 100, y: 200,
    dx: 5, dy: -3,
    left_pressed: true, right_pressed: false, middle_pressed: false,
    left_just_pressed: true, right_just_pressed: false,
    left_just_released: false
)
expect(event.x).to_equal(100)
expect(event.y).to_equal(200)
expect(event.dx).to_equal(5)
expect(event.dy).to_equal(-3)
expect(event.left_pressed).to_equal(true)
expect(event.left_just_pressed).to_equal(true)
expect(event.left_just_released).to_equal(false)
```

</details>

### Ps2Mouse.create

#### starts at screen center

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mouse = Ps2Mouse.create(800, 600)
val state = mouse.get_state()
expect(state.x).to_equal(400)
expect(state.y).to_equal(300)
```

</details>

#### starts not initialized

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mouse = Ps2Mouse.create(800, 600)
expect(mouse.is_initialized()).to_equal(false)
```

</details>

#### starts with no buttons pressed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mouse = Ps2Mouse.create(800, 600)
val state = mouse.get_state()
expect(state.left_button).to_equal(false)
expect(state.right_button).to_equal(false)
expect(state.middle_button).to_equal(false)
```

</details>

#### starts with zero deltas

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mouse = Ps2Mouse.create(800, 600)
val state = mouse.get_state()
expect(state.dx).to_equal(0)
expect(state.dy).to_equal(0)
```

</details>

#### stores screen dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mouse = Ps2Mouse.create(1024, 768)
val state = mouse.get_state()
expect(state.screen_width).to_equal(1024)
expect(state.screen_height).to_equal(768)
```

</details>

### packet parsing

#### poll returns nil when not initialized

1. var mouse = Ps2Mouse create
   - Expected: event.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mouse = Ps2Mouse.create(800, 600)
val event = mouse.poll()
expect(event.?).to_equal(false)
```

</details>

### CursorState

#### constructs with position and hotspot

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = CursorState(
    x: 100, y: 200,
    visible: true,
    hotspot_x: 1, hotspot_y: 1
)
expect(cursor.x).to_equal(100)
expect(cursor.y).to_equal(200)
expect(cursor.visible).to_equal(true)
expect(cursor.hotspot_x).to_equal(1)
expect(cursor.hotspot_y).to_equal(1)
```

</details>

#### default_cursor_state starts at origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = default_cursor_state()
expect(cursor.x).to_equal(0)
expect(cursor.y).to_equal(0)
expect(cursor.visible).to_equal(true)
```

</details>

### cursor bitmap

#### has 19 rows in bitmap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bitmap = get_cursor_bitmap()
expect(bitmap.len()).to_equal(19)
```

</details>

#### has 19 rows in mask

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = get_cursor_mask()
expect(mask.len()).to_equal(19)
```

</details>

#### CURSOR_WIDTH is 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CURSOR_WIDTH).to_equal(12)
```

</details>

#### CURSOR_HEIGHT is 19

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CURSOR_HEIGHT).to_equal(19)
```

</details>

#### first bitmap row has only top-left pixel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bitmap = get_cursor_bitmap()
# MSB = bit 11, so top-left pixel = 0b100000000000 = 2048
expect(bitmap[0]).to_equal(2048)
```

</details>

#### mask is wider than bitmap on first row

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bitmap = get_cursor_bitmap()
val mask = get_cursor_mask()
# Mask row 0: 0b110000000000 = 3072, bitmap row 0: 2048
val mask_wider = mask[0] > bitmap[0]
expect(mask_wider).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
