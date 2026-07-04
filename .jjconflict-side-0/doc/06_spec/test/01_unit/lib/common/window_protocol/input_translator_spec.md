# Input Translator Specification

> <details>

<!-- sdn-diagram:id=input_translator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=input_translator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

input_translator_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=input_translator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Input Translator Specification

## Scenarios

### key_char_to_wm_key_event

#### when key_char is nil

#### produces key_code 0 and KeyDown with correct window_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = key_char_to_wm_key_event(WindowId(value: 42), nil)
expect(evt.key_code.code).to_equal(0 as u32)
expect(evt.event_type).to_equal(WmEventType.KeyDown)
expect(evt.window_id.value).to_equal(42)
```

</details>

#### when key_char is a lowercase letter

#### maps 'a' to key_code 97 and passes window_id through

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = key_char_to_wm_key_event(WindowId(value: 7), "a")
expect(evt.key_code.code).to_equal(97 as u32)
expect(evt.key_code.name).to_equal("a")
expect(evt.window_id.value).to_equal(7)
expect(evt.event_type).to_equal(WmEventType.KeyDown)
```

</details>

#### when key_char is an uppercase letter

#### maps 'A' to key_code 65

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = key_char_to_wm_key_event(WindowId(value: 0), "A")
expect(evt.key_code.code).to_equal(65 as u32)
expect(evt.event_type).to_equal(WmEventType.KeyDown)
expect(evt.window_id.value).to_equal(0)
```

</details>

#### mouse_pos defaults

#### mouse_x and mouse_y are 0 for key events

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = key_char_to_wm_key_event(WindowId(value: 1), "z")
expect(evt.point.x).to_equal(0)
expect(evt.point.y).to_equal(0)
```

</details>

### pointer_to_wm_mouse_event

#### maps pointer down, up, and move into typed WM input events

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mods = Modifiers(shift: true, ctrl: false, alt: false, meta: false)
val down = pointer_to_wm_mouse_event(WindowId(value: 9), "pointer_down", 10, 20, mods)
val up = pointer_to_wm_mouse_event(WindowId(value: 9), "pointer_up", 11, 21, mods)
val moved = pointer_to_wm_mouse_event(WindowId(value: 9), "move", 12, 22, mods)

expect(down.event_type).to_equal(WmEventType.MouseDown)
expect(up.event_type).to_equal(WmEventType.MouseUp)
expect(moved.event_type).to_equal(WmEventType.MouseMove)
expect(down.point.x).to_equal(10)
expect(down.point.y).to_equal(20)
expect(down.modifiers.shift).to_equal(true)
```

</details>

### wheel_to_wm_scroll_event

#### preserves scroll delta, coordinates, window_id, and modifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mods = Modifiers(shift: false, ctrl: true, alt: false, meta: false)
val evt = wheel_to_wm_scroll_event(WindowId(value: 5), 30, 40, 1.5, -8.0, mods)

expect(evt.event_type).to_equal(WmEventType.Scroll)
expect(evt.window_id.value).to_equal(5)
expect(evt.point.x).to_equal(30)
expect(evt.point.y).to_equal(40)
expect(evt.scroll_dx).to_equal(1.5)
expect(evt.scroll_dy).to_equal(-8.0)
expect(evt.modifiers.ctrl).to_equal(true)
```

</details>

### ascii_code_for_key

#### uses the first character and returns 0 for unsupported or empty keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ascii_code_for_key("ab")).to_equal(97 as u32)
expect(ascii_code_for_key("")).to_equal(0 as u32)
expect(ascii_code_for_key(nil)).to_equal(0 as u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/window_protocol/input_translator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- key_char_to_wm_key_event
- pointer_to_wm_mouse_event
- wheel_to_wm_scroll_event
- ascii_code_for_key

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
