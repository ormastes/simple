# Widget Interact Model Specification

> <details>

<!-- sdn-diagram:id=widget_interact_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_interact_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_interact_model_spec -> std
widget_interact_model_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_interact_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Interact Model Specification

## Scenarios

### widget interaction model

#### starts at the documented initial state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = interact_state_new()
expect(s.counter).to_equal(0)
expect(s.text).to_equal("")
expect(s.caret).to_equal(0)
expect(s.scroll_offset).to_equal(0)
expect(s.anim_x).to_equal(ANIM_MIN)
```

</details>

#### increments the counter on a click inside the button

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = interact_state_new()
val s1 = on_click(s0, BTN_X + 5, BTN_Y + 5)
expect(s1.counter).to_equal(1)
val s2 = on_click(s1, BTN_X + 5, BTN_Y + 5)
expect(s2.counter).to_equal(2)
```

</details>

#### ignores a click outside the button

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = interact_state_new()
val s1 = on_click(s0, BTN_X + 5, BTN_Y + 500)
expect(s1.counter).to_equal(0)
val s2 = on_click(s1, BTN_X + 5000, BTN_Y + 5)
expect(s2.counter).to_equal(0)
```

</details>

#### maps keycodes to lowercase ascii chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(keycode_to_char(72)).to_equal("h")
expect(keycode_to_char(73)).to_equal("i")
expect(keycode_to_char(55)).to_equal("7")
expect(keycode_to_char(32)).to_equal(" ")
expect(keycode_to_char(8)).to_equal("")
```

</details>

#### appends typed printable keys to the text input

- var s = interact state new
- s = on key
- s = on key
- s = on key
- s = on key
   - Expected: s.text equals `hi 7`
   - Expected: s.caret equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = interact_state_new()
s = on_key(s, 72)   # H -> h
s = on_key(s, 73)   # I -> i
s = on_key(s, 32)   # space
s = on_key(s, 55)   # 7
expect(s.text).to_equal("hi 7")
expect(s.caret).to_equal(4)
```

</details>

#### deletes the last char on backspace and stops at empty

- var s = interact state new
- s = on key
- s = on key
   - Expected: s.text equals `ab`
- s = on key
   - Expected: s.text equals `a`
   - Expected: s.caret equals `1`
- s = on key
   - Expected: s.text equals ``
- s = on key
   - Expected: s.text equals ``
   - Expected: s.caret equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = interact_state_new()
s = on_key(s, 65)   # 'a'
s = on_key(s, 66)   # 'b'
expect(s.text).to_equal("ab")
s = on_key(s, KEY_BACKSPACE)
expect(s.text).to_equal("a")
expect(s.caret).to_equal(1)
s = on_key(s, KEY_BACKSPACE)
expect(s.text).to_equal("")
s = on_key(s, KEY_BACKSPACE)
expect(s.text).to_equal("")
expect(s.caret).to_equal(0)
```

</details>

#### scrolls the list down and clamps at the bottom

- var s = interact state new
   - Expected: s.scroll_offset equals `0`
- s = on wheel
   - Expected: s.scroll_offset equals `1`
- s = on wheel
   - Expected: s.scroll_offset equals `scroll_max()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = interact_state_new()
expect(s.scroll_offset).to_equal(0)
s = on_wheel(s, -1)
expect(s.scroll_offset).to_equal(1)
var i = 0
while i < 50:
    s = on_wheel(s, -1)
    i = i + 1
expect(s.scroll_offset).to_equal(scroll_max())
```

</details>

#### scrolls the list up and clamps at the top

- var s = interact state new
- s = on wheel
   - Expected: s.scroll_offset equals `3`
- s = on wheel
   - Expected: s.scroll_offset equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = interact_state_new()
s = on_wheel(s, -3)
expect(s.scroll_offset).to_equal(3)
var i = 0
while i < 50:
    s = on_wheel(s, 1)
    i = i + 1
expect(s.scroll_offset).to_equal(0)
```

</details>

#### scrolls via up/down arrow keys

- var s = interact state new
- s = on key
   - Expected: s.scroll_offset equals `1`
- s = on key
   - Expected: s.scroll_offset equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = interact_state_new()
s = on_key(s, KEY_ARROW_DOWN)
expect(s.scroll_offset).to_equal(1)
s = on_key(s, KEY_ARROW_UP)
expect(s.scroll_offset).to_equal(0)
```

</details>

#### bounces the animation off both walls and stays in bounds

- var s = interact state new
- s = on tick
   - Expected: in_bounds is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = interact_state_new()
var i = 0
var sign_flips = 0
var prev_dx = s.anim_dx
var in_bounds = true
# Accumulate bounds/flip facts in the loop; assert once after (the test
# runner mishandles expect() called inside a loop body in interpret mode).
while i < 400:
    s = on_tick(s)
    if s.anim_x < ANIM_MIN or s.anim_x > ANIM_MAX:
        in_bounds = false
    if s.anim_dx != prev_dx:
        sign_flips = sign_flips + 1
        prev_dx = s.anim_dx
    i = i + 1
expect(in_bounds).to_equal(true)
# over 400 ticks across a ~220px span it must have bounced both walls
expect(sign_flips).to_be_greater_than(1)
```

</details>

#### bounces the animation off the left wall

- var s = InteractState
- s = on tick
   - Expected: s.anim_x equals `ANIM_MIN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = InteractState(counter: 0, text: "", caret: 0, scroll_offset: 0, anim_x: ANIM_MIN + 2, anim_dx: -3)
s = on_tick(s)
expect(s.anim_x).to_equal(ANIM_MIN)
expect(s.anim_dx).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/ui/widget_interact_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- widget interaction model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
