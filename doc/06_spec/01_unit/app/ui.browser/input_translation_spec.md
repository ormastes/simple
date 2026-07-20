# Browser Event Bridge — mouse button translation

> `app.ui.browser.event_bridge.translate_mouse_event` is the pure translator that turns a raw browser mouse event (x, y, button code, action string) into the engine's `UIEvent`: left button maps to the touch-style `TouchPress`/`TouchRelease`/`TouchMove` events, middle and right buttons map to `MouseEvent` with an explicit button/kind label, and anything the browser sends that the engine doesn't recognize maps to `nil` (dropped) rather than crashing or mis-routing. This is a compile-only smoke spec — no winit / FFI / compositor bring-up required — so the translation table can be verified in isolation from the windowing stack.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Event Bridge — mouse button translation

`app.ui.browser.event_bridge.translate_mouse_event` is the pure translator that turns a raw browser mouse event (x, y, button code, action string) into the engine's `UIEvent`: left button maps to the touch-style `TouchPress`/`TouchRelease`/`TouchMove` events, middle and right buttons map to `MouseEvent` with an explicit button/kind label, and anything the browser sends that the engine doesn't recognize maps to `nil` (dropped) rather than crashing or mis-routing. This is a compile-only smoke spec — no winit / FFI / compositor bring-up required — so the translation table can be verified in isolation from the windowing stack.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.browser/input_translation_spec.spl` |
| Updated | 2026-07-20 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`app.ui.browser.event_bridge.translate_mouse_event` is the pure translator
that turns a raw browser mouse event (x, y, button code, action string)
into the engine's `UIEvent`: left button maps to the touch-style
`TouchPress`/`TouchRelease`/`TouchMove` events, middle and right buttons
map to `MouseEvent` with an explicit button/kind label, and anything the
browser sends that the engine doesn't recognize maps to `nil` (dropped)
rather than crashing or mis-routing. This is a compile-only smoke spec —
no winit / FFI / compositor bring-up required — so the translation table
can be verified in isolation from the windowing stack.

## Examples

Left press/release become `TouchPress`/`TouchRelease` carrying the exact
coordinates. Middle and right press/release become `MouseEvent` carrying
`button: "middle"|"right"` and `kind: "down"|"up"`. Any button on a move
action becomes `TouchMove` (button is irrelevant while moving). An
unrecognized button code, or an unrecognized action string, both resolve
to `nil` instead of a malformed event.

## Scenarios

### Browser Event Bridge — mouse button translation

#### maps left press (button=0) to TouchPress

- Translate a left-button press at (120, 240)
- UIEvent TouchPress
- fail test
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a left-button press at (120, 240)")
val raw = translate_mouse_event(120, 240, 0, "press")
if val ev = raw.?:
    match ev:
        UIEvent.TouchPress(x, y) =>
            expect(x == 120).to_be_true()
            expect(y == 240).to_be_true()
        _ =>
            fail_test("expected TouchPress(120, 240), got a different UIEvent variant")
else:
    fail_test("expected TouchPress(120, 240) but translate_mouse_event returned nil")
```

</details>

#### maps left release (button=0) to TouchRelease

- Translate a left-button release at (120, 240)
- UIEvent TouchRelease
- fail test
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a left-button release at (120, 240)")
val raw = translate_mouse_event(120, 240, 0, "release")
if val ev = raw.?:
    match ev:
        UIEvent.TouchRelease(x, y) =>
            expect(x == 120).to_be_true()
            expect(y == 240).to_be_true()
        _ =>
            fail_test("expected TouchRelease(120, 240), got a different UIEvent variant")
else:
    fail_test("expected TouchRelease(120, 240) but translate_mouse_event returned nil")
```

</details>

#### maps middle press (button=1) to MouseEvent(button: middle, kind: down)

- Translate a middle-button press at (50, 60)
- UIEvent MouseEvent
- fail test
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a middle-button press at (50, 60)")
val raw = translate_mouse_event(50, 60, 1, "press")
if val ev = raw.?:
    match ev:
        UIEvent.MouseEvent(x, y, button, kind) =>
            expect(x == 50.0).to_be_true()
            expect(y == 60.0).to_be_true()
            expect(button == "middle").to_be_true()
            expect(kind == "down").to_be_true()
        _ =>
            fail_test("expected MouseEvent(button: middle, kind: down), got a different UIEvent variant")
else:
    fail_test("expected MouseEvent(button: middle, kind: down) but translate_mouse_event returned nil")
```

</details>

#### maps middle release (button=1) to MouseEvent(button: middle, kind: up)

- Translate a middle-button release at (50, 60)
- UIEvent MouseEvent
- fail test
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a middle-button release at (50, 60)")
val raw = translate_mouse_event(50, 60, 1, "release")
if val ev = raw.?:
    match ev:
        UIEvent.MouseEvent(x, y, button, kind) =>
            expect(button == "middle").to_be_true()
            expect(kind == "up").to_be_true()
        _ =>
            fail_test("expected MouseEvent(button: middle, kind: up), got a different UIEvent variant")
else:
    fail_test("expected MouseEvent(button: middle, kind: up) but translate_mouse_event returned nil")
```

</details>

#### maps right press (button=2) to MouseEvent(button: right, kind: down)

- Translate a right-button press at (10, 20)
- UIEvent MouseEvent
- fail test
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a right-button press at (10, 20)")
val raw = translate_mouse_event(10, 20, 2, "press")
if val ev = raw.?:
    match ev:
        UIEvent.MouseEvent(x, y, button, kind) =>
            expect(x == 10.0).to_be_true()
            expect(y == 20.0).to_be_true()
            expect(button == "right").to_be_true()
            expect(kind == "down").to_be_true()
        _ =>
            fail_test("expected MouseEvent(button: right, kind: down), got a different UIEvent variant")
else:
    fail_test("expected MouseEvent(button: right, kind: down) but translate_mouse_event returned nil")
```

</details>

#### maps right release (button=2) to MouseEvent(button: right, kind: up)

- Translate a right-button release at (10, 20)
- UIEvent MouseEvent
- fail test
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a right-button release at (10, 20)")
val raw = translate_mouse_event(10, 20, 2, "release")
if val ev = raw.?:
    match ev:
        UIEvent.MouseEvent(x, y, button, kind) =>
            expect(button == "right").to_be_true()
            expect(kind == "up").to_be_true()
        _ =>
            fail_test("expected MouseEvent(button: right, kind: up), got a different UIEvent variant")
else:
    fail_test("expected MouseEvent(button: right, kind: up) but translate_mouse_event returned nil")
```

</details>

#### maps move regardless of button to TouchMove

- Translate a move action while the left button is held
- UIEvent TouchMove
- fail test
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a move action while the left button is held")
val raw = translate_mouse_event(5, 6, 0, "move")
if val ev = raw.?:
    match ev:
        UIEvent.TouchMove(x, y) =>
            expect(x == 5).to_be_true()
            expect(y == 6).to_be_true()
        _ =>
            fail_test("expected TouchMove(5, 6), got a different UIEvent variant")
else:
    fail_test("expected TouchMove(5, 6) but translate_mouse_event returned nil")
```

</details>

#### maps an unknown button code (3) on press to nil

- Translate a press with a button code the engine does not recognize


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a press with a button code the engine does not recognize")
val raw = translate_mouse_event(1, 1, 3, "press")
expect(raw == nil).to_be_true()
```

</details>

#### maps an unknown action to nil

- Translate an action string the engine does not recognize


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate an action string the engine does not recognize")
val raw = translate_mouse_event(1, 1, 0, "drag")
expect(raw == nil).to_be_true()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
