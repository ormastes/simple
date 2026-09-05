# HostInputEvent — single host->widget input ingress type

> `common.ui.host_input_event` is the SOLE definition site for the ingress event every screen host (2d / gui / web / wm) hands to the widget layer. It exists because `UIEvent.MouseEvent` carries `x: f64, y: f64, button: text` while `widget_hit.widget_dispatch_click` consumes `i32, i32`, so every backend used to do its own truncation and button-name mapping and could diverge on rounding, naming and wheel sign.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HostInputEvent — single host->widget input ingress type

`common.ui.host_input_event` is the SOLE definition site for the ingress event every screen host (2d / gui / web / wm) hands to the widget layer. It exists because `UIEvent.MouseEvent` carries `x: f64, y: f64, button: text` while `widget_hit.widget_dispatch_click` consumes `i32, i32`, so every backend used to do its own truncation and button-name mapping and could diverge on rounding, naming and wheel sign.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md |
| Design | doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/ui/host_input_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`common.ui.host_input_event` is the SOLE definition site for the ingress
event every screen host (2d / gui / web / wm) hands to the widget layer.
It exists because `UIEvent.MouseEvent` carries `x: f64, y: f64,
button: text` while `widget_hit.widget_dispatch_click` consumes `i32, i32`,
so every backend used to do its own truncation and button-name mapping and
could diverge on rounding, naming and wheel sign.

This spec pins the conversions that used to be per-backend: f64 truncation,
button-name mapping (including the unknown-name fallback), the wheel sign
convention (positive = content scrolls DOWN, matching the `dy` argument of
`widget_dispatch_scroll`), and the WM file-bridge round trip including the
additive `key_code` / `ch` / `mods` / `wheel` fields — plus the
backward-compatibility guarantee that a document written with only the
historic six keys still decodes.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md

## Design

**Design:** doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md

## Research

**Research:** N/A

## Examples

A left mouse-down at (3.7, 4.2) becomes `Pointer(3, 4, HOST_BTN_LEFT, true, 0)`;
an unknown button name falls back to `HOST_BTN_NONE`; a wheel event survives
the WM file bridge with its sign intact.

## Scenarios

### HostInputEvent — constructors

#### host_pointer_down carries the button, pressed=true and no wheel

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- host_pointer_down carries the button, pressed=true and no wheel
- Build a left-button press at (12, 34)
   - Expected: tag_of(ev) equals `pointer`
   - Expected: p_x(ev) equals `12`
   - Expected: p_y(ev) equals `34`
   - Expected: p_button(ev) equals `HOST_BTN_LEFT`
   - Expected: p_pressed(ev) is true
   - Expected: p_wheel(ev) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_pointer_down carries the button, pressed=true and no wheel")
step("Build a left-button press at (12, 34)")
val ev = host_pointer_down(12, 34, HOST_BTN_LEFT)

expect(tag_of(ev)).to_equal("pointer")
expect(p_x(ev)).to_equal(12)
expect(p_y(ev)).to_equal(34)
expect(p_button(ev)).to_equal(HOST_BTN_LEFT)
expect(p_pressed(ev)).to_equal(true)
expect(p_wheel(ev)).to_equal(0)
```

</details>

#### host_pointer_up carries pressed=false with the button preserved

- host_pointer_up carries pressed=false with the button preserved
- Release the right button at (5, 6)
   - Expected: p_pressed(ev) is false
   - Expected: p_button(ev) equals `HOST_BTN_RIGHT`
   - Expected: p_wheel(ev) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_pointer_up carries pressed=false with the button preserved")
step("Release the right button at (5, 6)")
val ev = host_pointer_up(5, 6, HOST_BTN_RIGHT)

expect(p_pressed(ev)).to_equal(false)
expect(p_button(ev)).to_equal(HOST_BTN_RIGHT)
expect(p_wheel(ev)).to_equal(0)
```

</details>

#### host_pointer_move is button-NONE and pressed, so a move is not a press

- host_pointer_move is button-NONE and pressed, so a move is not a press
- Motion to (7, 8)
   - Expected: p_button(ev) equals `HOST_BTN_NONE`
   - Expected: p_pressed(ev) is true
   - Expected: p_wheel(ev) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_pointer_move is button-NONE and pressed, so a move is not a press")
step("Motion to (7, 8)")
val ev = host_pointer_move(7, 8)

expect(p_button(ev)).to_equal(HOST_BTN_NONE)
expect(p_pressed(ev)).to_equal(true)
expect(p_wheel(ev)).to_equal(0)
```

</details>

#### host_pointer_wheel carries notches and no button

- host_pointer_wheel carries notches and no button
- Three notches at (2, 3)
   - Expected: p_wheel(ev) equals `3`
   - Expected: p_button(ev) equals `HOST_BTN_NONE`
   - Expected: p_pressed(ev) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_pointer_wheel carries notches and no button")
step("Three notches at (2, 3)")
val ev = host_pointer_wheel(2, 3, 3)

expect(p_wheel(ev)).to_equal(3)
expect(p_button(ev)).to_equal(HOST_BTN_NONE)
expect(p_pressed(ev)).to_equal(false)
```

</details>

#### host_key_down / host_key_up carry code, char, mods and direction

- host_key_down / host_key_up carry code, char, mods and direction
- Shift+Ctrl 'x' down then up
   - Expected: tag_of(down) equals `key`
   - Expected: k_code(down) equals `120`
   - Expected: k_ch(down) equals `x`
   - Expected: k_mods(down) equals `mods`
   - Expected: k_down(down) is true
   - Expected: k_down(up) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_key_down / host_key_up carry code, char, mods and direction")
step("Shift+Ctrl 'x' down then up")
val mods = HOST_MOD_SHIFT + HOST_MOD_CTRL
val down = host_key_down(120, "x", mods)
val up = host_key_up(120, "x", mods)

expect(tag_of(down)).to_equal("key")
expect(k_code(down)).to_equal(120)
expect(k_ch(down)).to_equal("x")
expect(k_mods(down)).to_equal(mods)
expect(k_down(down)).to_equal(true)
expect(k_down(up)).to_equal(false)
```

</details>

#### host_resize carries the new surface size

- host_resize carries the new surface size
- Resize to 800x600
   - Expected: tag_of(ev) equals `resize`
   - Expected: r_w(ev) equals `800`
   - Expected: r_h(ev) equals `600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_resize carries the new surface size")
step("Resize to 800x600")
val ev = host_resize(800, 600)

expect(tag_of(ev)).to_equal("resize")
expect(r_w(ev)).to_equal(800)
expect(r_h(ev)).to_equal(600)
```

</details>

### HostInputEvent — button and key vocabulary

#### button names map to HOST_BTN_* and unknown names fall back to NONE

- button names map to HOST_BTN_* and unknown names fall back to NONE
- Map every known name plus two unknowns
   - Expected: host_button_from_name("left") equals `HOST_BTN_LEFT`
   - Expected: host_button_from_name("RIGHT") equals `HOST_BTN_RIGHT`
   - Expected: host_button_from_name("middle") equals `HOST_BTN_MIDDLE`
   - Expected: host_button_from_name("") equals `HOST_BTN_NONE`
   - Expected: host_button_from_name("thumb4") equals `HOST_BTN_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("button names map to HOST_BTN_* and unknown names fall back to NONE")
step("Map every known name plus two unknowns")
expect(host_button_from_name("left")).to_equal(HOST_BTN_LEFT)
expect(host_button_from_name("RIGHT")).to_equal(HOST_BTN_RIGHT)
expect(host_button_from_name("middle")).to_equal(HOST_BTN_MIDDLE)
expect(host_button_from_name("")).to_equal(HOST_BTN_NONE)
expect(host_button_from_name("thumb4")).to_equal(HOST_BTN_NONE)
```

</details>

#### host_button_name inverts the mapping, with NONE mapping to empty

- host_button_name inverts the mapping, with NONE mapping to empty
- Round-trip each code back to its name
   - Expected: host_button_name(HOST_BTN_LEFT) equals `left`
   - Expected: host_button_name(HOST_BTN_RIGHT) equals `right`
   - Expected: host_button_name(HOST_BTN_MIDDLE) equals `middle`
   - Expected: host_button_name(HOST_BTN_NONE) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_button_name inverts the mapping, with NONE mapping to empty")
step("Round-trip each code back to its name")
expect(host_button_name(HOST_BTN_LEFT)).to_equal("left")
expect(host_button_name(HOST_BTN_RIGHT)).to_equal("right")
expect(host_button_name(HOST_BTN_MIDDLE)).to_equal("middle")
expect(host_button_name(HOST_BTN_NONE)).to_equal("")
```

</details>

#### host_key_text prefers the printable char and falls back to the key name

- host_key_text prefers the printable char and falls back to the key name
- A char key and a bare backspace keycode
   - Expected: host_key_text(host_key_down(120, "x", 0)) equals `x`
   - Expected: host_key_text(host_key_down(8, "", 0)) equals `backspace`
   - Expected: host_key_name(37) equals `left`
   - Expected: host_key_name(9999) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_key_text prefers the printable char and falls back to the key name")
step("A char key and a bare backspace keycode")
expect(host_key_text(host_key_down(120, "x", 0))).to_equal("x")
expect(host_key_text(host_key_down(8, "", 0))).to_equal("backspace")
expect(host_key_name(37)).to_equal("left")
expect(host_key_name(9999)).to_equal("")
```

</details>

### HostInputEvent — UIEvent seam (the lossy conversion, done once)

#### MouseEvent down truncates f64 coords and maps the button name

- MouseEvent down truncates f64 coords and maps the button name
- MouseEvent(3.7, 4.2, "left", "down")
   - Expected: ev != nil is true
   - Expected: p_x(ev!) equals `3`
   - Expected: p_y(ev!) equals `4`
   - Expected: p_button(ev!) equals `HOST_BTN_LEFT`
   - Expected: p_pressed(ev!) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("MouseEvent down truncates f64 coords and maps the button name")
step("MouseEvent(3.7, 4.2, \"left\", \"down\")")
val ev = host_input_from_ui_event(
    UIEvent.MouseEvent(x: 3.7, y: 4.2, button: "left", kind: "down")
)

expect(ev != nil).to_equal(true)
expect(p_x(ev!)).to_equal(3)
expect(p_y(ev!)).to_equal(4)
expect(p_button(ev!)).to_equal(HOST_BTN_LEFT)
expect(p_pressed(ev!)).to_equal(true)
```

</details>

#### MouseEvent up is pressed=false and an unknown button name becomes NONE

- MouseEvent up is pressed=false and an unknown button name becomes NONE
- An 'up' with a button name the widget layer has never heard of
   - Expected: p_pressed(ev!) is false
   - Expected: p_button(ev!) equals `HOST_BTN_NONE`
   - Expected: p_x(ev!) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("MouseEvent up is pressed=false and an unknown button name becomes NONE")
step("An 'up' with a button name the widget layer has never heard of")
val ev = host_input_from_ui_event(
    UIEvent.MouseEvent(x: 9.9, y: 1.1, button: "pinky", kind: "up")
)

expect(p_pressed(ev!)).to_equal(false)
expect(p_button(ev!)).to_equal(HOST_BTN_NONE)
expect(p_x(ev!)).to_equal(9)
```

</details>

#### ScrollEvent dy keeps its sign: positive dy stays positive wheel

- ScrollEvent dy keeps its sign: positive dy stays positive wheel
- widget_dispatch_scroll takes dy with the same sign, so no negation may creep in
   - Expected: p_wheel(down!) equals `3`
   - Expected: p_wheel(up!) equals `-2`
   - Expected: p_button(down!) equals `HOST_BTN_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ScrollEvent dy keeps its sign: positive dy stays positive wheel")
step("widget_dispatch_scroll takes dy with the same sign, so no negation may creep in")
val down = host_input_from_ui_event(
    UIEvent.ScrollEvent(x: 4.0, y: 5.0, dx: 0.0, dy: 3.0)
)
val up = host_input_from_ui_event(
    UIEvent.ScrollEvent(x: 4.0, y: 5.0, dx: 0.0, dy: -2.0)
)

expect(p_wheel(down!)).to_equal(3)
expect(p_wheel(up!)).to_equal(-2)
expect(p_button(down!)).to_equal(HOST_BTN_NONE)
```

</details>

#### UIEvent variants with no host input convert to nil

- UIEvent variants with no host input convert to nil
- Action carries no pointer, key or size
   - Expected: host_input_from_ui_event(UIEvent.Action(name: "save")) == nil is true
   - Expected: host_input_from_ui_event(UIEvent.Quit) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("UIEvent variants with no host input convert to nil")
step("Action carries no pointer, key or size")
expect(host_input_from_ui_event(UIEvent.Action(name: "save")) == nil).to_equal(true)
expect(host_input_from_ui_event(UIEvent.Quit) == nil).to_equal(true)
```

</details>

#### host_input_to_ui_event round-trips a left press back to a MouseEvent

- host_input_to_ui_event round-trips a left press back to a MouseEvent
- Pointer -> UIEvent -> Pointer
   - Expected: p_x(again!) equals `11`
   - Expected: p_y(again!) equals `22`
   - Expected: p_button(again!) equals `HOST_BTN_LEFT`
   - Expected: p_pressed(again!) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_input_to_ui_event round-trips a left press back to a MouseEvent")
step("Pointer -> UIEvent -> Pointer")
val back = host_input_to_ui_event(host_pointer_down(11, 22, HOST_BTN_LEFT))
val again = host_input_from_ui_event(back!)

expect(p_x(again!)).to_equal(11)
expect(p_y(again!)).to_equal(22)
expect(p_button(again!)).to_equal(HOST_BTN_LEFT)
expect(p_pressed(again!)).to_equal(true)
```

</details>

#### host_input_to_ui_event turns a wheel into a ScrollEvent, not a MouseEvent

- host_input_to_ui_event turns a wheel into a ScrollEvent, not a MouseEvent
- Wheel +2 must survive as dy=+2
   - Expected: p_wheel(again!) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host_input_to_ui_event turns a wheel into a ScrollEvent, not a MouseEvent")
step("Wheel +2 must survive as dy=+2")
val back = host_input_to_ui_event(host_pointer_wheel(1, 2, 2))
val again = host_input_from_ui_event(back!)

expect(p_wheel(again!)).to_equal(2)
```

</details>

### HostInputEvent — WM file-bridge seam

#### a historic key event still decodes: keycode arrives in `button`

- a historic key event still decodes: keycode arrives in `button`
- wm_fs_key_event has always shipped the keycode in `button`
   - Expected: tag_of(ev!) equals `key`
   - Expected: k_code(ev!) equals `65`
   - Expected: k_down(ev!) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a historic key event still decodes: keycode arrives in `button`")
step("wm_fs_key_event has always shipped the keycode in `button`")
val wire = wm_fs_app_event_encode(wm_fs_key_event(7, 65, true))
val ev = host_input_from_wm_fs_event(wm_fs_app_event_decode(wire))

expect(tag_of(ev!)).to_equal("key")
expect(k_code(ev!)).to_equal(65)
expect(k_down(ev!)).to_equal(true)
```

</details>

#### a char/mods key event round-trips through the additive fields

- a char/mods key event round-trips through the additive fields
- wm_fs_key_char_event -> encode -> decode -> HostInputEvent
   - Expected: decoded.ch equals `x`
   - Expected: decoded.key_code equals `120`
   - Expected: decoded.mods equals `HOST_MOD_CTRL`
   - Expected: k_ch(ev!) equals `x`
   - Expected: k_code(ev!) equals `120`
   - Expected: k_mods(ev!) equals `HOST_MOD_CTRL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a char/mods key event round-trips through the additive fields")
step("wm_fs_key_char_event -> encode -> decode -> HostInputEvent")
val src = wm_fs_key_char_event(9, 120, "x", HOST_MOD_CTRL, true)
val decoded = wm_fs_app_event_decode(wm_fs_app_event_encode(src))

expect(decoded.ch).to_equal("x")
expect(decoded.key_code).to_equal(120)
expect(decoded.mods).to_equal(HOST_MOD_CTRL)

val ev = host_input_from_wm_fs_event(decoded)
expect(k_ch(ev!)).to_equal("x")
expect(k_code(ev!)).to_equal(120)
expect(k_mods(ev!)).to_equal(HOST_MOD_CTRL)
```

</details>

#### a wheel event crosses the bridge with its sign intact

- a wheel event crosses the bridge with its sign intact
- wm_fs_wheel_event -> encode -> decode -> HostInputEvent
   - Expected: p_wheel(ev!) equals `2`
   - Expected: p_x(ev!) equals `40`
   - Expected: p_y(ev!) equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a wheel event crosses the bridge with its sign intact")
step("wm_fs_wheel_event -> encode -> decode -> HostInputEvent")
val decoded = wm_fs_app_event_decode(wm_fs_app_event_encode(wm_fs_wheel_event(3, 40, 50, 2)))
val ev = host_input_from_wm_fs_event(decoded)

expect(p_wheel(ev!)).to_equal(2)
expect(p_x(ev!)).to_equal(40)
expect(p_y(ev!)).to_equal(50)
```

</details>

#### a pointer press round-trips through host_input_to_wm_fs_event

- a pointer press round-trips through host_input_to_wm_fs_event
- HostInputEvent -> WmFsAppEvent -> encode -> decode -> HostInputEvent
   - Expected: p_x(ev!) equals `60`
   - Expected: p_y(ev!) equals `70`
   - Expected: p_button(ev!) equals `HOST_BTN_LEFT`
   - Expected: p_pressed(ev!) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a pointer press round-trips through host_input_to_wm_fs_event")
step("HostInputEvent -> WmFsAppEvent -> encode -> decode -> HostInputEvent")
val wire = wm_fs_app_event_encode(host_input_to_wm_fs_event(4, host_pointer_down(60, 70, HOST_BTN_LEFT)))
val ev = host_input_from_wm_fs_event(wm_fs_app_event_decode(wire))

expect(p_x(ev!)).to_equal(60)
expect(p_y(ev!)).to_equal(70)
expect(p_button(ev!)).to_equal(HOST_BTN_LEFT)
expect(p_pressed(ev!)).to_equal(true)
```

</details>

#### BACKWARD COMPAT: a document with only the historic six keys decodes with new fields defaulted

- BACKWARD COMPAT: a document with only the historic six keys decodes with new fields defaulted
- Hand-write the pre-extension wire format — no key_code/ch/mods/wheel lines
   - Expected: decoded.seq equals `2`
   - Expected: decoded.kind equals `down`
   - Expected: decoded.x equals `15`
   - Expected: decoded.y equals `25`
   - Expected: decoded.button equals `1`
   - Expected: decoded.pressed is true
   - Expected: decoded.key_code equals `0`
   - Expected: decoded.ch equals ``
   - Expected: decoded.mods equals `0`
   - Expected: decoded.wheel equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("BACKWARD COMPAT: a document with only the historic six keys decodes with new fields defaulted")
step("Hand-write the pre-extension wire format — no key_code/ch/mods/wheel lines")
val legacy = "seq=2\nkind=down\nx=15\ny=25\nbutton=1\npressed=true\n"
val decoded = wm_fs_app_event_decode(legacy)

expect(decoded.seq).to_equal(2)
expect(decoded.kind).to_equal("down")
expect(decoded.x).to_equal(15)
expect(decoded.y).to_equal(25)
expect(decoded.button).to_equal(1)
expect(decoded.pressed).to_equal(true)
expect(decoded.key_code).to_equal(0)
expect(decoded.ch).to_equal("")
expect(decoded.mods).to_equal(0)
expect(decoded.wheel).to_equal(0)
```

</details>

#### the historic six keys are still emitted first and unchanged

- the historic six keys are still emitted first and unchanged
- Old readers scan line-by-line, so the prefix must be byte-stable
   - Expected: wire.starts_with("seq=1\nkind=down\nx=3\ny=4\nbutton=1\npressed=true\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the historic six keys are still emitted first and unchanged")
step("Old readers scan line-by-line, so the prefix must be byte-stable")
val wire = wm_fs_app_event_encode(wm_fs_app_event(1, "down", 3, 4, HOST_BTN_LEFT, true))

expect(wire.starts_with("seq=1\nkind=down\nx=3\ny=4\nbutton=1\npressed=true\n")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md`
- **Design:** `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d68b032ad07c8ecbb67e318b246560c941ab8982df8731e0b4496288d2bd7843`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d68b032ad07c8ecbb67e318b246560c941ab8982df8731e0b4496288d2bd7843`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d68b032ad07c8ecbb67e318b246560c941ab8982df8731e0b4496288d2bd7843`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/host_input_event_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/host_input_event_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/host_input_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/host_input_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/host_input_event_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 32 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/host_input_event_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'host_pointer_down carries the button, pressed=true and no wheel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/host_input_event_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'host_pointer_up carries pressed=false with the button preserved' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/host_input_event_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'host_pointer_move is button-NONE and pressed, so a move is not a press' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
