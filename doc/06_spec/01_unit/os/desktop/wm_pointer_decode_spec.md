# SimpleOS WM pointer step — button and kind code decode

> The SimpleOS window manager receives pointer events as raw PS/2 status bytes from `compositor.spl`'s `_handle_input_ps2` / `_ps2_wm_pointer_button_code` (bits 0/1/2 of the status byte). Before those raw codes reach `handle_pending_wm_pointer_step` in `shell.spl`, two pure decode helpers translate them into the text labels the rest of the WM understands: `wm_pointer_button_from_code` (button 0-3 -> none/left/middle/right) and `wm_pointer_kind_from_code` (kind 0-3 -> none/down/up/move). This is a compile-only smoke spec covering the decode contract in isolation — no PS/2 device or compositor bring-up required — so a future refactor of the producer side can't silently change what a given code decodes to.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS WM pointer step — button and kind code decode

The SimpleOS window manager receives pointer events as raw PS/2 status bytes from `compositor.spl`'s `_handle_input_ps2` / `_ps2_wm_pointer_button_code` (bits 0/1/2 of the status byte). Before those raw codes reach `handle_pending_wm_pointer_step` in `shell.spl`, two pure decode helpers translate them into the text labels the rest of the WM understands: `wm_pointer_button_from_code` (button 0-3 -> none/left/middle/right) and `wm_pointer_kind_from_code` (kind 0-3 -> none/down/up/move). This is a compile-only smoke spec covering the decode contract in isolation — no PS/2 device or compositor bring-up required — so a future refactor of the producer side can't silently change what a given code decodes to.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/wm_pointer_decode_spec.spl` |
| Updated | 2026-07-20 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The SimpleOS window manager receives pointer events as raw PS/2 status
bytes from `compositor.spl`'s `_handle_input_ps2` /
`_ps2_wm_pointer_button_code` (bits 0/1/2 of the status byte). Before
those raw codes reach `handle_pending_wm_pointer_step` in `shell.spl`,
two pure decode helpers translate them into the text labels the rest of
the WM understands: `wm_pointer_button_from_code` (button 0-3 ->
none/left/middle/right) and `wm_pointer_kind_from_code` (kind 0-3 ->
none/down/up/move). This is a compile-only smoke spec covering the decode
contract in isolation — no PS/2 device or compositor bring-up required —
so a future refactor of the producer side can't silently change what a
given code decodes to.

## Examples

Each in-range code decodes to its documented label; any out-of-range code
decodes to `"none"` rather than crashing or aliasing another label. Codes
1 for both button and kind (left, down) are pinned as an exact regression
pair, matching the pre-existing value from before this decode logic was
extracted into standalone helpers.

## Scenarios

### SimpleOS WM pointer step — button code decode

#### decodes 0 to none

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_button_from_code(0)).to_equal("none")
```

</details>

#### decodes 1 to left (pre-existing value, must be unchanged)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_button_from_code(1)).to_equal("left")
```

</details>

#### decodes 2 to middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_button_from_code(2)).to_equal("middle")
```

</details>

#### decodes 3 to right

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_button_from_code(3)).to_equal("right")
```

</details>

#### decodes an unknown button code to none

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_button_from_code(7)).to_equal("none")
```

</details>

### SimpleOS WM pointer step — kind code decode

#### decodes 0 to none

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_kind_from_code(0)).to_equal("none")
```

</details>

#### decodes 1 to down (pre-existing value, must be unchanged)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_kind_from_code(1)).to_equal("down")
```

</details>

#### decodes 2 to up

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_kind_from_code(2)).to_equal("up")
```

</details>

#### decodes 3 to move

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_kind_from_code(3)).to_equal("move")
```

</details>

#### decodes an unknown kind code to none

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_kind_from_code(9)).to_equal("none")
```

</details>

### SimpleOS WM pointer step — left-down regression (exact pre-fix pair)

#### still decodes the original (1, 1) pair to (left, down)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_pointer_button_from_code(1)).to_equal("left")
expect(wm_pointer_kind_from_code(1)).to_equal("down")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
