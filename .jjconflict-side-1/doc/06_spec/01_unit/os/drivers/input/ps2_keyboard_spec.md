# PS/2 Keyboard Driver Specification

> Tests PS/2 keyboard scancode-to-key mapping, modifier state tracking, and key-to-character conversion with shift/caps awareness.

<!-- sdn-diagram:id=ps2_keyboard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ps2_keyboard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ps2_keyboard_spec -> std
ps2_keyboard_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ps2_keyboard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PS/2 Keyboard Driver Specification

Tests PS/2 keyboard scancode-to-key mapping, modifier state tracking, and key-to-character conversion with shift/caps awareness.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-PS2 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/os/drivers/input/ps2_keyboard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests PS/2 keyboard scancode-to-key mapping, modifier state tracking,
and key-to-character conversion with shift/caps awareness.

## Scenarios

### PS/2 Keyboard

### scancode_to_key

#### maps 0x1E to Key.A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x1E)
expect(key).to_equal(Key.A)
```

</details>

#### maps 0x39 to Key.Space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x39)
expect(key).to_equal(Key.Space)
```

</details>

#### maps 0x1C to Key.Enter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x1C)
expect(key).to_equal(Key.Enter)
```

</details>

#### maps 0x01 to Key.Escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x01)
expect(key).to_equal(Key.Escape)
```

</details>

#### maps 0x0E to Key.Backspace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x0E)
expect(key).to_equal(Key.Backspace)
```

</details>

#### maps 0x0F to Key.Tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x0F)
expect(key).to_equal(Key.Tab)
```

</details>

#### maps 0x2A to Key.LeftShift

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x2A)
expect(key).to_equal(Key.LeftShift)
```

</details>

#### maps 0x36 to Key.RightShift

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x36)
expect(key).to_equal(Key.RightShift)
```

</details>

#### maps 0x1D to Key.LeftCtrl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x1D)
expect(key).to_equal(Key.LeftCtrl)
```

</details>

#### maps 0x38 to Key.LeftAlt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0x38)
expect(key).to_equal(Key.LeftAlt)
```

</details>

#### maps letter scancodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(scancode_to_key(0x10)).to_equal(Key.Q)
expect(scancode_to_key(0x11)).to_equal(Key.W)
expect(scancode_to_key(0x12)).to_equal(Key.E)
expect(scancode_to_key(0x13)).to_equal(Key.R)
expect(scancode_to_key(0x14)).to_equal(Key.T)
expect(scancode_to_key(0x15)).to_equal(Key.Y)
```

</details>

#### maps number scancodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(scancode_to_key(0x02)).to_equal(Key.Num1)
expect(scancode_to_key(0x03)).to_equal(Key.Num2)
expect(scancode_to_key(0x0B)).to_equal(Key.Num0)
```

</details>

#### returns Unknown for unmapped scancode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = scancode_to_key(0xFF)
expect(key).to_equal(Key.Unknown)
```

</details>

### Ps2Keyboard modifier tracking

#### starts with shift_held false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
expect(kb.shift_held).to_equal(false)
```

</details>

#### starts with ctrl_held false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
expect(kb.ctrl_held).to_equal(false)
```

</details>

#### starts with alt_held false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
expect(kb.alt_held).to_equal(false)
```

</details>

#### starts with caps_lock false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
expect(kb.caps_lock).to_equal(false)
```

</details>

#### sets shift_held on LeftShift press

1. var kb = Ps2Keyboard new
2. kb update modifiers press
   - Expected: kb.shift_held is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kb = Ps2Keyboard.new()
kb.update_modifiers_press(Key.LeftShift)
expect(kb.shift_held).to_equal(true)
```

</details>

#### sets shift_held on RightShift press

1. var kb = Ps2Keyboard new
2. kb update modifiers press
   - Expected: kb.shift_held is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kb = Ps2Keyboard.new()
kb.update_modifiers_press(Key.RightShift)
expect(kb.shift_held).to_equal(true)
```

</details>

#### clears shift_held on LeftShift release

1. var kb = Ps2Keyboard new
2. kb update modifiers press
3. kb update modifiers release
   - Expected: kb.shift_held is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kb = Ps2Keyboard.new()
kb.update_modifiers_press(Key.LeftShift)
kb.update_modifiers_release(Key.LeftShift)
expect(kb.shift_held).to_equal(false)
```

</details>

#### sets ctrl_held on LeftCtrl press

1. var kb = Ps2Keyboard new
2. kb update modifiers press
   - Expected: kb.ctrl_held is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kb = Ps2Keyboard.new()
kb.update_modifiers_press(Key.LeftCtrl)
expect(kb.ctrl_held).to_equal(true)
```

</details>

#### clears ctrl_held on LeftCtrl release

1. var kb = Ps2Keyboard new
2. kb update modifiers press
3. kb update modifiers release
   - Expected: kb.ctrl_held is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kb = Ps2Keyboard.new()
kb.update_modifiers_press(Key.LeftCtrl)
kb.update_modifiers_release(Key.LeftCtrl)
expect(kb.ctrl_held).to_equal(false)
```

</details>

#### toggles caps_lock on CapsLock press

1. var kb = Ps2Keyboard new
2. kb update modifiers press
   - Expected: kb.caps_lock is true
3. kb update modifiers press
   - Expected: kb.caps_lock is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kb = Ps2Keyboard.new()
kb.update_modifiers_press(Key.CapsLock)
expect(kb.caps_lock).to_equal(true)
kb.update_modifiers_press(Key.CapsLock)
expect(kb.caps_lock).to_equal(false)
```

</details>

### key_to_char

#### converts Key.A to lowercase a

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
val ch = kb.key_to_char(Key.A)
expect(ch.?).to_equal(true)
expect(ch.unwrap()).to_equal("a")
```

</details>

#### converts Key.A to uppercase A with shift

1. var kb = Ps2Keyboard new
2. kb update modifiers press
   - Expected: ch.? is true
   - Expected: ch.unwrap() equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kb = Ps2Keyboard.new()
kb.update_modifiers_press(Key.LeftShift)
val ch = kb.key_to_char(Key.A)
expect(ch.?).to_equal(true)
expect(ch.unwrap()).to_equal("A")
```

</details>

#### converts Key.A to uppercase A with caps lock

1. var kb = Ps2Keyboard new
2. kb update modifiers press
   - Expected: ch.? is true
   - Expected: ch.unwrap() equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kb = Ps2Keyboard.new()
kb.update_modifiers_press(Key.CapsLock)
val ch = kb.key_to_char(Key.A)
expect(ch.?).to_equal(true)
expect(ch.unwrap()).to_equal("A")
```

</details>

#### converts Key.Space to space

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
val ch = kb.key_to_char(Key.Space)
expect(ch.?).to_equal(true)
expect(ch.unwrap()).to_equal(" ")
```

</details>

#### converts Key.Enter to newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
val ch = kb.key_to_char(Key.Enter)
expect(ch.?).to_equal(true)
expect(ch.unwrap()).to_equal("\n")
```

</details>

#### converts Key.Num0 to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
val ch = kb.key_to_char(Key.Num0)
expect(ch.?).to_equal(true)
expect(ch.unwrap()).to_equal("0")
```

</details>

#### returns nil for Key.Escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
val ch = kb.key_to_char(Key.Escape)
expect(ch.?).to_equal(false)
```

</details>

#### returns nil for Key.Unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kb = Ps2Keyboard.new()
val ch = kb.key_to_char(Key.Unknown)
expect(ch.?).to_equal(false)
```

</details>

### KeyEvent

#### constructs Press event

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = KeyEvent.Press(key: Key.A)
expect(event).to_equal(KeyEvent.Press(key: Key.A))
```

</details>

#### constructs Release event

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = KeyEvent.Release(key: Key.A)
expect(event).to_equal(KeyEvent.Release(key: Key.A))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
