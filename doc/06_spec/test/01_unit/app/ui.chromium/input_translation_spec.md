# Input Translation Specification

> <details>

<!-- sdn-diagram:id=input_translation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=input_translation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

input_translation_spec -> app
input_translation_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=input_translation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Input Translation Specification

## Scenarios

### Chromium Event Bridge — stateless translation

#### maps escape to NormalMode

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = translate_key_event(27, 0)
match ev:
    UIEvent.NormalMode =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### maps Ctrl+Q to Quit via modifier bitmask

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = translate_key_event(113, 2)
match ev:
    UIEvent.Quit =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### maps Shift+Tab to FocusPrev

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = translate_key_event(9, 1)
match ev:
    UIEvent.FocusPrev =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### maps mouse press(button=0) to TouchPress

1. UIEvent TouchPress


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = translate_mouse_event(120, 240, 0, "press")
match ev:
    UIEvent.TouchPress(x, y) =>
        expect(x == 120).to_be_true()
        expect(y == 240).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### maps positive wheel delta to FocusNext

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = translate_wheel_ui_event(3)
match ev:
    UIEvent.FocusNext =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### produces a DOM wheel event with type 'wheel'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dom = translate_wheel_dom_event(42, 1000)
expect(dom.type_name == "wheel").to_be_true()
expect(dom.target_id == 42).to_be_true()
```

</details>

### Chromium Event Bridge — modifier round-trip

#### round-trips a Shift press through the modifier mask

1. var bridge = ChromiumEventBridge new
2. bridge update modifier
3. bridge update modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bridge = ChromiumEventBridge.new()
bridge.update_modifier(16, true)
expect(bridge.shift_down).to_be_true()
expect(bridge.modifiers_mask() == 1).to_be_true()
bridge.update_modifier(16, false)
expect(not bridge.shift_down).to_be_true()
expect(bridge.modifiers_mask() == 0).to_be_true()
```

</details>

#### tracks Ctrl then produces Ctrl+C Quit on release edge

1. var bridge = ChromiumEventBridge new
2. bridge update modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bridge = ChromiumEventBridge.new()
bridge.update_modifier(17, true)
expect(bridge.ctrl_down).to_be_true()
val result = bridge.on_key(99, true)
match result:
    UIEvent.Quit =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/input_translation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chromium Event Bridge — stateless translation
- Chromium Event Bridge — modifier round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
