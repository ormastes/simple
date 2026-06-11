# Blink InputEvent Specification

> Tests for the Blink-style InputEvent — the unified envelope that mirrors blink::WebInputEvent. Covers free constructors for mouse/key/char/touch/wheel events, modifier bitmask queries, event-type classification, and the handled-flag latch used by the dispatcher to stop propagation.

<!-- sdn-diagram:id=input_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=input_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

input_event_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=input_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink InputEvent Specification

Tests for the Blink-style InputEvent — the unified envelope that mirrors blink::WebInputEvent. Covers free constructors for mouse/key/char/touch/wheel events, modifier bitmask queries, event-type classification, and the handled-flag latch used by the dispatcher to stop propagation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/01_unit/lib/blink/input_event_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Blink-style InputEvent — the unified envelope that mirrors
blink::WebInputEvent. Covers free constructors for mouse/key/char/touch/wheel
events, modifier bitmask queries, event-type classification, and the
handled-flag latch used by the dispatcher to stop propagation.

## Scenarios

### mouse_event

#### creates MouseDown with correct position

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = mouse_event(EventType.MouseDown, 120.5, 64.0, 1000.0, 0)
val is_mouse_down = ev.event_type == EventType.MouseDown
expect(is_mouse_down).to_equal(true)
expect(ev.position.x).to_equal(120.5)
expect(ev.position.y).to_equal(64.0)
expect(ev.timestamp).to_be_greater_than(0.0)
```

</details>

### key_event

#### creates KeyDown with key_code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = key_event(EventType.KeyDown, 65, 2000.0, 0)
val is_key_down = ev.event_type == EventType.KeyDown
expect(is_key_down).to_equal(true)
expect(ev.key_code).to_equal(65)
```

</details>

### char_event

#### creates Char with char_code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = char_event(97, 3000.0, 0)
val is_char = ev.event_type == EventType.Char
expect(is_char).to_equal(true)
expect(ev.char_code).to_equal(97)
```

</details>

### touch_event

#### stores touch list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = touch_point(1, 10.0, 20.0)
val t1 = touch_point(2, 30.0, 40.0)
val ev = touch_event(EventType.TouchStart, [t0, t1], 4000.0)
val is_touch_start = ev.event_type == EventType.TouchStart
expect(is_touch_start).to_equal(true)
expect(ev.touches.len()).to_equal(2)
```

</details>

### wheel_event

#### stores wheel deltas

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = wheel_event(50.0, 60.0, -120.0, 240.0, 5000.0, 0)
val is_wheel = ev.event_type == EventType.MouseWheel
expect(is_wheel).to_equal(true)
expect(ev.wheel_delta_y).to_equal(240.0)
expect(ev.wheel_delta_y).to_be_greater_than(0.0)
```

</details>

### has_modifier

#### detects Shift set via bitmask

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = key_event(EventType.KeyDown, 65, 6000.0, 1)
expect(ev.has_modifier(1)).to_equal(true)
expect(ev.has_modifier(2)).to_equal(false)
```

</details>

### is_mouse/is_keyboard/is_touch

#### classify event types correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mouse_event(EventType.MouseMove, 1.0, 2.0, 7000.0, 0)
expect(m.is_mouse()).to_equal(true)
expect(m.is_keyboard()).to_equal(false)
expect(m.is_touch()).to_equal(false)
val k = key_event(EventType.KeyUp, 13, 7100.0, 0)
expect(k.is_keyboard()).to_equal(true)
expect(k.is_mouse()).to_equal(false)
val t = touch_event(EventType.TouchMove, [], 7200.0)
expect(t.is_touch()).to_equal(true)
expect(t.is_mouse()).to_equal(false)
```

</details>

### mark_handled

#### sets handled flag

1. ev mark handled
   - Expected: ev.handled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = mouse_event(EventType.MouseUp, 5.0, 5.0, 8000.0, 0)
expect(ev.handled).to_equal(false)
ev.mark_handled()
expect(ev.handled).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
