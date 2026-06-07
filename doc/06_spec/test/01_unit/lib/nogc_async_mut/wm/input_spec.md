# Input Specification

> <details>

<!-- sdn-diagram:id=input_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=input_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

input_spec -> std
input_spec -> nogc_async_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=input_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Input Specification

## Scenarios

### WM Input Protocol

#### starts with an empty queue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = wm_input_queue_new()
expect(wm_input_queue_len(q)).to_equal(0)
```

</details>

#### pushes a key press event and increments queue length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = wm_input_queue_new()
val key = WmKeyEvent(window_id: 1, key_code: 65, scan_code: 30, modifiers: 0, pressed: true)
val q2 = wm_input_push_key(q, key)
expect(wm_input_queue_len(q2)).to_equal(1)
```

</details>

#### pushes a mouse event and increments queue length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = wm_input_queue_new()
val mouse = WmMouseEvent(window_id: 1, x: 100, y: 200, button: 1, pressed: true)
val q2 = wm_input_push_mouse(q, mouse)
expect(wm_input_queue_len(q2)).to_equal(1)
```

</details>

#### polls events in FIFO order

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = wm_input_queue_new()
val k1 = WmKeyEvent(window_id: 1, key_code: 65, scan_code: 30, modifiers: 0, pressed: true)
val k2 = WmKeyEvent(window_id: 1, key_code: 66, scan_code: 48, modifiers: 0, pressed: false)
val q1 = wm_input_push_key(q, k1)
val q2 = wm_input_push_key(q1, k2)
val p1 = wm_input_poll(q2)
expect(p1.ok).to_equal(true)
expect(p1.entry.key_code).to_equal(65)
val p2 = wm_input_poll(p1.queue)
expect(p2.entry.key_code).to_equal(66)
val p3 = wm_input_poll(p2.queue)
expect(p3.ok).to_equal(false)
expect(p3.state).to_equal("queue-empty")
```

</details>

#### records key press and release distinction

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = wm_input_queue_new()
val press = WmKeyEvent(window_id: 2, key_code: 13, scan_code: 28, modifiers: 0, pressed: true)
val release = WmKeyEvent(window_id: 2, key_code: 13, scan_code: 28, modifiers: 0, pressed: false)
val q1 = wm_input_push_key(q, press)
val q2 = wm_input_push_key(q1, release)
val p1 = wm_input_poll(q2)
expect(p1.entry.pressed).to_equal(true)
val p2 = wm_input_poll(p1.queue)
expect(p2.entry.pressed).to_equal(false)
```

</details>

#### records mouse button and position

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = wm_input_queue_new()
val mouse = WmMouseEvent(window_id: 3, x: 50, y: 75, button: 3, pressed: true)
val q2 = wm_input_push_mouse(q, mouse)
val p = wm_input_poll(q2)
expect(p.ok).to_equal(true)
expect(p.entry.mouse_x).to_equal(50)
expect(p.entry.mouse_y).to_equal(75)
expect(p.entry.button).to_equal(3)
```

</details>

#### records scroll event with delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = wm_input_queue_new()
val scroll = WmScrollEvent(window_id: 1, delta_x: 0, delta_y: 3)
val q2 = wm_input_push_scroll(q, scroll)
val p = wm_input_poll(q2)
expect(p.ok).to_equal(true)
expect(p.entry.delta_y).to_equal(3)
```

</details>

#### handles mixed key and mouse events in FIFO order

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = wm_input_queue_new()
val key = WmKeyEvent(window_id: 1, key_code: 32, scan_code: 57, modifiers: 0, pressed: true)
val mouse = WmMouseEvent(window_id: 1, x: 10, y: 20, button: 1, pressed: false)
val q1 = wm_input_push_key(q, key)
val q2 = wm_input_push_mouse(q1, mouse)
val p1 = wm_input_poll(q2)
expect(p1.entry.kind).to_equal("key")
val p2 = wm_input_poll(p1.queue)
expect(p2.entry.kind).to_equal("mouse")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/wm/input_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WM Input Protocol

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
