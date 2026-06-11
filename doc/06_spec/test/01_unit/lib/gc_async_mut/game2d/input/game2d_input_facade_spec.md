# Game2d Input Facade Specification

> 1. set current

<!-- sdn-diagram:id=game2d_input_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_input_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_input_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_input_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Input Facade Specification

## Scenarios

### gc_async_mut game2d input facade

#### re-exports key constructors, snapshots, and current input accessors

1. set current
   - Expected: current().key_down(jump) is true
   - Expected: key_down(jump) is true
   - Expected: key_pressed_this_frame(jump) is true
   - Expected: mouse_down(left) is true
   - Expected: mouse_pos().y equals `24.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jump = Key(32)
val left = mouse_left()
val right = mouse_right()
expect(jump.code).to_equal(32)
expect(left.code).to_equal(1)
expect(right.code).to_equal(3)

val empty = InputSnapshot.create()
expect(empty.key_down(jump)).to_equal(false)

val snap = freeze_from([jump], [jump], Vec2(x: 12.0, y: 24.0), [left])
expect(snap.key_down(jump)).to_equal(true)
expect(snap.key_pressed_this_frame(jump)).to_equal(true)
expect(snap.mouse_down(left)).to_equal(true)
expect(snap.mouse_position().x).to_equal(12.0)

set_current(snap)
expect(current().key_down(jump)).to_equal(true)
expect(key_down(jump)).to_equal(true)
expect(key_pressed_this_frame(jump)).to_equal(true)
expect(mouse_down(left)).to_equal(true)
expect(mouse_pos().y).to_equal(24.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/input/game2d_input_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut game2d input facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
