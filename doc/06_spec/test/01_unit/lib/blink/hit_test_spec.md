# Blink HitTest Specification

> Tests for hit_test — the function that maps a 2D input point to the topmost (innermost) LayoutBox containing it.  Mirrors Blink's EventHandler::HitTestResultAtLocation.

<!-- sdn-diagram:id=hit_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hit_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hit_test_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hit_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink HitTest Specification

Tests for hit_test — the function that maps a 2D input point to the topmost (innermost) LayoutBox containing it.  Mirrors Blink's EventHandler::HitTestResultAtLocation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Input |
| Status | Active |
| Source | `test/01_unit/lib/blink/hit_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for hit_test — the function that maps a 2D input point to the
topmost (innermost) LayoutBox containing it.  Mirrors Blink's
EventHandler::HitTestResultAtLocation.

## Scenarios

### hit_test_empty

#### hit_box_id is -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = hit_test_empty()
expect(r.hit_box_id).to_equal(-1)
```

</details>

### point_in_rect

#### point inside rect returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val inside = point_in_rect(rect, 50.0, 50.0)
expect(inside).to_equal(true)
```

</details>

#### point outside rect returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val outside = point_in_rect(rect, 150.0, 50.0)
expect(outside).to_equal(false)
```

</details>

### hit_test

#### point inside root box returns root's id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_ctx_single_box()
val result = hit_test(ctx, 100.0, 50.0)
expect(result.hit_box_id).to_equal(1)
```

</details>

#### point inside nested child returns child's id (innermost wins)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_ctx_parent_child()
# (50, 50) is inside both parent (0-200) and child (10-90)
val result = hit_test(ctx, 50.0, 50.0)
expect(result.hit_box_id).to_equal(2)
```

</details>

#### point outside everything returns hit_test_empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_ctx_single_box()
# (500, 500) is outside the 200x100 root box
val result = hit_test(ctx, 500.0, 500.0)
expect(result.hit_box_id).to_equal(-1)
```

</details>

### hit_test_event

#### mouse event at (50, 50) inside a box hits that box

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_ctx_single_box()
val ev = mouse_event(EventType.MouseDown, 50.0, 50.0, 0.0, 0)
val result = hit_test_event(ctx, ev)
expect(result.hit_box_id).to_equal(1)
val lx_ok = result.local_x >= 0.0
expect(lx_ok).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
