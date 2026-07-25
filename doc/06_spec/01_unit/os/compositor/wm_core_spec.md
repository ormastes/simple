# WM Core Spec

> Unit tests for `wm_core.spl` — pure WM hit-testing and resize logic: `detect_resize_edge`, `raise_to_top`, and `apply_resize`.

<!-- sdn-diagram:id=wm_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_core_spec -> std
wm_core_spec -> os
wm_core_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM Core Spec

Unit tests for `wm_core.spl` — pure WM hit-testing and resize logic: `detect_resize_edge`, `raise_to_top`, and `apply_resize`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/compositor/wm_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for `wm_core.spl` — pure WM hit-testing and resize logic:
`detect_resize_edge`, `raise_to_top`, and `apply_resize`.

## Scenarios

### detect_resize_edge

#### returns EDGE_NONE for interior point

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = Rect.xywh(10, 20, 100, 50)
val pt     = Point.xy(60, 45)
val result = detect_resize_edge(bounds, pt, Px(value: 5))
expect(result).to_equal(EDGE_NONE)
```

</details>

#### returns EDGE_LEFT for point on left edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = Rect.xywh(10, 20, 100, 50)
val pt     = Point.xy(10, 45)
val result = detect_resize_edge(bounds, pt, Px(value: 5))
expect(result).to_equal(EDGE_LEFT)
```

</details>

#### returns EDGE_RIGHT for point on right edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = Rect.xywh(10, 20, 100, 50)
val pt     = Point.xy(110, 45)
val result = detect_resize_edge(bounds, pt, Px(value: 5))
expect(result).to_equal(EDGE_RIGHT)
```

</details>

#### returns EDGE_TOP for point on top edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = Rect.xywh(10, 20, 100, 50)
val pt     = Point.xy(60, 20)
val result = detect_resize_edge(bounds, pt, Px(value: 5))
expect(result).to_equal(EDGE_TOP)
```

</details>

#### returns EDGE_BOTTOM for point on bottom edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = Rect.xywh(10, 20, 100, 50)
val pt     = Point.xy(60, 70)
val result = detect_resize_edge(bounds, pt, Px(value: 5))
expect(result).to_equal(EDGE_BOTTOM)
```

</details>

#### returns EDGE_LEFT|EDGE_TOP for top-left corner

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds  = Rect.xywh(10, 20, 100, 50)
val pt      = Point.xy(10, 20)
val result  = detect_resize_edge(bounds, pt, Px(value: 5))
val expected = EDGE_LEFT | EDGE_TOP
expect(result).to_equal(expected)
```

</details>

#### returns EDGE_NONE for point far outside surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = Rect.xywh(10, 20, 100, 50)
val pt     = Point.xy(200, 200)
val result = detect_resize_edge(bounds, pt, Px(value: 5))
expect(result).to_equal(EDGE_NONE)
```

</details>

### raise_to_top

#### moves element at idx=1 to end of list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = raise_to_top([1, 2, 3, 4], 1)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(3)
expect(result[2]).to_equal(4)
expect(result[3]).to_equal(2)
```

</details>

#### returns unchanged list for negative idx

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = raise_to_top([1, 2, 3], -1)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(3)
```

</details>

#### returns unchanged list for out-of-range idx

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = raise_to_top([1, 2, 3], 5)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(3)
```

</details>

#### returns unchanged list when element is already last

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = raise_to_top([1, 2, 3], 2)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(3)
```

</details>

### apply_resize

#### EDGE_RIGHT grows width with positive delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds   = Rect.xywh(10, 20, 100, 50)
val min_size = Size.wh(20, 10)
val delta    = Point.xy(10, 0)
val result   = apply_resize(bounds, EDGE_RIGHT, delta, min_size)
expect(result.origin.x.to_i32()).to_equal(10)
expect(result.origin.y.to_i32()).to_equal(20)
expect(result.size.width.to_i32()).to_equal(110)
expect(result.size.height.to_i32()).to_equal(50)
```

</details>

#### EDGE_LEFT shrinks width and shifts origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds   = Rect.xywh(10, 20, 100, 50)
val min_size = Size.wh(20, 10)
val delta    = Point.xy(10, 0)
val result   = apply_resize(bounds, EDGE_LEFT, delta, min_size)
expect(result.origin.x.to_i32()).to_equal(20)
expect(result.size.width.to_i32()).to_equal(90)
```

</details>

#### EDGE_RIGHT clamps width to min_w when delta is very negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds   = Rect.xywh(10, 20, 100, 50)
val min_size = Size.wh(20, 10)
val delta    = Point.xy(-1000, 0)
val result   = apply_resize(bounds, EDGE_RIGHT, delta, min_size)
expect(result.size.width.to_i32()).to_equal(20)
```

</details>

#### EDGE_BOTTOM grows height with positive delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds   = Rect.xywh(10, 20, 100, 50)
val min_size = Size.wh(20, 10)
val delta    = Point.xy(0, 10)
val result   = apply_resize(bounds, EDGE_BOTTOM, delta, min_size)
expect(result.size.height.to_i32()).to_equal(60)
```

</details>

#### EDGE_TOP clamps height to min_h when delta is very negative and shifts y

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds   = Rect.xywh(10, 20, 100, 50)
val min_size = Size.wh(20, 10)
val delta    = Point.xy(-1000, -1000)
val result   = apply_resize(bounds, EDGE_TOP, delta, min_size)
expect(result.size.height.to_i32()).to_equal(10)
val expected_y = 20 + 50 - 10
expect(result.origin.y.to_i32()).to_equal(expected_y)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
