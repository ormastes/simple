# Fill Rect Edges Specification

> 1. backend fill rect

<!-- sdn-diagram:id=fill_rect_edges_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fill_rect_edges_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fill_rect_edges_spec -> std
fill_rect_edges_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fill_rect_edges_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fill Rect Edges Specification

## Scenarios

### BrowserCompositorBackend fill_rect edges

#### painted region is half-open [x,x+w) x [y,y+h)

#### paints interior pixel (4, 4) when rect is (2,2,3,3)

1. backend fill rect
   - Expected: cap_read_pixel(backend, 4, 4) equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(2, 2, 3, 3, RED)
expect(cap_read_pixel(backend, 4, 4)).to_equal(RED)
```

</details>

#### paints top-left corner (2, 2) when rect is (2,2,3,3)

1. backend fill rect
   - Expected: cap_read_pixel(backend, 2, 2) equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(2, 2, 3, 3, RED)
expect(cap_read_pixel(backend, 2, 2)).to_equal(RED)
```

</details>

#### leaves right/bottom edge (5, 5) untouched (EXCLUSIVE)

1. backend fill rect
   - Expected: cap_read_pixel(backend, 5, 5) equals `CLEAR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(2, 2, 3, 3, RED)
expect(cap_read_pixel(backend, 5, 5)).to_equal(CLEAR)
```

</details>

#### leaves outside-top-left (1, 1) untouched

1. backend fill rect
   - Expected: cap_read_pixel(backend, 1, 1) equals `CLEAR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(2, 2, 3, 3, RED)
expect(cap_read_pixel(backend, 1, 1)).to_equal(CLEAR)
```

</details>

#### degenerate and full-canvas cases

#### no-ops on zero width/height

1. backend fill rect
   - Expected: _all_pixels_are(backend, CLEAR) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(0, 0, 0, 0, BLUE)
expect(_all_pixels_are(backend, CLEAR)).to_equal(true)
```

</details>

#### fills every pixel when rect matches canvas

1. backend fill rect
   - Expected: _all_pixels_are(backend, GREEN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(0, 0, W, H, GREEN)
expect(_all_pixels_are(backend, GREEN)).to_equal(true)
```

</details>

#### edge-overlap write order

#### later write wins at overlap (0,0) -> CYAN

1. backend fill rect
2. backend fill rect
   - Expected: cap_read_pixel(backend, 0, 0) equals `CYAN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(0, 0, W, 1, YELLOW)
backend.fill_rect(0, 0, 1, H, CYAN)
expect(cap_read_pixel(backend, 0, 0)).to_equal(CYAN)
```

</details>

#### non-overlap strip pixel (1, 0) stays YELLOW

1. backend fill rect
2. backend fill rect
   - Expected: cap_read_pixel(backend, 1, 0) equals `YELLOW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(0, 0, W, 1, YELLOW)
backend.fill_rect(0, 0, 1, H, CYAN)
expect(cap_read_pixel(backend, 1, 0)).to_equal(YELLOW)
```

</details>

#### non-overlap column pixel (0, 1) stays CYAN

1. backend fill rect
2. backend fill rect
   - Expected: cap_read_pixel(backend, 0, 1) equals `CYAN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _fresh()
backend.fill_rect(0, 0, W, 1, YELLOW)
backend.fill_rect(0, 0, 1, H, CYAN)
expect(cap_read_pixel(backend, 0, 1)).to_equal(CYAN)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/ui/fill_rect_edges_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserCompositorBackend fill_rect edges

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
