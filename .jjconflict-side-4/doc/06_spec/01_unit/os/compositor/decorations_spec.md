# Decorations Specification

> <details>

<!-- sdn-diagram:id=decorations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=decorations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

decorations_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=decorations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Decorations Specification

## Scenarios

### Decoration constants

#### TITLE_BAR_HEIGHT is 24

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TITLE_BAR_HEIGHT).to_equal(24)
```

</details>

#### BORDER_WIDTH is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BORDER_WIDTH).to_equal(1)
```

</details>

#### CLOSE_BUTTON_SIZE is 18

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CLOSE_BUTTON_SIZE).to_equal(18)
```

</details>

#### CLOSE_BUTTON_MARGIN is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CLOSE_BUTTON_MARGIN).to_equal(3)
```

</details>

#### TITLE_TEXT_X_OFFSET is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TITLE_TEXT_X_OFFSET).to_equal(8)
```

</details>

#### TITLE_TEXT_Y_OFFSET is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TITLE_TEXT_Y_OFFSET).to_equal(4)
```

</details>

### Decoration dimensions

#### total_decoration_top is TITLE_BAR_HEIGHT + BORDER_WIDTH

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val top = total_decoration_top()
expect(top).to_equal(25)
```

</details>

#### total_decoration_left is BORDER_WIDTH

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = total_decoration_left()
expect(left).to_equal(1)
```

</details>

#### total_decoration_right is BORDER_WIDTH

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val right = total_decoration_right()
expect(right).to_equal(1)
```

</details>

#### total_decoration_bottom is BORDER_WIDTH

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bottom = total_decoration_bottom()
expect(bottom).to_equal(1)
```

</details>

### Client area calculation

#### client_area_x adds left decoration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = client_area_x(100)
expect(x).to_equal(101)
```

</details>

#### client_area_y adds top decoration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = client_area_y(50)
# 50 + TITLE_BAR_HEIGHT(24) + BORDER_WIDTH(1) = 75
expect(y).to_equal(75)
```

</details>

#### client_area_width subtracts left and right borders

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = client_area_width(640)
# 640 - BORDER_WIDTH(1) - BORDER_WIDTH(1) = 638
expect(w).to_equal(638)
```

</details>

#### client_area_height subtracts top and bottom decorations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = client_area_height(480)
# 480 - total_decoration_top(25) - total_decoration_bottom(1) = 454
expect(h).to_equal(454)
```

</details>

#### client_area_width returns 0 for too-narrow window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = client_area_width(1)
expect(w).to_equal(0)
```

</details>

#### client_area_height returns 0 for too-short window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = client_area_height(10)
expect(h).to_equal(0)
```

</details>

#### client_area_x with zero position

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = client_area_x(0)
expect(x).to_equal(1)
```

</details>

#### client_area_y with zero position

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = client_area_y(0)
expect(y).to_equal(25)
```

</details>

### is_in_title_bar

#### returns true for click inside title bar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Window at (100, 50), width 640
# Title bar: x range [101, 739), y range [51, 75)
val result = is_in_title_bar(100, 50, 640, 110, 60)
expect(result).to_equal(true)
```

</details>

#### returns true for click at top-left of title bar

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bar_x = 100 + 1 = 101, bar_y = 50 + 1 = 51
val result = is_in_title_bar(100, 50, 640, 101, 51)
expect(result).to_equal(true)
```

</details>

#### returns false for click below title bar

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Title bar bottom = 50 + 1 + 24 = 75
val result = is_in_title_bar(100, 50, 640, 110, 80)
expect(result).to_equal(false)
```

</details>

#### returns false for click above window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_in_title_bar(100, 50, 640, 110, 40)
expect(result).to_equal(false)
```

</details>

#### returns false for click left of window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_in_title_bar(100, 50, 640, 90, 60)
expect(result).to_equal(false)
```

</details>

#### returns false for click right of window

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bar right edge = 100 + 1 + (640 - 2) = 739
val result = is_in_title_bar(100, 50, 640, 750, 60)
expect(result).to_equal(false)
```

</details>

### is_in_close_button

#### returns true for click on close button

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Window at (100, 50), width 640
# bar_x = 101, bar_w = 638
# btn_x = 101 + 638 - 18 - 3 = 718
# btn_y = 51 + 3 = 54
# Button area: [718, 736) x [54, 72)
val result = is_in_close_button(100, 50, 640, 720, 60)
expect(result).to_equal(true)
```

</details>

#### returns false for click far from close button

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_in_close_button(100, 50, 640, 200, 60)
expect(result).to_equal(false)
```

</details>

#### returns false for click below close button

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Close button y range [54, 72)
val result = is_in_close_button(100, 50, 640, 720, 80)
expect(result).to_equal(false)
```

</details>

#### returns false for click outside window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_in_close_button(100, 50, 640, 50, 60)
expect(result).to_equal(false)
```

</details>

### Decoration color palette

#### title_bar_color_focused returns dark gray

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = title_bar_color_focused()
expect(color).to_equal(Color.rgb(50, 50, 50))
```

</details>

#### title_bar_color_unfocused returns medium gray

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = title_bar_color_unfocused()
expect(color).to_equal(Color.rgb(100, 100, 100))
```

</details>

#### close_button_bg returns red

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = close_button_bg()
expect(color).to_equal(Color.rgb(200, 50, 50))
```

</details>

#### close_button_x_color returns white

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = close_button_x_color()
expect(color).to_equal(Color.white())
```

</details>

#### border_color_focused returns blue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = border_color_focused()
expect(color).to_equal(Color.rgb(100, 149, 237))
```

</details>

#### border_color_unfocused returns dark gray

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = border_color_unfocused()
expect(color).to_equal(Color.rgb(80, 80, 80))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/decorations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Decoration constants
- Decoration dimensions
- Client area calculation
- is_in_title_bar
- is_in_close_button
- Decoration color palette

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
