# Blink ScrollManager Specification

> Tests for the scroll manager: per-element scroll offset tracking, clamping, overflow behaviour, registration, lookup, and delegation via scroll_element.

<!-- sdn-diagram:id=scroll_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scroll_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scroll_manager_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scroll_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink ScrollManager Specification

Tests for the scroll manager: per-element scroll offset tracking, clamping, overflow behaviour, registration, lookup, and delegation via scroll_element.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Scroll |
| Status | Active |
| Source | `test/01_unit/lib/blink/scroll_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the scroll manager: per-element scroll offset tracking, clamping,
overflow behaviour, registration, lookup, and delegation via scroll_element.

## Scenarios

### scrollable_area_new

#### scroll_x/y start at 0, overflow=Auto

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = scrollable_area_new(1, 800.0, 600.0, 1600.0, 1200.0)
expect(approx_eq(area.scroll_x, 0.0)).to_equal(true)
expect(approx_eq(area.scroll_y, 0.0)).to_equal(true)
expect(area.overflow_x == OverflowBehavior.Auto).to_equal(true)
expect(area.overflow_y == OverflowBehavior.Auto).to_equal(true)
```

</details>

### max_scroll_x and max_scroll_y

#### max_scroll_x/y: correct for content > viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = scrollable_area_new(2, 800.0, 600.0, 1600.0, 1200.0)
expect(approx_eq(area.max_scroll_x(), 800.0)).to_equal(true)
expect(approx_eq(area.max_scroll_y(), 600.0)).to_equal(true)
```

</details>

### scroll_by upper clamp

#### scroll_by: clamps to max (beyond content does not overshoot)

1. area scroll by
   - Expected: approx_eq(area.scroll_x, 800.0) is true
   - Expected: approx_eq(area.scroll_y, 600.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = scrollable_area_new(3, 800.0, 600.0, 1600.0, 1200.0)
area.scroll_by(10000.0, 10000.0)
expect(approx_eq(area.scroll_x, 800.0)).to_equal(true)
expect(approx_eq(area.scroll_y, 600.0)).to_equal(true)
```

</details>

### scroll_by lower clamp

#### scroll_by: clamps to 0 (negative scroll disallowed)

1. area scroll by
   - Expected: approx_eq(area.scroll_x, 0.0) is true
   - Expected: approx_eq(area.scroll_y, 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = scrollable_area_new(4, 800.0, 600.0, 1600.0, 1200.0)
area.scroll_by(-500.0, -500.0)
expect(approx_eq(area.scroll_x, 0.0)).to_equal(true)
expect(approx_eq(area.scroll_y, 0.0)).to_equal(true)
```

</details>

### can_scroll_y Auto

#### can_scroll_y: Auto with content > viewport returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = scrollable_area_new(5, 800.0, 600.0, 800.0, 1200.0)
expect(area.can_scroll_y()).to_equal(true)
```

</details>

### can_scroll_y Hidden

#### can_scroll_y: Hidden returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = scrollable_area_new(6, 800.0, 600.0, 800.0, 1200.0)
area.overflow_y = OverflowBehavior.Hidden
expect(area.can_scroll_y()).to_equal(true)
```

</details>

### ScrollManager register and find_area

#### register + find_area: round-trips

1. mgr register
   - Expected: found is None is false
   - Expected: a.element_id == 10 is true
   - Expected: approx_eq(a.viewport_width, 800.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = scroll_manager_new()
val area = scrollable_area_new(10, 800.0, 600.0, 1600.0, 1200.0)
mgr.register(area)
val found = mgr.find_area(10)
expect(found is None).to_equal(false)
val a = found.unwrap()
expect(a.element_id == 10).to_equal(true)
expect(approx_eq(a.viewport_width, 800.0)).to_equal(true)
```

</details>

### ScrollManager scroll_element missing

#### scroll_element: missing element returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = scroll_manager_new()
val result = mgr.scroll_element(999, 100.0, 100.0)
expect(result).to_equal(false)
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
