# Blink BlockFlow Layout Specification

> Tests for the BFC (Block Formatting Context) vertical stacking layout engine. Covers BoxGeometry construction, single-box layout, vertical child stacking, nested padding offsets, empty-context safety, and total_height_for.

<!-- sdn-diagram:id=block_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=block_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

block_flow_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=block_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink BlockFlow Layout Specification

Tests for the BFC (Block Formatting Context) vertical stacking layout engine. Covers BoxGeometry construction, single-box layout, vertical child stacking, nested padding offsets, empty-context safety, and total_height_for.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Layout |
| Status | Active |
| Source | `test/01_unit/lib/blink/block_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the BFC (Block Formatting Context) vertical stacking layout engine.
Covers BoxGeometry construction, single-box layout, vertical child stacking,
nested padding offsets, empty-context safety, and total_height_for.

## Scenarios

### box_geometry_zero

#### all fields zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geo = box_geometry_zero()
expect(geo.width == 0.0).to_equal(true)
expect(geo.height == 0.0).to_equal(true)
expect(geo.margin_top == 0.0).to_equal(true)
expect(geo.margin_right == 0.0).to_equal(true)
expect(geo.margin_bottom == 0.0).to_equal(true)
expect(geo.margin_left == 0.0).to_equal(true)
expect(geo.padding_top == 0.0).to_equal(true)
expect(geo.padding_right == 0.0).to_equal(true)
expect(geo.padding_bottom == 0.0).to_equal(true)
expect(geo.padding_left == 0.0).to_equal(true)
expect(geo.border_top == 0.0).to_equal(true)
expect(geo.border_right == 0.0).to_equal(true)
expect(geo.border_bottom == 0.0).to_equal(true)
expect(geo.border_left == 0.0).to_equal(true)
```

</details>

### box_geometry_new

#### box_geometry_new(100, 50, 10, 20, 3): correct margin/padding/border splits

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geo = box_geometry_new(100.0, 50.0, 10.0, 20.0, 3.0)
expect(approx_eq(geo.width, 100.0)).to_equal(true)
expect(approx_eq(geo.height, 50.0)).to_equal(true)
expect(approx_eq(geo.margin_top, 10.0)).to_equal(true)
expect(approx_eq(geo.margin_right, 10.0)).to_equal(true)
expect(approx_eq(geo.margin_bottom, 10.0)).to_equal(true)
expect(approx_eq(geo.margin_left, 10.0)).to_equal(true)
expect(approx_eq(geo.padding_top, 20.0)).to_equal(true)
expect(approx_eq(geo.padding_right, 20.0)).to_equal(true)
expect(approx_eq(geo.padding_bottom, 20.0)).to_equal(true)
expect(approx_eq(geo.padding_left, 20.0)).to_equal(true)
expect(approx_eq(geo.border_top, 3.0)).to_equal(true)
expect(approx_eq(geo.border_right, 3.0)).to_equal(true)
expect(approx_eq(geo.border_bottom, 3.0)).to_equal(true)
expect(approx_eq(geo.border_left, 3.0)).to_equal(true)
```

</details>

### compute_layout single root

#### single root box has computed_rect with box width/height

1. ctx add box
2. ctx set root
3. ctx compute layout
   - Expected: opt is None is false
   - Expected: approx_eq(b.computed_rect.right - b.computed_rect.left, 200.0) is true
   - Expected: approx_eq(b.computed_rect.bottom - b.computed_rect.top, 100.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geo = box_geometry_new(200.0, 100.0, 0.0, 0.0, 0.0)
val root = layout_box_new(0, geo)
val ctx = layout_context_new(800.0, 600.0)
ctx.add_box(root)
ctx.set_root(0)
ctx.compute_layout()
val opt = ctx.get_box(0)
expect(opt is None).to_equal(false)
val b = opt.unwrap()
expect(approx_eq(b.computed_rect.right - b.computed_rect.left, 200.0)).to_equal(true)
expect(approx_eq(b.computed_rect.bottom - b.computed_rect.top, 100.0)).to_equal(true)
```

</details>

### compute_layout two children

#### two child boxes stack vertically — second top = first bottom + margins

1. parent children ids push
2. parent children ids push
3. ctx add box
4. ctx add box
5. ctx add box
6. ctx set root
7. ctx compute layout
   - Expected: opt1 is None is false
   - Expected: opt2 is None is false
   - Expected: approx_eq(b1.computed_rect.top, 5.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_geo = box_geometry_new(300.0, 0.0, 0.0, 0.0, 0.0)
val parent = layout_box_new(1, parent_geo)
parent.children_ids.push(2)
parent.children_ids.push(3)

val child1_geo = box_geometry_new(300.0, 40.0, 5.0, 0.0, 0.0)
val child1 = layout_box_new(2, child1_geo)

val child2_geo = box_geometry_new(300.0, 60.0, 8.0, 0.0, 0.0)
val child2 = layout_box_new(3, child2_geo)

val ctx = layout_context_new(800.0, 600.0)
ctx.add_box(parent)
ctx.add_box(child1)
ctx.add_box(child2)
ctx.set_root(1)
ctx.compute_layout()

val opt1 = ctx.get_box(2)
val opt2 = ctx.get_box(3)
expect(opt1 is None).to_equal(false)
expect(opt2 is None).to_equal(false)

val b1 = opt1.unwrap()
val b2 = opt2.unwrap()

# child1 top = parent_top + border + padding + child1.margin_top = 0 + 0 + 0 + 5 = 5
expect(approx_eq(b1.computed_rect.top, 5.0)).to_equal(true)

# child2 top = child1.margin_top + child1.height + child1.margin_bottom + child2.margin_top
#            = 5 + 40 + 5 + 8 = 58
expect(b2.computed_rect.top).to_be_greater_than(b1.computed_rect.bottom)
```

</details>

### compute_layout nested padding

#### nested box padding shifts child position

1. parent children ids push
2. ctx add box
3. ctx add box
4. ctx set root
5. ctx compute layout
   - Expected: opt_child is None is false
   - Expected: approx_eq(bc.computed_rect.left, 12.0) is true
   - Expected: approx_eq(bc.computed_rect.top, 17.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_geo = BoxGeometry(
    width: 300.0,
    height: 200.0,
    margin_top: 0.0,
    margin_right: 0.0,
    margin_bottom: 0.0,
    margin_left: 0.0,
    padding_top: 15.0,
    padding_right: 10.0,
    padding_bottom: 15.0,
    padding_left: 10.0,
    border_top: 2.0,
    border_right: 2.0,
    border_bottom: 2.0,
    border_left: 2.0
)
val parent = layout_box_new(10, parent_geo)
parent.children_ids.push(11)

val child_geo = box_geometry_new(100.0, 50.0, 0.0, 0.0, 0.0)
val child = layout_box_new(11, child_geo)

val ctx = layout_context_new(800.0, 600.0)
ctx.add_box(parent)
ctx.add_box(child)
ctx.set_root(10)
ctx.compute_layout()

val opt_child = ctx.get_box(11)
expect(opt_child is None).to_equal(false)
val bc = opt_child.unwrap()

# child left = parent.margin_left + parent.border_left + parent.padding_left + child.margin_left
#            = 0 + 2 + 10 + 0 = 12
expect(approx_eq(bc.computed_rect.left, 12.0)).to_equal(true)

# child top = parent.margin_top + parent.border_top + parent.padding_top + child.margin_top
#           = 0 + 2 + 15 + 0 = 17
expect(approx_eq(bc.computed_rect.top, 17.0)).to_equal(true)
```

</details>

### compute_layout empty context

#### empty context does not crash

1. ctx compute layout
   - Expected: opt is None is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = layout_context_new(800.0, 600.0)
ctx.compute_layout()
val opt = ctx.get_box(0)
expect(opt is None).to_equal(true)
```

</details>

### total_height_for

#### returns correct height of laid-out box

1. ctx add box
2. ctx set root
3. ctx compute layout
   - Expected: approx_eq(h, 120.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geo = box_geometry_new(400.0, 120.0, 10.0, 5.0, 1.0)
val root = layout_box_new(20, geo)
val ctx = layout_context_new(800.0, 600.0)
ctx.add_box(root)
ctx.set_root(20)
ctx.compute_layout()
val h = ctx.total_height_for(20)
# height is the border-box height = geo.height = 120
expect(approx_eq(h, 120.0)).to_equal(true)
expect(h).to_be_greater_than(0.0)
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
