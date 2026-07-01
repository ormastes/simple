# Layout Specification

> <details>

<!-- sdn-diagram:id=layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_spec -> std
layout_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Specification

## Scenarios

### compute_layout single widget

#### assigns full rect to a single text widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("t1", "Hello")
val rects = compute_layout(root, 0, 0, 80, 24)
val r = find_rect(rects, "t1")
expect(r != nil).to_equal(true)
if r != nil:
    expect(r.x).to_equal(0)
    expect(r.y).to_equal(0)
    expect(r.w).to_equal(80)
    expect(r.h).to_equal(24)
```

</details>

### compute_layout vbox

#### splits height evenly between two equal children

1. text widget
2. text widget
   - Expected: ra != nil is true
   - Expected: rb != nil is true
   - Expected: ra.h equals `11`
   - Expected: ra.w equals `78`
   - Expected: rb.h equals `11`
   - Expected: rb.y equals `ra.y + 11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("vbox1", [
    text_widget("v_a", "A"),
    text_widget("v_b", "B")
])
val rects = compute_layout(root, 0, 0, 80, 24)
# Panel border: inner area is x+1, y+1, w-2, h-2 => 1,1,78,22
# Two flex children split 22 evenly => 11 each
val ra = find_rect(rects, "v_a")
val rb = find_rect(rects, "v_b")
expect(ra != nil).to_equal(true)
expect(rb != nil).to_equal(true)
if ra != nil:
    expect(ra.h).to_equal(11)
    expect(ra.w).to_equal(78)
if rb != nil:
    expect(rb.h).to_equal(11)
    expect(rb.y).to_equal(ra.y + 11)
```

</details>

#### gives statusbar height 1 and remaining to flex child

1. text widget
2. statusbar
   - Expected: rc != nil is true
   - Expected: rs != nil is true
   - Expected: rc.h equals `21`
   - Expected: rs.h equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("vbox2", [
    text_widget("v_content", "Content"),
    statusbar("v_status", "left", "right")
])
val rects = compute_layout(root, 0, 0, 80, 24)
# Inner area: 1,1,78,22. StatusBar fixed h=1, flex child gets 21
val rc = find_rect(rects, "v_content")
val rs = find_rect(rects, "v_status")
expect(rc != nil).to_equal(true)
expect(rs != nil).to_equal(true)
if rc != nil:
    expect(rc.h).to_equal(21)
if rs != nil:
    expect(rs.h).to_equal(1)
```

</details>

### compute_layout hbox

#### splits width evenly between two equal children

1. text widget
2. text widget
   - Expected: ra != nil is true
   - Expected: rb != nil is true
   - Expected: ra.w equals `39`
   - Expected: ra.h equals `22`
   - Expected: rb.w equals `39`
   - Expected: rb.x equals `ra.x + 39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = row("hbox1", [
    text_widget("h_a", "A"),
    text_widget("h_b", "B")
])
val rects = compute_layout(root, 0, 0, 80, 24)
# Inner area: 1,1,78,22. Two flex=1 children => 39 each
val ra = find_rect(rects, "h_a")
val rb = find_rect(rects, "h_b")
expect(ra != nil).to_equal(true)
expect(rb != nil).to_equal(true)
if ra != nil:
    expect(ra.w).to_equal(39)
    expect(ra.h).to_equal(22)
if rb != nil:
    expect(rb.w).to_equal(39)
    expect(rb.x).to_equal(ra.x + 39)
```

</details>

#### gives fixed-width child exact width and flex child the remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixed_child = with_width(text_widget("h_fixed", "Fixed"), 20)
val flex_child = text_widget("h_flex", "Flex")
val root = row("hbox2", [fixed_child, flex_child])
val rects = compute_layout(root, 0, 0, 80, 24)
# Inner area: 1,1,78,22. fixed=20, flex gets 78-20=58
val rf = find_rect(rects, "h_fixed")
val rx = find_rect(rects, "h_flex")
expect(rf != nil).to_equal(true)
expect(rx != nil).to_equal(true)
if rf != nil:
    expect(rf.w).to_equal(20)
if rx != nil:
    expect(rx.w).to_equal(58)
```

</details>

### compute_layout panel

#### reserves 1-char border for panel children

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = text_widget("p_inner", "Inner")
val root = panel("p_outer", "Title", [child])
val rects = compute_layout(root, 0, 0, 40, 20)
# Outer panel rect: 0,0,40,20 (kind=panel => border)
# Inner area: 1,1,38,18
# Child panel is also kind=panel with its own border
# But text_widget is kind=text (no border) so it gets inner area directly
val ri = find_rect(rects, "p_inner")
expect(ri != nil).to_equal(true)
if ri != nil:
    # panel -> inner 1,1,38,18 -> child gets full inner
    expect(ri.x).to_equal(1)
    expect(ri.y).to_equal(1)
    expect(ri.w).to_equal(38)
    expect(ri.h).to_equal(18)
```

</details>

### compute_layout grid

#### arranges 4 children into a 2x2 grid

1. text widget
2. text widget
3. text widget
4. text widget
   - Expected: ra != nil is true
   - Expected: rb != nil is true
   - Expected: rc != nil is true
   - Expected: rd != nil is true
   - Expected: ra.x equals `1`
   - Expected: ra.y equals `1`
   - Expected: ra.w equals `39`
   - Expected: ra.h equals `11`
   - Expected: rb.x equals `40`
   - Expected: rb.y equals `1`
   - Expected: rc.x equals `1`
   - Expected: rc.y equals `12`
   - Expected: rd.x equals `40`
   - Expected: rd.y equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = builder.grid("grid1", [
    text_widget("g_a", "A"),
    text_widget("g_b", "B"),
    text_widget("g_c", "C"),
    text_widget("g_d", "D")
])
val rects = compute_layout(root, 0, 0, 80, 24)
# Inner area: 1,1,78,22. 4 children => cols=2, rows=2
# cell_w = 78/2 = 39, cell_h = 22/2 = 11
val ra = find_rect(rects, "g_a")
val rb = find_rect(rects, "g_b")
val rc = find_rect(rects, "g_c")
val rd = find_rect(rects, "g_d")
expect(ra != nil).to_equal(true)
expect(rb != nil).to_equal(true)
expect(rc != nil).to_equal(true)
expect(rd != nil).to_equal(true)
if ra != nil:
    expect(ra.x).to_equal(1)
    expect(ra.y).to_equal(1)
    expect(ra.w).to_equal(39)
    expect(ra.h).to_equal(11)
if rb != nil:
    expect(rb.x).to_equal(40)
    expect(rb.y).to_equal(1)
if rc != nil:
    expect(rc.x).to_equal(1)
    expect(rc.y).to_equal(12)
if rd != nil:
    expect(rd.x).to_equal(40)
    expect(rd.y).to_equal(12)
```

</details>

### find_rect

#### locates a rect by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("find_me", "Find me")
val rects = compute_layout(root, 5, 10, 60, 30)
val r = find_rect(rects, "find_me")
expect(r != nil).to_equal(true)
if r != nil:
    expect(r.id).to_equal("find_me")
    expect(r.x).to_equal(5)
    expect(r.y).to_equal(10)
```

</details>

#### returns nil for a missing id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("exists", "Hello")
val rects = compute_layout(root, 0, 0, 80, 24)
val r = find_rect(rects, "does_not_exist")
expect(r).to_be_nil()
```

</details>

### compute_layout visibility

#### does not lay out invisible children

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val visible_child = text_widget("vis_child", "Visible")
val invisible_child = with_visible(text_widget("invis_child", "Hidden"), false)
val root = column("vis_root", [visible_child, invisible_child])
val rects = compute_layout(root, 0, 0, 80, 24)
# The invisible child should not appear in the child layout rects
# (it is excluded by get_visible_children)
# The visible child should get the full inner height
val rv = find_rect(rects, "vis_child")
expect(rv != nil).to_equal(true)
if rv != nil:
    expect(rv.h).to_equal(22)
```

</details>

### compute_layout menubar

#### gives menubar height 1 by default

1. menubar
2. text widget
   - Expected: rm != nil is true
   - Expected: rb != nil is true
   - Expected: rm.h equals `1`
   - Expected: rb.h equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("menu_root", [
    menubar("menu_bar", ["File", "Edit"]),
    text_widget("menu_body", "Body")
])
val rects = compute_layout(root, 0, 0, 80, 24)
# Inner area: 1,1,78,22. MenuBar fixed h=1, flex child gets 21
val rm = find_rect(rects, "menu_bar")
val rb = find_rect(rects, "menu_body")
expect(rm != nil).to_equal(true)
expect(rb != nil).to_equal(true)
if rm != nil:
    expect(rm.h).to_equal(1)
if rb != nil:
    expect(rb.h).to_equal(21)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compute_layout single widget
- compute_layout vbox
- compute_layout hbox
- compute_layout panel
- compute_layout grid
- find_rect
- compute_layout visibility
- compute_layout menubar

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
