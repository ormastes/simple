# float_layout_spec

> Float Layout Test Spec

<!-- sdn-diagram:id=float_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=float_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

float_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=float_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# float_layout_spec

Float Layout Test Spec

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M13-FLOAT-CSS-QUICKWINS |
| Category | Browser Engine / CSS Float Layout |
| Status | Implemented |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/float_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Float Layout Test Spec

Tests the CSS float layout implementation in the canonical browser engine:
- Float placement (left, right)
- Float clearing (clear: left, right, both)
- Float line box intrusion
- Float stacking/ordering
- BFC containment (overflow:hidden, display:flow-root)
- Display mode dispatch (inline-flex, flow-root)
- CSS property parsing (float_code, clear_code)

## Scenarios

### CSS float placement

#### float:left renders colored box at left edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px;height:40px'><div style='float:left;width:20px;height:20px;background:#ff0000'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Red pixels should appear in the left region
expect(_count_region_color(pixels, VW, 0, 0, 20, 20, 0xFFFF0000u32)).to_be_greater_than(0)
```

</details>

#### float:right renders colored box at right edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px;height:40px'><div style='float:right;width:20px;height:20px;background:#00ff00'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Green pixels should appear in the right region
expect(_count_region_color(pixels, VW, 20, 0, 20, 20, 0xFF00FF00u32)).to_be_greater_than(0)
```

</details>

#### two left floats render side by side

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px;height:40px'><div style='float:left;width:10px;height:10px;background:#ff0000'></div><div style='float:left;width:10px;height:10px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Red in left region
expect(_count_region_color(pixels, VW, 0, 0, 10, 10, 0xFFFF0000u32)).to_be_greater_than(0)
# Blue in second position (x=10..20)
expect(_count_region_color(pixels, VW, 10, 0, 10, 10, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

#### float does not push subsequent in-flow content down

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px'><div style='float:left;width:10px;height:30px;background:#ff0000'></div><div style='width:40px;height:10px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Blue should start at y=0 (floats don't advance cursor_y)
# The blue box should appear in the top row area, narrowed by float
expect(_count_region_color(pixels, VW, 10, 0, 30, 10, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

### CSS float clearing

#### clear:left pushes content below left float

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px'><div style='float:left;width:20px;height:20px;background:#ff0000'></div><div style='clear:left;width:40px;height:10px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Blue should appear below the red float (y >= 20)
expect(_count_region_color(pixels, VW, 0, 20, 40, 10, 0xFF0000FFu32)).to_be_greater_than(0)
# Blue should NOT appear in the float region (y < 20)
expect(_count_region_color(pixels, VW, 0, 0, 40, 20, 0xFF0000FFu32)).to_equal(0)
```

</details>

#### clear:right pushes content below right float

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px'><div style='float:right;width:20px;height:20px;background:#ff0000'></div><div style='clear:right;width:40px;height:10px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Blue should appear below the float (y >= 20)
expect(_count_region_color(pixels, VW, 0, 20, 40, 10, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

#### clear:both pushes content below tallest float

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px'><div style='float:left;width:10px;height:10px;background:#ff0000'></div><div style='float:right;width:10px;height:20px;background:#00ff00'></div><div style='clear:both;width:40px;height:10px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Blue should be below the taller float (y >= 20)
expect(_count_region_color(pixels, VW, 0, 20, 40, 10, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

#### clear:left does not clear right floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px'><div style='float:right;width:20px;height:20px;background:#ff0000'></div><div style='clear:left;width:20px;height:10px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Blue should appear at y=0 (no left floats to clear)
expect(_count_region_color(pixels, VW, 0, 0, 20, 10, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

### CSS float line box intrusion

#### in-flow block narrows beside left float

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px'><div style='float:left;width:20px;height:20px;background:#ff0000'></div><div style='width:40px;height:20px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Blue should NOT overlap with red region (0..20, 0..20)
# Red should be at left
expect(_count_region_color(pixels, VW, 0, 0, 20, 20, 0xFFFF0000u32)).to_be_greater_than(0)
# Blue should be to the right of red
expect(_count_region_color(pixels, VW, 20, 0, 20, 20, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

### BFC float containment

#### overflow:hidden encloses float in container height

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='overflow:hidden;width:40px;background:#cccccc'><div style='float:left;width:20px;height:20px;background:#ff0000'></div></div><div style='width:40px;height:10px;background:#0000ff'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# BFC container should have expanded to contain the float
# so the blue div should be below the float (y >= 20)
expect(_count_region_color(pixels, VW, 0, 20, 40, 10, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

#### display:flow-root encloses float in container height

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='display:flow-root;width:40px;background:#cccccc'><div style='float:left;width:20px;height:20px;background:#ff0000'></div></div><div style='width:40px;height:10px;background:#0000ff'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# flow-root should contain the float, pushing blue below
expect(_count_region_color(pixels, VW, 0, 20, 40, 10, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

### display mode dispatch

#### display:flow-root renders block-level content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='display:flow-root;width:20px;height:20px;background:#ff0000'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
expect(_count_color(pixels, 0xFFFF0000u32)).to_be_greater_than(0)
```

</details>

#### display:inline-flex renders flex content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='display:inline-flex;width:20px;height:20px;background:#00ff00'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
expect(_count_color(pixels, 0xFF00FF00u32)).to_be_greater_than(0)
```

</details>

#### display:none renders nothing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='display:none;width:20px;height:20px;background:#ff0000'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
expect(_count_color(pixels, 0xFFFF0000u32)).to_equal(0)
```

</details>

### CSS float stacking

#### left and right floats do not overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:40px;height:40px'><div style='float:left;width:15px;height:15px;background:#ff0000'></div><div style='float:right;width:15px;height:15px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# Left float (red) in left region
expect(_count_region_color(pixels, VW, 0, 0, 15, 15, 0xFFFF0000u32)).to_be_greater_than(0)
# Right float (blue) in right region
expect(_count_region_color(pixels, VW, 25, 0, 15, 15, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

#### float wraps to next line when container is too narrow

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='width:30px;height:40px'><div style='float:left;width:20px;height:10px;background:#ff0000'></div><div style='float:left;width:20px;height:10px;background:#0000ff'></div></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, VW, VH).pixel_data
expect(pixels.len()).to_equal(VW * VH)
# First float at top
expect(_count_region_color(pixels, VW, 0, 0, 20, 10, 0xFFFF0000u32)).to_be_greater_than(0)
# Second float should wrap below (y >= 10)
expect(_count_region_color(pixels, VW, 0, 10, 20, 10, 0xFF0000FFu32)).to_be_greater_than(0)
```

</details>

### float/clear CSS property parsing

#### float:left sets float_code to 1

1. node set style
   - Expected: css_get_float_code(style).value equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("float", "left")
val style = be_dom_get_style(node)
expect(css_get_float_code(style).value).to_equal(1)
```

</details>

#### float:right sets float_code to 2

1. node set style
   - Expected: css_get_float_code(style).value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("float", "right")
val style = be_dom_get_style(node)
expect(css_get_float_code(style).value).to_equal(2)
```

</details>

#### clear:left sets clear_code to 1

1. node set style
   - Expected: css_get_clear_code(style).value equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("clear", "left")
val style = be_dom_get_style(node)
expect(css_get_clear_code(style).value).to_equal(1)
```

</details>

#### clear:right sets clear_code to 2

1. node set style
   - Expected: css_get_clear_code(style).value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("clear", "right")
val style = be_dom_get_style(node)
expect(css_get_clear_code(style).value).to_equal(2)
```

</details>

#### clear:both sets clear_code to 3

1. node set style
   - Expected: css_get_clear_code(style).value equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("clear", "both")
val style = be_dom_get_style(node)
expect(css_get_clear_code(style).value).to_equal(3)
```

</details>

#### float:none sets float_code to 0

1. node set style
   - Expected: css_get_float_code(style).value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("float", "none")
val style = be_dom_get_style(node)
expect(css_get_float_code(style).value).to_equal(0)
```

</details>

#### clear:none sets clear_code to 0

1. node set style
   - Expected: css_get_clear_code(style).value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("clear", "none")
val style = be_dom_get_style(node)
expect(css_get_clear_code(style).value).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
