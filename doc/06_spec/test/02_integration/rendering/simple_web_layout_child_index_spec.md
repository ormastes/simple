# Simple Web Layout Child Index Specification

> <details>

<!-- sdn-diagram:id=simple_web_layout_child_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_layout_child_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_layout_child_index_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_layout_child_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Layout Child Index Specification

## Scenarios

### simple web layout child index

#### keeps flat sibling block order stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _flat_rows(8)
val y0 = simple_web_layout_debug_layout_by_id(html, 200, 200, "row0", "y").to_i32()
val y1 = simple_web_layout_debug_layout_by_id(html, 200, 200, "row1", "y").to_i32()
val y7 = simple_web_layout_debug_layout_by_id(html, 200, 200, "row7", "y").to_i32()
expect(y1).to_be_greater_than(y0)
expect(y7).to_be_greater_than(y1)
```

</details>

#### renders a sibling-heavy startup fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _flat_rows(80)
val pixels = simple_web_layout_render_html_software_pixels(html, 160, 120)
expect(pixels.len()).to_equal(19200)
```

</details>

#### keeps CSS bucket candidates in cascade order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>" +
    ".unused0{height:1px}.unused1{height:2px}.unused2{height:3px}" +
    "div,.target{height:9px}#target{height:11px}.target{height:13px}" +
    "</style></head><body><div id=\"target\" class=\"target target\">row</div></body></html>"
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
expect(height).to_equal("13")
```

</details>

#### keeps spaced descendant and child selectors stable with pretrimmed parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>" +
    ".outer   >   .inner   .target{height:17px}" +
    "</style></head><body><section class=\"outer\"><div class=\"inner\"><span id=\"target\" class=\"target\">row</span></div></section></body></html>"
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
expect(height).to_equal("17")
```

</details>

#### keeps empty class attributes out of class selector buckets

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>" +
    "div{height:9px}.missing{height:13px}" +
    "</style></head><body><div id=\"plain\">row</div></body></html>"
val height = simple_web_layout_debug_style_by_id(html, "plain", "height")
expect(height).to_equal("9")
```

</details>

#### keeps overflow clipping stable with cached ancestor clips

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>" +
    "html,body{margin:0;padding:0;background-color:#ffffff}" +
    ".shell{overflow:hidden;background-color:#e5e7eb;width:12px;height:8px}" +
    ".wide{background-color:#ef4444;width:30px;height:6px}" +
    "</style></head><body><section class=\"shell\"><div class=\"wide\"></div></section></body></html>"
val pixels = simple_web_layout_render_html_software_pixels(html, 32, 24)
expect(_pixel_at(pixels, 32, 4, 2)).to_equal(0xffef4444u32)
expect(_pixel_at(pixels, 32, 16, 2)).to_equal(0xffffffffu32)
```

</details>

#### keeps widget chrome rendering stable with folded widget scans

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><section class=\"widget-panel\"><div class=\"widget\">Hello</div></section></body></html>"
val pixels = simple_web_layout_render_html_software_pixels(html, 64, 64)
expect(pixels.len()).to_equal(4096)
expect(_pixel_at(pixels, 64, 0, 0)).to_equal(0xff0066ccu32)
```

</details>

#### keeps nested flex intrinsic widths stable with shared memo

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>" +
    "html,body{margin:0;padding:0;background-color:#ffffff}" +
    ".outer{display:flex;gap:4px;width:120px;background-color:#e5e7eb}" +
    ".inner{display:flex;gap:2px;background-color:#dbeafe}" +
    ".label{display:inline;background-color:#22c55e}" +
    ".tail{display:inline;background-color:#f59e0b}" +
    "</style></head><body><section id=\"outer\" class=\"outer\">" +
    "<div id=\"inner\" class=\"inner\"><span id=\"label\" class=\"label\">ALPHA</span><span id=\"tail\" class=\"tail\">BETA</span></div>" +
    "<div id=\"right\" class=\"inner\"><span>GAMMA</span></div>" +
    "</section></body></html>"
val outer_w = simple_web_layout_debug_layout_by_id(html, 160, 80, "outer", "w").to_i32()
val inner_w = simple_web_layout_debug_layout_by_id(html, 160, 80, "inner", "w").to_i32()
val label_x = simple_web_layout_debug_layout_by_id(html, 160, 80, "label", "x").to_i32()
val tail_x = simple_web_layout_debug_layout_by_id(html, 160, 80, "tail", "x").to_i32()
val right_x = simple_web_layout_debug_layout_by_id(html, 160, 80, "right", "x").to_i32()
expect(outer_w).to_equal(120)
expect(inner_w).to_be_greater_than(0)
expect(tail_x).to_be_greater_than(label_x)
expect(right_x).to_be_greater_than(tail_x)
```

</details>

#### keeps flex wrap line heights stable with fixed line buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>" +
    "html,body{margin:0;padding:0;background-color:#ffffff}" +
    "#wrap{display:flex;flex-wrap:wrap;gap:2px;width:28px}" +
    ".item{width:12px;height:5px;background-color:#22c55e}" +
    "</style></head><body><section id=\"wrap\">" +
    "<div id=\"a\" class=\"item\"></div><div id=\"b\" class=\"item\"></div><div id=\"c\" class=\"item\"></div>" +
    "</section></body></html>"
val ay = simple_web_layout_debug_layout_by_id(html, 64, 64, "a", "y").to_i32()
val by = simple_web_layout_debug_layout_by_id(html, 64, 64, "b", "y").to_i32()
val cy = simple_web_layout_debug_layout_by_id(html, 64, 64, "c", "y").to_i32()
expect(by).to_equal(ay)
expect(cy).to_be_greater_than(by)
```

<details>
<summary>Rendered scenario source</summary>

> val html = "<html><head><style>" +<br>
>     "html,body{margin:0;padding:0;background-color:#ffffff}" +<br>
>     "#wrap{display:flex;flex-wrap:wrap;gap:2px;width:28px}" +<br>
>     ".ite$width$" +<br>
>     "</style></head><body><section id=\"wrap\">" +<br>
>     "<div id=\"a\" class=\"item\"></div><div id=\"b\" class=\"item\"></div><div id=\"c\" class=\"item\"></div>" +<br>
>     "</section></body></html>"<br>
> val ay = simple_web_layout_debug_layout_by_id(html, 64, 64, "a", "y").to_i32()<br>
> val by = simple_web_layout_debug_layout_by_id(html, 64, 64, "b", "y").to_i32()<br>
> val cy = simple_web_layout_debug_layout_by_id(html, 64, 64, "c", "y").to_i32()<br>
> expect(by).to_equal(ay)<br>
> expect(cy).to_be_greater_than(by)

</details>

</details>

#### keeps positive z-index absolute paint order stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>" +
    "html,body{margin:0;padding:0;background-color:#ffffff}" +
    "#low{position:absolute;left:0;top:0;width:12px;height:12px;background-color:#ef4444;z-index:1}" +
    "#high{position:absolute;left:0;top:0;width:12px;height:12px;background-color:#22c55e;z-index:3}" +
    "#mid{position:absolute;left:0;top:0;width:12px;height:12px;background-color:#3b82f6;z-index:2}" +
    "</style></head><body><div id=\"low\"></div><div id=\"high\"></div><div id=\"mid\"></div></body></html>"
val pixels = simple_web_layout_render_html_software_pixels(html, 24, 24)
expect(_pixel_at(pixels, 24, 2, 2)).to_equal(0xff22c55eu32)
```

</details>

#### keeps already sorted positive z-index paint order stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>" +
    "html,body{margin:0;padding:0;background-color:#ffffff}" +
    "#low{position:absolute;left:0;top:0;width:12px;height:12px;background-color:#ef4444;z-index:1}" +
    "#mid{position:absolute;left:0;top:0;width:12px;height:12px;background-color:#3b82f6;z-index:2}" +
    "#high{position:absolute;left:0;top:0;width:12px;height:12px;background-color:#22c55e;z-index:3}" +
    "</style></head><body><div id=\"low\"></div><div id=\"mid\"></div><div id=\"high\"></div></body></html>"
val pixels = simple_web_layout_render_html_software_pixels(html, 24, 24)
expect(_pixel_at(pixels, 24, 2, 2)).to_equal(0xff22c55eu32)
```

</details>

#### emits Draw IR commands for visible HTML boxes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><section id=\"panel\" style=\"width:40px;height:16px;background-color:#e5e7eb\"><div id=\"child\" style=\"height:8px;background-color:#22c55e\"></div></section></body></html>"
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
expect(composition.batches.len()).to_equal(1)
expect(composition.batches[0].commands.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simple_web_layout_child_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple web layout child index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
