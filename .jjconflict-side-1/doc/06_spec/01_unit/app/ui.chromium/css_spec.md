# Css Specification

> <details>

<!-- sdn-diagram:id=css_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=css_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

css_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=css_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Specification

## Scenarios

### Chromium CSS subset — flex-flow shorthand

#### expands 'row wrap' into flex-direction=row + flex-wrap=wrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = expand_flex_flow("row wrap")
expect(out.len() == 2).to_be_true()
expect(css_decls_contain(out, "flex-direction", "row")).to_be_true()
expect(css_decls_contain(out, "flex-wrap", "wrap")).to_be_true()
```

</details>

#### expands bare 'column-reverse' with default nowrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = expand_flex_flow("column-reverse")
expect(out.len() == 2).to_be_true()
expect(css_decls_contain(out, "flex-direction", "column-reverse")).to_be_true()
expect(css_decls_contain(out, "flex-wrap", "nowrap")).to_be_true()
```

</details>

#### expands 'wrap-reverse row' (order-independent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = expand_flex_flow("wrap-reverse row")
expect(out.len() == 2).to_be_true()
expect(css_decls_contain(out, "flex-direction", "row")).to_be_true()
expect(css_decls_contain(out, "flex-wrap", "wrap-reverse")).to_be_true()
```

</details>

### Chromium CSS subset — hsl/hsla color parsing

#### parses hsl(0, 100%, 50%) as pure red

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_color_value("hsl(0, 100%, 50%)")
# RGBA packed as 0xRRGGBBAA — red = 0xFF0000FF
expect(c == 0xFF0000FF).to_be_true()
```

</details>

#### parses hsl(120, 100%, 50%) as pure green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_color_value("hsl(120, 100%, 50%)")
expect(c == 0x00FF00FF).to_be_true()
```

</details>

#### parses hsl(240, 100%, 50%) as pure blue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_color_value("hsl(240, 100%, 50%)")
expect(c == 0x0000FFFF).to_be_true()
```

</details>

#### parses hsla(0, 0%, 0%, 1.0) as opaque black

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_color_value("hsla(0, 0%, 0%, 1.0)")
expect(c == 0x000000FF).to_be_true()
```

</details>

#### parses hsl(0, 0%, 100%) as white

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_color_value("hsl(0, 0%, 100%)")
expect(c == 0xFFFFFFFF).to_be_true()
```

</details>

### Chromium CSS subset — currentColor keyword

#### resolves border-color: currentColor to the element's color

1. var node = BeDomNode element
2. node set style
3. node set style
4. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = BeDomNode.element("div")
# Establish the element's color first.
node.set_style("color", "#FF00FFFF")  # magenta
node.set_style("border-width", "2px")
node.set_style("border-color", "currentColor")
expect(be_dom_get_border_color(node).value == 0xFF00FFFF).to_be_true()
```

</details>

#### accepts the mixed-case spelling 'currentColor'

1. var node = BeDomNode element
2. node set style
3. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = BeDomNode.element("div")
node.set_style("color", "#112233FF")
node.set_style("border-color", "currentColor")
expect(be_dom_get_border_color(node).value == 0x112233FF).to_be_true()
```

</details>

### Chromium CSS subset — DesktopShell glass-theme properties

#### accepts the full panel property set without losing values

1. var node = BeDomNode element
2. node set style
3. node set style
4. node set style
5. node set style
6. node set style
7. node set style
8. node set style
9. node set style
10. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = BeDomNode.element("div")
node.set_style("display", "flex")
node.set_style("flex-direction", "column")
node.set_style("gap", "8px")
node.set_style("padding", "10px")
node.set_style("background-color", "rgba(30,30,35,0.72)")
node.set_style("border-width", "1px")
node.set_style("border-color", "rgba(255,255,255,0.08)")
node.set_style("border-radius", "20px")
node.set_style("color", "#F5F5F7FF")
val s = node.style
expect(be_dom_get_display(node) == "flex").to_be_true()
expect(css_get_flex_direction(s) == "column").to_be_true()
expect(css_get_gap(s).value == 8).to_be_true()
expect(be_dom_get_padding_top(node).value == 10).to_be_true()
expect(be_dom_get_padding_left(node).value == 10).to_be_true()
expect(be_dom_get_border_width(node).value == 1).to_be_true()
expect(be_dom_get_border_radius(node).value == 20).to_be_true()
```

</details>

#### stores display: flow-root and display: contents as freeform values

1. var node1 = BeDomNode element
2. node1 set style
3. var node2 = BeDomNode element
4. node2 set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# These are not emitted by widget_to_dom for DesktopShell today
# (waived per M3 acceptance), but set_style must not panic if a
# future widget set-style path feeds them in.
var node1 = BeDomNode.element("div")
node1.set_style("display", "flow-root")
expect(be_dom_get_display(node1) == "flow-root").to_be_true()

var node2 = BeDomNode.element("div")
node2.set_style("display", "contents")
expect(be_dom_get_display(node2) == "contents").to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/css_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chromium CSS subset — flex-flow shorthand
- Chromium CSS subset — hsl/hsla color parsing
- Chromium CSS subset — currentColor keyword
- Chromium CSS subset — DesktopShell glass-theme properties

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
