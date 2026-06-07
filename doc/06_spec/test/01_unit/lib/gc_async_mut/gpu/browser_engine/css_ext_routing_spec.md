# Css Ext Routing Specification

> 1. node set style

<!-- sdn-diagram:id=css_ext_routing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=css_ext_routing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

css_ext_routing_spec -> std
css_ext_routing_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=css_ext_routing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Ext Routing Specification

## Scenarios

### css_ext routing into parse_declaration

#### routes `float: left` through css_ext::parse_float_keyword

1. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("float", "left")
val style = be_dom_get_style(node)
expect(css_get_float_code(style).value == parse_float_keyword("left")).to_be_true()
```

</details>

#### routes `clear: both` through css_ext::parse_clear_keyword

1. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("clear", "both")
val style = be_dom_get_style(node)
expect(css_get_clear_code(style).value == parse_clear_keyword("both")).to_be_true()
```

</details>

#### routes `outline-style: dashed` through css_ext::parse_outline_style

1. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("outline-style", "dashed")
val style = be_dom_get_style(node)
expect(css_get_outline_style(style) == "dashed").to_be_true()
expect(parse_outline_style("dashed") == 3).to_be_true()
```

</details>

#### expands the `outline` shorthand into width/style/color

1. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("outline", "2px solid #ff0000")
val style = be_dom_get_style(node)
expect(css_get_outline_width(style).value == 2).to_be_true()
expect(css_get_outline_style(style) == "solid").to_be_true()
expect(css_get_outline_color(style) != 0).to_be_true()
```

</details>

#### routes `outline-offset` into the Outline record

1. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("outline-offset", "4px")
val style = be_dom_get_style(node)
expect(css_get_outline_offset(style).value == 4).to_be_true()
```

</details>

#### routes `width: calc(10px + 5px)` through css_ext::calc_resolve

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cv = parse_length_or_calc("calc(10px + 5px)")
expect(css_value_as_i32(cv) == 15).to_be_true()
```

</details>

#### honours operator precedence for `calc(2px + 3px * 4)`

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cv = parse_length_or_calc("calc(2px + 3px * 4)")
expect(css_value_as_i32(cv) == 14).to_be_true()
```

</details>

#### falls back to parse_css_value when calc() is malformed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Unknown trailing token fails calc, plain parser falls back to auto.
val cv = parse_length_or_calc("calc(10px +)")
expect(css_value_unit(cv) == "auto").to_be_true()
```

</details>

#### applies `calc(...)` through set_style(\

1. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("div")
node.set_style("width", "calc(100px - 25px)")
val style = be_dom_get_style(node)
expect(css_value_as_i32(css_get_width(style)) == 75).to_be_true()
```

</details>

#### keeps calc_resolve pure and predictable for external callers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = calc_resolve([6, 2, 3], [CALC_OP_ADD, CALC_OP_MUL])
expect(calc_value_ok(result)).to_be_true()
expect(calc_value_pixels(result) == 12).to_be_true()
```

</details>

#### expands flex-flow and applies direction plus wrapping

1. node set style
2. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decls = parse_declarations("flex-flow: column wrap;")
expect(decls.len() == 2).to_be_true()
expect(decls[0].property == "flex-direction").to_be_true()
expect(decls[0].value == "column").to_be_true()
expect(decls[1].property == "flex-wrap").to_be_true()
expect(decls[1].value == "wrap").to_be_true()

val node = BeDomNode.element("div")
node.set_style(decls[0].property, decls[0].value)
node.set_style(decls[1].property, decls[1].value)
val style = be_dom_get_style(node)
expect(css_get_flex_direction(style) == "column").to_be_true()
expect(css_get_flex_wrap(style) == "wrap").to_be_true()
```

</details>

#### stores list-style:none as list-style-type state

1. node set style


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.element("ul")
node.set_style("list-style", "none")
val style = be_dom_get_style(node)
expect(css_get_list_style_type(style) == "none").to_be_true()
expect(eval_supports_query("(list-style-type: none)")).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- css_ext routing into parse_declaration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
