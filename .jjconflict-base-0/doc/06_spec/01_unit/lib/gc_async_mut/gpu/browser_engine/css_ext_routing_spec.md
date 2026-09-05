# Css Ext Routing Specification

> Tests covering css_ext routing into parse_declaration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Ext Routing Specification

## Scenarios

### css_ext routing into parse_declaration

#### routes `float: left` through css_ext::parse_float_keyword

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes `float: left` through css_ext::parse_float_keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes `float: left` through css_ext::parse_float_keyword")
val node = BeDomNode.element("div")
node.set_style("float", "left")
val style = be_dom_get_style(node)
expect(css_get_float_code(style).value == parse_float_keyword("left")).to_be_true()
```

</details>

#### routes `clear: both` through css_ext::parse_clear_keyword

- routes `clear: both` through css_ext::parse_clear_keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes `clear: both` through css_ext::parse_clear_keyword")
val node = BeDomNode.element("div")
node.set_style("clear", "both")
val style = be_dom_get_style(node)
expect(css_get_clear_code(style).value == parse_clear_keyword("both")).to_be_true()
```

</details>

#### routes `outline-style: dashed` through css_ext::parse_outline_style

- routes `outline-style: dashed` through css_ext::parse_outline_style


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes `outline-style: dashed` through css_ext::parse_outline_style")
val node = BeDomNode.element("div")
node.set_style("outline-style", "dashed")
val style = be_dom_get_style(node)
expect(css_get_outline_style(style) == "dashed").to_be_true()
expect(parse_outline_style("dashed") == 3).to_be_true()
```

</details>

#### expands the `outline` shorthand into width/style/color

- expands the `outline` shorthand into width/style/color


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands the `outline` shorthand into width/style/color")
val node = BeDomNode.element("div")
node.set_style("outline", "2px solid #ff0000")
val style = be_dom_get_style(node)
expect(css_get_outline_width(style).value == 2).to_be_true()
expect(css_get_outline_style(style) == "solid").to_be_true()
expect(css_get_outline_color(style) != 0).to_be_true()
```

</details>

#### routes `outline-offset` into the Outline record

- routes `outline-offset` into the Outline record


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes `outline-offset` into the Outline record")
val node = BeDomNode.element("div")
node.set_style("outline-offset", "4px")
val style = be_dom_get_style(node)
expect(css_get_outline_offset(style).value == 4).to_be_true()
```

</details>

#### routes `width: calc(10px + 5px)` through css_ext::calc_resolve

- routes `width: calc(10px + 5px)` through css_ext::calc_resolve


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes `width: calc(10px + 5px)` through css_ext::calc_resolve")
val cv = parse_length_or_calc("calc(10px + 5px)")
expect(css_value_as_i32(cv) == 15).to_be_true()
```

</details>

#### honours operator precedence for `calc(2px + 3px * 4)`

- honours operator precedence for `calc(2px + 3px * 4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("honours operator precedence for `calc(2px + 3px * 4)`")
val cv = parse_length_or_calc("calc(2px + 3px * 4)")
expect(css_value_as_i32(cv) == 14).to_be_true()
```

</details>

#### falls back to parse_css_value when calc() is malformed

- falls back to parse_css_value when calc() is malformed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to parse_css_value when calc() is malformed")
# Unknown trailing token fails calc, plain parser falls back to auto.
val cv = parse_length_or_calc("calc(10px +)")
expect(css_value_unit(cv) == "auto").to_be_true()
```

</details>

#### applies `calc(...)` through set_style(\

- applies `calc(...)` through set_style(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies `calc(...)` through set_style(\")
val node = BeDomNode.element("div")
node.set_style("width", "calc(100px - 25px)")
val style = be_dom_get_style(node)
expect(css_value_as_i32(css_get_width(style)) == 75).to_be_true()
```

</details>

#### keeps calc_resolve pure and predictable for external callers

- keeps calc_resolve pure and predictable for external callers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps calc_resolve pure and predictable for external callers")
val result = calc_resolve([6, 2, 3], [CALC_OP_ADD, CALC_OP_MUL])
expect(calc_value_ok(result)).to_be_true()
expect(calc_value_pixels(result) == 12).to_be_true()
```

</details>

#### expands flex-flow and applies direction plus wrapping

- expands flex-flow and applies direction plus wrapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands flex-flow and applies direction plus wrapping")
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

- stores list-style:none as list-style-type state


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores list-style:none as list-style-type state")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering css_ext routing into parse_declaration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c722cec64a8796a85d0f8a745463fcd8ab1a5768ba1a2628a804b08042067b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c722cec64a8796a85d0f8a745463fcd8ab1a5768ba1a2628a804b08042067b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c722cec64a8796a85d0f8a745463fcd8ab1a5768ba1a2628a804b08042067b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes `float: left` through css_ext::parse_float_keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes `clear: both` through css_ext::parse_clear_keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes `outline-style: dashed` through css_ext::parse_outline_style' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
