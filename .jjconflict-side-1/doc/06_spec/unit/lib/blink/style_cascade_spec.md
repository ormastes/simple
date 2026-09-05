# Style Cascade Specification

> Tests for the CSS style cascade engine — parse_length_value, parse_color_value, parse_f64_value, apply_declaration, and resolve_style. Mirrors Blink's StyleResolver behaviour for a core set of CSS properties.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Cascade Specification

Tests for the CSS style cascade engine — parse_length_value, parse_color_value, parse_f64_value, apply_declaration, and resolve_style. Mirrors Blink's StyleResolver behaviour for a core set of CSS properties.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/lib/blink/style_cascade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the CSS style cascade engine — parse_length_value, parse_color_value,
parse_f64_value, apply_declaration, and resolve_style. Mirrors Blink's
StyleResolver behaviour for a core set of CSS properties.

## Scenarios

### parse_length_value

#### 100px returns Length with value 100 and unit px

- 100px returns Length with value 100 and unit px
   - Expected: value_ok is true
   - Expected: unit_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("100px returns Length with value 100 and unit px")
val result = parse_length_value("100px")
val value_ok = result.value > 99.9 && result.value < 100.1
val unit_ok  = result.unit == "px"
expect(value_ok).to_equal(true)
expect(unit_ok).to_equal(true)
```

</details>

#### empty string returns Length(0, px)

- empty string returns Length(0, px)
   - Expected: value_ok is true
   - Expected: unit_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string returns Length(0, px)")
val result = parse_length_value("")
val value_ok = result.value > -0.001 && result.value < 0.001
val unit_ok  = result.unit == "px"
expect(value_ok).to_equal(true)
expect(unit_ok).to_equal(true)
```

</details>

### parse_color_value

#### reads a plain named colour

- reads a plain named colour
- read `red`
   - Expected: _color_read("red") equals `255,0,0,255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a plain named colour")
step("read `red`")
expect(_color_read("red")).to_equal("255,0,0,255")
```

</details>

#### reads a name from the full CSS table, not a nine-colour subset

- reads a name from the full CSS table, not a nine-colour subset
- read `rebeccapurple` and `cornflowerblue`, outside the old built-in list
   - Expected: _color_read("rebeccapurple") equals `102,51,153,255`
   - Expected: _color_read("cornflowerblue") equals `100,149,237,255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a name from the full CSS table, not a nine-colour subset")
step("read `rebeccapurple` and `cornflowerblue`, outside the old built-in list")
expect(_color_read("rebeccapurple")).to_equal("102,51,153,255")
expect(_color_read("cornflowerblue")).to_equal("100,149,237,255")
```

</details>

#### reads all four hex lengths including the alpha forms

- reads all four hex lengths including the alpha forms
- read #RGB, #RGBA, #RRGGBB and #RRGGBBAA
   - Expected: _color_read("#f00") equals `255,0,0,255`
   - Expected: _color_read("#f008") equals `255,0,0,136`
   - Expected: _color_read("#ff0000") equals `255,0,0,255`
   - Expected: _color_read("#11223344") equals `17,34,51,68`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads all four hex lengths including the alpha forms")
step("read #RGB, #RGBA, #RRGGBB and #RRGGBBAA")
expect(_color_read("#f00")).to_equal("255,0,0,255")
expect(_color_read("#f008")).to_equal("255,0,0,136")
expect(_color_read("#ff0000")).to_equal("255,0,0,255")
expect(_color_read("#11223344")).to_equal("17,34,51,68")
```

</details>

#### reads rgb() and rgba() in both CSS forms

- reads rgb() and rgba() in both CSS forms
- read the legacy comma form and the modern slash-alpha form
   - Expected: _color_read("rgb(255, 128, 0)") equals `255,128,0,255`
   - Expected: _color_read("rgba(255, 128, 0, 0.5)") equals `255,128,0,128`
   - Expected: _color_read("rgb(255 128 0 / 50%)") equals `255,128,0,128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads rgb() and rgba() in both CSS forms")
step("read the legacy comma form and the modern slash-alpha form")
expect(_color_read("rgb(255, 128, 0)")).to_equal("255,128,0,255")
expect(_color_read("rgba(255, 128, 0, 0.5)")).to_equal("255,128,0,128")
expect(_color_read("rgb(255 128 0 / 50%)")).to_equal("255,128,0,128")
```

</details>

#### reads hsl() and hsla() in both CSS forms

- reads hsl() and hsla() in both CSS forms
- read the legacy comma form and the modern slash-alpha form
   - Expected: _color_read("hsl(120, 100%, 50%)") equals `0,255,0,255`
   - Expected: _color_read("hsla(0, 100%, 50%, 0.5)") equals `255,0,0,128`
   - Expected: _color_read("hsl(240deg 100% 50% / 25%)") equals `0,0,255,64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads hsl() and hsla() in both CSS forms")
step("read the legacy comma form and the modern slash-alpha form")
expect(_color_read("hsl(120, 100%, 50%)")).to_equal("0,255,0,255")
expect(_color_read("hsla(0, 100%, 50%, 0.5)")).to_equal("255,0,0,128")
expect(_color_read("hsl(240deg 100% 50% / 25%)")).to_equal("0,0,255,64")
```

</details>

#### reports an unsupported colour as unsupported instead of painting black

- reports an unsupported colour as unsupported instead of painting black
- read the colour syntaxes this cascade does not implement
   - Expected: _color_read("color-mix(in srgb, red, blue)") equals `unsupported`
   - Expected: _color_read("lab(50% 40 59.5)") equals `unsupported`
   - Expected: _color_read("currentColor") equals `unsupported`
   - Expected: _color_read("var(--brand)") equals `unsupported`
- read a malformed colour and a name that is not a CSS colour
   - Expected: _color_read("#gg0000") equals `unsupported`
   - Expected: _color_read("rgb(red, 0, 0)") equals `unsupported`
   - Expected: _color_read("notacolour") equals `unsupported`
   - Expected: _color_read("") equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an unsupported colour as unsupported instead of painting black")
step("read the colour syntaxes this cascade does not implement")
# This is the regression that made the whole gap invisible: each of
# these used to come back as opaque black, indistinguishable from an
# author writing `color: black`.
expect(_color_read("color-mix(in srgb, red, blue)")).to_equal("unsupported")
expect(_color_read("lab(50% 40 59.5)")).to_equal("unsupported")
expect(_color_read("currentColor")).to_equal("unsupported")
expect(_color_read("var(--brand)")).to_equal("unsupported")
step("read a malformed colour and a name that is not a CSS colour")
expect(_color_read("#gg0000")).to_equal("unsupported")
expect(_color_read("rgb(red, 0, 0)")).to_equal("unsupported")
expect(_color_read("notacolour")).to_equal("unsupported")
expect(_color_read("")).to_equal("unsupported")
```

</details>

### applying an unsupported colour declaration

#### leaves the property at its previous value instead of repainting it

- leaves the property at its previous value instead of repainting it
- start from a style whose colour is red
   - Expected: base.color.r > 0.99 is true
- apply `color: color-mix(in srgb, red, blue)`, which is unsupported
- the invalid declaration is dropped — the colour is still red, not black
   - Expected: after.color.r > 0.99 is true
   - Expected: after.color.g < 0.01 is true
   - Expected: after.color.b < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the property at its previous value instead of repainting it")
step("start from a style whose colour is red")
val base = apply_declaration(computed_style_default(), CssDeclaration(
    property: "color", value: "red", important: false
))
expect(base.color.r > 0.99).to_equal(true)
step("apply `color: color-mix(in srgb, red, blue)`, which is unsupported")
val after = apply_declaration(base, CssDeclaration(
    property: "color", value: "color-mix(in srgb, red, blue)", important: false
))
step("the invalid declaration is dropped — the colour is still red, not black")
expect(after.color.r > 0.99).to_equal(true)
expect(after.color.g < 0.01).to_equal(true)
expect(after.color.b < 0.01).to_equal(true)
```

</details>

#### leaves background-color at its previous value too

- leaves background-color at its previous value too
- start from a style whose background is white
   - Expected: base.background_color.r > 0.99 is true
   - Expected: base.background_color.b > 0.99 is true
- apply `background-color: var(--brand)`, which is unsupported
- the background is still white, not black
   - Expected: after.background_color.r > 0.99 is true
   - Expected: after.background_color.g > 0.99 is true
   - Expected: after.background_color.b > 0.99 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves background-color at its previous value too")
step("start from a style whose background is white")
val base = apply_declaration(computed_style_default(), CssDeclaration(
    property: "background-color", value: "white", important: false
))
expect(base.background_color.r > 0.99).to_equal(true)
expect(base.background_color.b > 0.99).to_equal(true)
step("apply `background-color: var(--brand)`, which is unsupported")
val after = apply_declaration(base, CssDeclaration(
    property: "background-color", value: "var(--brand)", important: false
))
step("the background is still white, not black")
expect(after.background_color.r > 0.99).to_equal(true)
expect(after.background_color.g > 0.99).to_equal(true)
expect(after.background_color.b > 0.99).to_equal(true)
```

</details>

#### still applies a supported colour written in a modern notation

- still applies a supported colour written in a modern notation
- apply `color: hsl(240deg 100% 50%)` to a default style
   - Expected: after.color.b > 0.99 is true
   - Expected: after.color.r < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still applies a supported colour written in a modern notation")
step("apply `color: hsl(240deg 100% 50%)` to a default style")
val after = apply_declaration(computed_style_default(), CssDeclaration(
    property: "color", value: "hsl(240deg 100% 50%)", important: false
))
expect(after.color.b > 0.99).to_equal(true)
expect(after.color.r < 0.01).to_equal(true)
```

</details>

### parse_f64_value

#### 0.5 returns 0.5

- 0.5 returns 0.5
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0.5 returns 0.5")
val result = parse_f64_value("0.5")
val ok = result > 0.49 && result < 0.51
expect(ok).to_equal(true)
```

</details>

#### invalid string returns 0.0

- invalid string returns 0.0
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid string returns 0.0")
val result = parse_f64_value("abc")
val ok = result > -0.001 && result < 0.001
expect(ok).to_equal(true)
```

</details>

### apply_declaration

#### color: blue sets style.color to blue

- color: blue sets style.color to blue
   - Expected: b_ok is true
   - Expected: r_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("color: blue sets style.color to blue")
val style = computed_style_default()
val decl = CssDeclaration(property: "color", value: "blue", important: false)
val updated = apply_declaration(style, decl)
val b_ok = updated.color.b > 0.99
val r_ok = updated.color.r < 0.01
expect(b_ok).to_equal(true)
expect(r_ok).to_equal(true)
```

</details>

#### unknown property is ignored and style is returned unchanged

- unknown property is ignored and style is returned unchanged
   - Expected: display_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown property is ignored and style is returned unchanged")
val style = computed_style_default()
val decl = CssDeclaration(property: "unknown-property", value: "whatever", important: false)
val updated = apply_declaration(style, decl)
# display should remain the default (Inline)
val display_ok = updated.display == Display.Inline
expect(display_ok).to_equal(true)
```

</details>

### resolve_style cascade order

#### the most specific selector wins even when it is listed first

- the most specific selector wins even when it is listed first
- author three rules that all set colour on the same div: #go blue, .btn green, div red
- resolve the div's style
- expect the id rule to win: blue, not the last-listed red
   - Expected: result.color.b > 0.99 is true
   - Expected: result.color.r < 0.01 is true
   - Expected: result.color.g < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the most specific selector wins even when it is listed first")
step("author three rules that all set colour on the same div: #go blue, .btn green, div red")
val tree = _cascade_fixture_tree()
var rs: [CssStyleRule] = []
rs.push(_cascade_rule("#go", "color", "blue", false))
rs.push(_cascade_rule(".btn", "color", "green", false))
rs.push(_cascade_rule("div", "color", "red", false))

step("resolve the div's style")
val result = resolve_style(tree, 1, computed_style_default(), _cascade_sheet(rs))

step("expect the id rule to win: blue, not the last-listed red")
# #go is (1,0,0), .btn (0,1,0), div (0,0,1) — the id rule outranks both
# despite appearing first in source order.
expect(result.color.b > 0.99).to_equal(true)
expect(result.color.r < 0.01).to_equal(true)
expect(result.color.g < 0.01).to_equal(true)
```

</details>

#### an !important declaration beats a more specific normal one

- an !important declaration beats a more specific normal one
- author `#go { color: blue }` and `div { color: red !important }`
- resolve the div's style
- expect red: !important outranks the id selector entirely
   - Expected: result.color.r > 0.99 is true
   - Expected: result.color.b < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an !important declaration beats a more specific normal one")
step("author `#go { color: blue }` and `div { color: red !important }`")
val tree = _cascade_fixture_tree()
var rs: [CssStyleRule] = []
rs.push(_cascade_rule("#go", "color", "blue", false))
rs.push(_cascade_rule("div", "color", "red", true))

step("resolve the div's style")
val result = resolve_style(tree, 1, computed_style_default(), _cascade_sheet(rs))

step("expect red: !important outranks the id selector entirely")
expect(result.color.r > 0.99).to_equal(true)
expect(result.color.b < 0.01).to_equal(true)
```

</details>

#### at equal specificity the later rule wins

- at equal specificity the later rule wins
- author `div { color: red }` then `div { color: blue }`
- resolve the div's style
- expect blue: the tie is broken by source order, last wins
   - Expected: result.color.b > 0.99 is true
   - Expected: result.color.r < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("at equal specificity the later rule wins")
step("author `div { color: red }` then `div { color: blue }`")
val tree = _cascade_fixture_tree()
var rs: [CssStyleRule] = []
rs.push(_cascade_rule("div", "color", "red", false))
rs.push(_cascade_rule("div", "color", "blue", false))

step("resolve the div's style")
val result = resolve_style(tree, 1, computed_style_default(), _cascade_sheet(rs))

step("expect blue: the tie is broken by source order, last wins")
expect(result.color.b > 0.99).to_equal(true)
expect(result.color.r < 0.01).to_equal(true)
```

</details>

### resolve_style inheritance

#### colour inherits from the parent while display restarts at its initial value

- colour inherits from the parent while display restarts at its initial value
- give the parent red text and a block display, with no rules matching the child
- resolve the child against an empty stylesheet
- expect inherited colour and text-align to carry over
   - Expected: result.color.r > 0.99 is true
   - Expected: result.text_align == TextAlign.Center is true
- expect non-inherited display and background to be back at their initial values
   - Expected: result.display == Display.Inline is true
   - Expected: result.background_color.a < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("colour inherits from the parent while display restarts at its initial value")
step("give the parent red text and a block display, with no rules matching the child")
val tree = _cascade_fixture_tree()
val base = computed_style_default()
val parent = ComputedStyle(
    display: Display.Block,
    position: base.position,
    overflow: base.overflow,
    visibility: base.visibility,
    text_align: TextAlign.Center,
    opacity: base.opacity,
    color: sk_color4f(1.0, 0.0, 0.0, 1.0),
    background_color: sk_color4f(0.0, 1.0, 0.0, 1.0),
    margin_left: base.margin_left,
    margin_right: base.margin_right,
    margin_top: base.margin_top,
    margin_bottom: base.margin_bottom,
    padding_left: base.padding_left,
    padding_top: base.padding_top,
    padding_right: base.padding_right,
    padding_bottom: base.padding_bottom,
    width: base.width,
    height: base.height
)
var empty: [CssStyleRule] = []

step("resolve the child against an empty stylesheet")
val result = resolve_style(tree, 1, parent, _cascade_sheet(empty))

step("expect inherited colour and text-align to carry over")
expect(result.color.r > 0.99).to_equal(true)
expect(result.text_align == TextAlign.Center).to_equal(true)

step("expect non-inherited display and background to be back at their initial values")
expect(result.display == Display.Inline).to_equal(true)
expect(result.background_color.a < 0.01).to_equal(true)
```

</details>

### resolve_style_with_state on a literal tree

#### a :hover rule applies only while that node is the hovered node

- a :hover rule applies only while that node is the hovered node
- author `.btn:hover { background-color: red }`
- resolve with no node hovered
- expect the background to stay at the initial transparent value
   - Expected: idle.background_color.r < 0.99 is true
- resolve again with this node hovered
- expect the background to become red
   - Expected: hovered.background_color.r > 0.99 is true
   - Expected: hovered.background_color.a > 0.99 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a :hover rule applies only while that node is the hovered node")
step("author `.btn:hover { background-color: red }`")
val tree = _cascade_fixture_tree()
var rs: [CssStyleRule] = []
rs.push(_cascade_rule(".btn:hover", "background-color", "red", false))
val sheet = _cascade_sheet(rs)
val parent = computed_style_default()

step("resolve with no node hovered")
val idle = resolve_style_with_state(tree, 1, parent, sheet, interaction_state_empty())

step("expect the background to stay at the initial transparent value")
expect(idle.background_color.r < 0.99).to_equal(true)

step("resolve again with this node hovered")
val hovered = resolve_style_with_state(tree, 1, parent, sheet, interaction_state_with_hover(1))

step("expect the background to become red")
expect(hovered.background_color.r > 0.99).to_equal(true)
expect(hovered.background_color.a > 0.99).to_equal(true)
```

</details>

### resolve_style

#### rule matching div sets its color

- rule matching div sets its color
   - Expected: r_ok is true
   - Expected: g_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rule matching div sets its color")
var tree = dom_tree_new()
val div_id = tree.create_element("div")
tree.append_child(tree.root_id, div_id)

val decl = CssDeclaration(property: "color", value: "red", important: false)
var decls: [CssDeclaration] = []
decls.push(decl)
val rule = CssStyleRule(selector: "div", declarations: decls)
var rules: [CssStyleRule] = []
rules.push(rule)
val sheet = CssStyleSheet(rules: rules, errors: [])

val parent_style = computed_style_default()
val result = resolve_style(tree, div_id, parent_style, sheet)
val r_ok = result.color.r > 0.99
val g_ok = result.color.g < 0.01
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
```

</details>

#### non-matching rule does not affect style

- non-matching rule does not affect style
   - Expected: r_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-matching rule does not affect style")
var tree = dom_tree_new()
val span_id = tree.create_element("span")
tree.append_child(tree.root_id, span_id)

val decl = CssDeclaration(property: "color", value: "red", important: false)
var decls: [CssDeclaration] = []
decls.push(decl)
val rule = CssStyleRule(selector: "div", declarations: decls)
var rules: [CssStyleRule] = []
rules.push(rule)
val sheet = CssStyleSheet(rules: rules, errors: [])

val parent_style = computed_style_default()
val result = resolve_style(tree, span_id, parent_style, sheet)
# color should remain inherited from parent (default black: r=0)
val r_ok = result.color.r < 0.01
expect(r_ok).to_equal(true)
```

</details>

### resolve_style_with_state: :hover pseudo-class

#### .btn:hover { background-color: red } only applies when hovered

- .btn:hover { background-color: red } only applies when hovered
   - Expected: idle_not_red is true
   - Expected: hover_r_ok is true
   - Expected: hover_g_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step(".btn:hover { background-color: red } only applies when hovered")
var tree = dom_tree_new()
val btn_id = tree.create_element("button")
tree.append_child(tree.root_id, btn_id)
tree.set_attribute(btn_id, "class", "btn")

val decl = CssDeclaration(property: "background-color", value: "red", important: false)
var decls: [CssDeclaration] = []
decls.push(decl)
val rule = CssStyleRule(selector: ".btn:hover", declarations: decls)
var rules: [CssStyleRule] = []
rules.push(rule)
val sheet = CssStyleSheet(rules: rules, errors: [])

val parent_style = computed_style_default()

# With empty state, :hover must not match — background stays at initial.
val idle = resolve_style_with_state(tree, btn_id, parent_style, sheet, interaction_state_empty())
val idle_not_red = idle.background_color.r < 0.99
expect(idle_not_red).to_equal(true)

# With hovered_id == btn_id, :hover matches — background becomes red.
val hovered = resolve_style_with_state(tree, btn_id, parent_style, sheet, interaction_state_with_hover(btn_id))
val hover_r_ok = hovered.background_color.r > 0.99
val hover_g_ok = hovered.background_color.g < 0.01
expect(hover_r_ok).to_equal(true)
expect(hover_g_ok).to_equal(true)
```

</details>

### apply_declaration: margin/padding shorthand expansion

#### margin: 10px sets all four sides to 10px

- margin: 10px sets all four sides to 10px
- apply the single-value margin shorthand
- expect top, right, bottom, left all 10px
   - Expected: updated.margin_top.value > 9.9 and updated.margin_top.value < 10.1 is true
   - Expected: updated.margin_right.value > 9.9 and updated.margin_right.value < 10.1 is true
   - Expected: updated.margin_bottom.value > 9.9 and updated.margin_bottom.value < 10.1 is true
   - Expected: updated.margin_left.value > 9.9 and updated.margin_left.value < 10.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("margin: 10px sets all four sides to 10px")
step("apply the single-value margin shorthand")
val style = computed_style_default()
val decl = CssDeclaration(property: "margin", value: "10px", important: false)
val updated = apply_declaration(style, decl)

step("expect top, right, bottom, left all 10px")
expect(updated.margin_top.value > 9.9 and updated.margin_top.value < 10.1).to_equal(true)
expect(updated.margin_right.value > 9.9 and updated.margin_right.value < 10.1).to_equal(true)
expect(updated.margin_bottom.value > 9.9 and updated.margin_bottom.value < 10.1).to_equal(true)
expect(updated.margin_left.value > 9.9 and updated.margin_left.value < 10.1).to_equal(true)
```

</details>

#### margin: 10px 20px sets vertical 10px and horizontal 20px

- margin: 10px 20px sets vertical 10px and horizontal 20px
- apply the two-value margin shorthand
- expect top/bottom 10px, left/right 20px
   - Expected: updated.margin_top.value > 9.9 and updated.margin_top.value < 10.1 is true
   - Expected: updated.margin_bottom.value > 9.9 and updated.margin_bottom.value < 10.1 is true
   - Expected: updated.margin_left.value > 19.9 and updated.margin_left.value < 20.1 is true
   - Expected: updated.margin_right.value > 19.9 and updated.margin_right.value < 20.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("margin: 10px 20px sets vertical 10px and horizontal 20px")
step("apply the two-value margin shorthand")
val style = computed_style_default()
val decl = CssDeclaration(property: "margin", value: "10px 20px", important: false)
val updated = apply_declaration(style, decl)

step("expect top/bottom 10px, left/right 20px")
expect(updated.margin_top.value > 9.9 and updated.margin_top.value < 10.1).to_equal(true)
expect(updated.margin_bottom.value > 9.9 and updated.margin_bottom.value < 10.1).to_equal(true)
expect(updated.margin_left.value > 19.9 and updated.margin_left.value < 20.1).to_equal(true)
expect(updated.margin_right.value > 19.9 and updated.margin_right.value < 20.1).to_equal(true)
```

</details>

#### margin: 10px 20px 30px sets top 10px, left/right 20px, bottom 30px

- margin: 10px 20px 30px sets top 10px, left/right 20px, bottom 30px
- apply the three-value margin shorthand
- expect top 10px, right/left 20px, bottom 30px — the classic 3-value trap
   - Expected: updated.margin_top.value > 9.9 and updated.margin_top.value < 10.1 is true
   - Expected: updated.margin_right.value > 19.9 and updated.margin_right.value < 20.1 is true
   - Expected: updated.margin_left.value > 19.9 and updated.margin_left.value < 20.1 is true
   - Expected: updated.margin_bottom.value > 29.9 and updated.margin_bottom.value < 30.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("margin: 10px 20px 30px sets top 10px, left/right 20px, bottom 30px")
step("apply the three-value margin shorthand")
val style = computed_style_default()
val decl = CssDeclaration(property: "margin", value: "10px 20px 30px", important: false)
val updated = apply_declaration(style, decl)

step("expect top 10px, right/left 20px, bottom 30px — the classic 3-value trap")
expect(updated.margin_top.value > 9.9 and updated.margin_top.value < 10.1).to_equal(true)
expect(updated.margin_right.value > 19.9 and updated.margin_right.value < 20.1).to_equal(true)
expect(updated.margin_left.value > 19.9 and updated.margin_left.value < 20.1).to_equal(true)
expect(updated.margin_bottom.value > 29.9 and updated.margin_bottom.value < 30.1).to_equal(true)
```

</details>

#### margin: 10px 20px 30px 40px sets top/right/bottom/left clockwise

- margin: 10px 20px 30px 40px sets top/right/bottom/left clockwise
- apply the four-value margin shorthand
- expect top 10, right 20, bottom 30, left 40 — clockwise from the top
   - Expected: updated.margin_top.value > 9.9 and updated.margin_top.value < 10.1 is true
   - Expected: updated.margin_right.value > 19.9 and updated.margin_right.value < 20.1 is true
   - Expected: updated.margin_bottom.value > 29.9 and updated.margin_bottom.value < 30.1 is true
   - Expected: updated.margin_left.value > 39.9 and updated.margin_left.value < 40.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("margin: 10px 20px 30px 40px sets top/right/bottom/left clockwise")
step("apply the four-value margin shorthand")
val style = computed_style_default()
val decl = CssDeclaration(property: "margin", value: "10px 20px 30px 40px", important: false)
val updated = apply_declaration(style, decl)

step("expect top 10, right 20, bottom 30, left 40 — clockwise from the top")
expect(updated.margin_top.value > 9.9 and updated.margin_top.value < 10.1).to_equal(true)
expect(updated.margin_right.value > 19.9 and updated.margin_right.value < 20.1).to_equal(true)
expect(updated.margin_bottom.value > 29.9 and updated.margin_bottom.value < 30.1).to_equal(true)
expect(updated.margin_left.value > 39.9 and updated.margin_left.value < 40.1).to_equal(true)
```

</details>

#### padding: 5px 6px 7px 8px sets all four padding longhands clockwise

- padding: 5px 6px 7px 8px sets all four padding longhands clockwise
- apply the four-value padding shorthand
- expect top 5, right 6, bottom 7, left 8
   - Expected: updated.padding_top.value > 4.9 and updated.padding_top.value < 5.1 is true
   - Expected: updated.padding_right.value > 5.9 and updated.padding_right.value < 6.1 is true
   - Expected: updated.padding_bottom.value > 6.9 and updated.padding_bottom.value < 7.1 is true
   - Expected: updated.padding_left.value > 7.9 and updated.padding_left.value < 8.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("padding: 5px 6px 7px 8px sets all four padding longhands clockwise")
step("apply the four-value padding shorthand")
val style = computed_style_default()
val decl = CssDeclaration(property: "padding", value: "5px 6px 7px 8px", important: false)
val updated = apply_declaration(style, decl)

step("expect top 5, right 6, bottom 7, left 8")
expect(updated.padding_top.value > 4.9 and updated.padding_top.value < 5.1).to_equal(true)
expect(updated.padding_right.value > 5.9 and updated.padding_right.value < 6.1).to_equal(true)
expect(updated.padding_bottom.value > 6.9 and updated.padding_bottom.value < 7.1).to_equal(true)
expect(updated.padding_left.value > 7.9 and updated.padding_left.value < 8.1).to_equal(true)
```

</details>

#### a later longhand overrides an earlier shorthand for that one side

- a later longhand overrides an earlier shorthand for that one side
- author `margin: 10px; margin-top: 20px` in source order via resolve_style
- expect top 20px (longhand won) but right/bottom/left still 10px from the shorthand
   - Expected: result.margin_top.value > 19.9 and result.margin_top.value < 20.1 is true
   - Expected: result.margin_right.value > 9.9 and result.margin_right.value < 10.1 is true
   - Expected: result.margin_bottom.value > 9.9 and result.margin_bottom.value < 10.1 is true
   - Expected: result.margin_left.value > 9.9 and result.margin_left.value < 10.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a later longhand overrides an earlier shorthand for that one side")
step("author `margin: 10px; margin-top: 20px` in source order via resolve_style")
val tree = _cascade_fixture_tree()
var rs: [CssStyleRule] = []
rs.push(_cascade_rule("div", "margin", "10px", false))
rs.push(_cascade_rule("div", "margin-top", "20px", false))
val result = resolve_style(tree, 1, computed_style_default(), _cascade_sheet(rs))

step("expect top 20px (longhand won) but right/bottom/left still 10px from the shorthand")
expect(result.margin_top.value > 19.9 and result.margin_top.value < 20.1).to_equal(true)
expect(result.margin_right.value > 9.9 and result.margin_right.value < 10.1).to_equal(true)
expect(result.margin_bottom.value > 9.9 and result.margin_bottom.value < 10.1).to_equal(true)
expect(result.margin_left.value > 9.9 and result.margin_left.value < 10.1).to_equal(true)
```

</details>

#### a later shorthand overrides an earlier longhand on every side

- a later shorthand overrides an earlier longhand on every side
- author `margin-top: 20px; margin: 10px` in source order via resolve_style
- expect top 10px too: the shorthand, applied later, overwrites the earlier longhand
   - Expected: result.margin_top.value > 9.9 and result.margin_top.value < 10.1 is true
   - Expected: result.margin_right.value > 9.9 and result.margin_right.value < 10.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a later shorthand overrides an earlier longhand on every side")
step("author `margin-top: 20px; margin: 10px` in source order via resolve_style")
val tree = _cascade_fixture_tree()
var rs: [CssStyleRule] = []
rs.push(_cascade_rule("div", "margin-top", "20px", false))
rs.push(_cascade_rule("div", "margin", "10px", false))
val result = resolve_style(tree, 1, computed_style_default(), _cascade_sheet(rs))

step("expect top 10px too: the shorthand, applied later, overwrites the earlier longhand")
expect(result.margin_top.value > 9.9 and result.margin_top.value < 10.1).to_equal(true)
expect(result.margin_right.value > 9.9 and result.margin_right.value < 10.1).to_equal(true)
```

</details>

### apply_declaration: border longhands

#### border-top-width/-style/-color set only the top side

- border-top-width/-style/-color set only the top side
- top side carries the new width/style/colour
   - Expected: s3.border_top_width.value > 2.9 and s3.border_top_width.value < 3.1 is true
   - Expected: s3.border_top_style equals `solid`
   - Expected: s3.border_top_color.r > 0.99 is true
- every other side is untouched (still the CSS initial: none, 0px)
   - Expected: s3.border_right_style equals `none`
   - Expected: s3.border_bottom_style equals `none`
   - Expected: s3.border_left_style equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border-top-width/-style/-color set only the top side")
val style = computed_style_default()
val s1 = apply_declaration(style, CssDeclaration(
    property: "border-top-width", value: "3px", important: false))
val s2 = apply_declaration(s1, CssDeclaration(
    property: "border-top-style", value: "solid", important: false))
val s3 = apply_declaration(s2, CssDeclaration(
    property: "border-top-color", value: "red", important: false))

step("top side carries the new width/style/colour")
expect(s3.border_top_width.value > 2.9 and s3.border_top_width.value < 3.1).to_equal(true)
expect(s3.border_top_style).to_equal("solid")
expect(s3.border_top_color.r > 0.99).to_equal(true)

step("every other side is untouched (still the CSS initial: none, 0px)")
expect(s3.border_right_style).to_equal("none")
expect(s3.border_bottom_style).to_equal("none")
expect(s3.border_left_style).to_equal("none")
```

</details>

#### an unrecognised border-style keyword leaves the current value alone

- an unrecognised border-style keyword leaves the current value alone
   - Expected: updated.border_top_style equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unrecognised border-style keyword leaves the current value alone")
val style = computed_style_default()
val updated = apply_declaration(style, CssDeclaration(
    property: "border-top-style", value: "not-a-real-style", important: false))
expect(updated.border_top_style).to_equal("none")
```

</details>

### resolve_style: border shorthand expansion

#### border: 2px solid red expands to all 4 sides via resolve_style

- border: 2px solid red expands to all 4 sides via resolve_style
- author `div { border: 2px solid red; }`
- all four sides resolved from the one shorthand declaration
   - Expected: result.border_top_style equals `solid`
   - Expected: result.border_right_style equals `solid`
   - Expected: result.border_bottom_style equals `solid`
   - Expected: result.border_left_style equals `solid`
   - Expected: result.border_top_width.value > 1.9 and result.border_top_width.value < 2.1 is true
   - Expected: result.border_left_color.r > 0.99 is true
   - Expected: result.border_left_color.g < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border: 2px solid red expands to all 4 sides via resolve_style")
step("author `div { border: 2px solid red; }`")
var rs: [CssStyleRule] = []
rs.push(_cascade_rule("div", "border", "2px solid red", false))
val sheet = _cascade_sheet(rs)
val tree = _cascade_fixture_tree()
val result = resolve_style(tree, 1, computed_style_default(), sheet)

step("all four sides resolved from the one shorthand declaration")
expect(result.border_top_style).to_equal("solid")
expect(result.border_right_style).to_equal("solid")
expect(result.border_bottom_style).to_equal("solid")
expect(result.border_left_style).to_equal("solid")
expect(result.border_top_width.value > 1.9 and result.border_top_width.value < 2.1).to_equal(true)
expect(result.border_left_color.r > 0.99).to_equal(true)
expect(result.border_left_color.g < 0.01).to_equal(true)
```

</details>

#### border-top: 1px dashed blue only expands the top side

- border-top: 1px dashed blue only expands the top side
- author `div { border-top: 1px dashed blue; }`
- top side takes the shorthand's values
   - Expected: result.border_top_style equals `dashed`
   - Expected: result.border_top_color.b > 0.99 is true
- other sides stay at the CSS initial (none)
   - Expected: result.border_right_style equals `none`
   - Expected: result.border_bottom_style equals `none`
   - Expected: result.border_left_style equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border-top: 1px dashed blue only expands the top side")
step("author `div { border-top: 1px dashed blue; }`")
var rs: [CssStyleRule] = []
rs.push(_cascade_rule("div", "border-top", "1px dashed blue", false))
val sheet = _cascade_sheet(rs)
val tree = _cascade_fixture_tree()
val result = resolve_style(tree, 1, computed_style_default(), sheet)

step("top side takes the shorthand's values")
expect(result.border_top_style).to_equal("dashed")
expect(result.border_top_color.b > 0.99).to_equal(true)

step("other sides stay at the CSS initial (none)")
expect(result.border_right_style).to_equal("none")
expect(result.border_bottom_style).to_equal("none")
expect(result.border_left_style).to_equal("none")
```

</details>

#### border is NOT an inherited property: a child does not pick up its parent's border

- border is NOT an inherited property: a child does not pick up its parent's border
   - Expected: result.border_top_style equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border is NOT an inherited property: a child does not pick up its parent's border")
val parent = apply_declaration(computed_style_default(), CssDeclaration(
    property: "border-top-style", value: "solid", important: false))
var rs: [CssStyleRule] = []
val sheet = _cascade_sheet(rs)
val tree = _cascade_fixture_tree()
val result = resolve_style(tree, 1, parent, sheet)
expect(result.border_top_style).to_equal("none")
```

</details>

### apply_declaration: box-shadow

#### box-shadow: 4px 6px black sets offset and colour and marks it set

- box-shadow: 4px 6px black sets offset and colour and marks it set
   - Expected: updated.box_shadow_set is true
   - Expected: updated.box_shadow_x.value > 3.9 and updated.box_shadow_x.value < 4.1 is true
   - Expected: updated.box_shadow_y.value > 5.9 and updated.box_shadow_y.value < 6.1 is true
   - Expected: updated.box_shadow_color.r < 0.01 is true
   - Expected: updated.box_shadow_color.a > 0.99 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("box-shadow: 4px 6px black sets offset and colour and marks it set")
val style = computed_style_default()
val updated = apply_declaration(style, CssDeclaration(
    property: "box-shadow", value: "4px 6px black", important: false))

expect(updated.box_shadow_set).to_equal(true)
expect(updated.box_shadow_x.value > 3.9 and updated.box_shadow_x.value < 4.1).to_equal(true)
expect(updated.box_shadow_y.value > 5.9 and updated.box_shadow_y.value < 6.1).to_equal(true)
expect(updated.box_shadow_color.r < 0.01).to_equal(true)
expect(updated.box_shadow_color.a > 0.99).to_equal(true)
```

</details>

#### box-shadow: 2px 2px 5px red (with a blur token) still resolves offset+colour

- box-shadow: 2px 2px 5px red (with a blur token) still resolves offset+colour
- blur radius is accepted syntactically but not modelled (see border_paint.spl header)
   - Expected: updated.box_shadow_set is true
   - Expected: updated.box_shadow_color.r > 0.99 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("box-shadow: 2px 2px 5px red (with a blur token) still resolves offset+colour")
val style = computed_style_default()
val updated = apply_declaration(style, CssDeclaration(
    property: "box-shadow", value: "2px 2px 5px red", important: false))

step("blur radius is accepted syntactically but not modelled (see border_paint.spl header)")
expect(updated.box_shadow_set).to_equal(true)
expect(updated.box_shadow_color.r > 0.99).to_equal(true)
```

</details>

#### box-shadow: none clears a previously-set shadow

- box-shadow: none clears a previously-set shadow
   - Expected: cleared.box_shadow_set is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("box-shadow: none clears a previously-set shadow")
val shadowed = apply_declaration(computed_style_default(), CssDeclaration(
    property: "box-shadow", value: "4px 6px black", important: false))
val cleared = apply_declaration(shadowed, CssDeclaration(
    property: "box-shadow", value: "none", important: false))
expect(cleared.box_shadow_set).to_equal(false)
```

</details>

#### an unparsable box-shadow (no colour) leaves the style unchanged

- an unparsable box-shadow (no colour) leaves the style unchanged
   - Expected: updated.box_shadow_set is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unparsable box-shadow (no colour) leaves the style unchanged")
val style = computed_style_default()
val updated = apply_declaration(style, CssDeclaration(
    property: "box-shadow", value: "4px 6px", important: false))
expect(updated.box_shadow_set).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
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

- Canonical SPipe generation for source `cac2c1c66394610596f9e84e88c3d728a8d7b55019f569f98bf868ba8fcce061`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cac2c1c66394610596f9e84e88c3d728a8d7b55019f569f98bf868ba8fcce061`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cac2c1c66394610596f9e84e88c3d728a8d7b55019f569f98bf868ba8fcce061`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/blink/style_cascade_spec.spl
mirror: doc/06_spec/unit/lib/blink/style_cascade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/blink/style_cascade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/style_cascade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/style_cascade_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '100px returns Length with value 100 and unit px' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/style_cascade_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty string returns Length(0, px)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/style_cascade_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a plain named colour' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
