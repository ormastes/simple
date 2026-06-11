# Style Cascade Specification

> Tests for the CSS style cascade engine — parse_length_value, parse_color_value, parse_f64_value, apply_declaration, and resolve_style. Mirrors Blink's StyleResolver behaviour for a core set of CSS properties.

<!-- sdn-diagram:id=style_cascade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=style_cascade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

style_cascade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=style_cascade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Cascade Specification

Tests for the CSS style cascade engine — parse_length_value, parse_color_value, parse_f64_value, apply_declaration, and resolve_style. Mirrors Blink's StyleResolver behaviour for a core set of CSS properties.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/style_cascade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the CSS style cascade engine — parse_length_value, parse_color_value,
parse_f64_value, apply_declaration, and resolve_style. Mirrors Blink's
StyleResolver behaviour for a core set of CSS properties.

## Scenarios

### parse_length_value

#### 100px returns Length with value 100 and unit px

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_length_value("100px")
val value_ok = result.value > 99.9 && result.value < 100.1
val unit_ok  = result.unit == "px"
expect(value_ok).to_equal(true)
expect(unit_ok).to_equal(true)
```

</details>

#### empty string returns Length(0, px)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_length_value("")
val value_ok = result.value > -0.001 && result.value < 0.001
val unit_ok  = result.unit == "px"
expect(value_ok).to_equal(true)
expect(unit_ok).to_equal(true)
```

</details>

### parse_color_value

#### red returns opaque red

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_color_value("red")
val r_ok = c.r > 0.99
val g_ok = c.g < 0.01
val b_ok = c.b < 0.01
val a_ok = c.a > 0.99
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>

#### #ff0000 returns opaque red

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_color_value("#ff0000")
val r_ok = c.r > 0.99
val g_ok = c.g < 0.01
val b_ok = c.b < 0.01
val a_ok = c.a > 0.99
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>

### parse_f64_value

#### 0.5 returns 0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_f64_value("0.5")
val ok = result > 0.49 && result < 0.51
expect(ok).to_equal(true)
```

</details>

#### invalid string returns 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_f64_value("abc")
val ok = result > -0.001 && result < 0.001
expect(ok).to_equal(true)
```

</details>

### apply_declaration

#### color: blue sets style.color to blue

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = computed_style_default()
val decl = CssDeclaration(property: "unknown-property", value: "whatever", important: false)
val updated = apply_declaration(style, decl)
# display should remain the default (Inline)
val display_ok = updated.display == Display.Inline
expect(display_ok).to_equal(true)
```

</details>

### resolve_style

#### rule matching div sets its color

1. tree append child
2. decls push
3. rules push
   - Expected: r_ok is true
   - Expected: g_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val div_id = tree.create_element("div")
tree.append_child(tree.root_id, div_id)

val decl = CssDeclaration(property: "color", value: "red", important: false)
val decls = [CssDeclaration]()
decls.push(decl)
val rule = CssStyleRule(selector: "div", declarations: decls)
val rules = [CssStyleRule]()
rules.push(rule)
val sheet = CssStyleSheet(rules: rules, errors: [String]())

val parent_style = computed_style_default()
val result = resolve_style(tree, div_id, parent_style, sheet)
val r_ok = result.color.r > 0.99
val g_ok = result.color.g < 0.01
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
```

</details>

#### non-matching rule does not affect style

1. tree append child
2. decls push
3. rules push
   - Expected: r_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val span_id = tree.create_element("span")
tree.append_child(tree.root_id, span_id)

val decl = CssDeclaration(property: "color", value: "red", important: false)
val decls = [CssDeclaration]()
decls.push(decl)
val rule = CssStyleRule(selector: "div", declarations: decls)
val rules = [CssStyleRule]()
rules.push(rule)
val sheet = CssStyleSheet(rules: rules, errors: [String]())

val parent_style = computed_style_default()
val result = resolve_style(tree, span_id, parent_style, sheet)
# color should remain inherited from parent (default black: r=0)
val r_ok = result.color.r < 0.01
expect(r_ok).to_equal(true)
```

</details>

### resolve_style_with_state: :hover pseudo-class

#### .btn:hover { background-color: red } only applies when hovered

1. tree append child
2. tree set attribute
3. decls push
4. rules push
   - Expected: idle_not_red is true
   - Expected: hover_r_ok is true
   - Expected: hover_g_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = dom_tree_new()
val btn_id = tree.create_element("button")
tree.append_child(tree.root_id, btn_id)
tree.set_attribute(btn_id, "class", "btn")

val decl = CssDeclaration(property: "background-color", value: "red", important: false)
val decls = [CssDeclaration]()
decls.push(decl)
val rule = CssStyleRule(selector: ".btn:hover", declarations: decls)
val rules = [CssStyleRule]()
rules.push(rule)
val sheet = CssStyleSheet(rules: rules, errors: [String]())

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
