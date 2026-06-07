# Style Ui Authoring Specification

> 1. var styles = ui style surface

<!-- sdn-diagram:id=style_ui_authoring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=style_ui_authoring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

style_ui_authoring_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=style_ui_authoring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Ui Authoring Specification

## Scenarios

### style{} typed authoring surface

#### defines typed tokens and component rules

1. var styles = ui style surface
2. styles = ui style add token
3. styles = ui style add token
4. styles = ui style add token
5. styles = ui style add rule
   - Expected: ui_style_token_value(styles, "ui-accent") equals `#3366ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var styles = ui_style_surface("docs")
styles = ui_style_add_token(styles, ui_color_token("ui-accent", "#3366ff"))
styles = ui_style_add_token(styles, ui_length_token("space-md", "16px"))
styles = ui_style_add_token(styles, ui_text_token("font-body", "Inter"))
styles = ui_style_add_rule(styles, ui_component_layout_rule("button", "primary_button", "8px 12px", "1.4", "flex", "row", "", "8px"))

val css = ui_style_to_css(styles)

expect(ui_style_token_value(styles, "ui-accent")).to_equal("#3366ff")
expect(css).to_contain("--space-md: 16px;")
expect(css).to_contain(".primary_button")
expect(css).to_contain("margin: 8px 12px;")
expect(css).to_contain("line-height: 1.4;")
expect(css).to_contain("display: flex;")
expect(css).to_contain("flex-direction: row;")
expect(css).to_contain("gap: 8px;")
```

</details>

#### exports CSS into the existing SimpleTheme token resolver

1. var styles = ui style surface
2. styles = ui style add token
   - Expected: theme.resolve_token("ui-accent") equals `#3366ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var styles = ui_style_surface("docs")
styles = ui_style_add_token(styles, ui_color_token("ui-accent", "#3366ff"))

val theme = ui_style_to_theme(styles)

expect(theme.resolve_token("ui-accent")).to_equal("#3366ff")
```

</details>

### ui{} widget style bindings

#### binds widgets to typed style references

1. var styles = ui style surface
2. styles = ui style add rule
3. var ui = ui surface
4. ui = ui surface add widget
   - Expected: ui_surface_all_bindings_valid(styles, ui) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var styles = ui_style_surface("docs")
styles = ui_style_add_rule(styles, ui_component_layout_rule("section", "content_grid", "0", "1.5", "grid", "", "1fr 2fr", "12px"))

var ui = ui_surface("article")
val binding = ui_widget_binding("main_grid", "Panel", "content_grid")
ui = ui_surface_add_widget(ui, binding)

expect(ui_surface_all_bindings_valid(styles, ui)).to_equal(true)
expect(ui_surface_to_dom_attrs(binding)).to_contain("data-ui-style=\"content_grid\"")
expect(ui_surface_to_dom_attrs(binding)).to_contain("class=\"content_grid\"")
```

</details>

#### rejects unknown style references

1. var styles = ui style surface
2. styles = ui style add rule
3. var ui = ui surface
4. ui = ui surface add widget
   - Expected: ui_surface_all_bindings_valid(styles, ui) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var styles = ui_style_surface("docs")
styles = ui_style_add_rule(styles, ui_component_layout_rule("button", "primary_button", "4px", "1.2", "flex", "row", "", "4px"))

var ui = ui_surface("article")
ui = ui_surface_add_widget(ui, ui_widget_binding("missing", "Button", "danger_button"))

expect(ui_surface_all_bindings_valid(styles, ui)).to_equal(false)
```

</details>

### style{} browser compatibility CSS

#### covers margin, line-height, flex, and grid output selected by design

1. var styles = ui style surface
2. styles = ui style add rule
3. styles = ui style add rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var styles = ui_style_surface("compat")
styles = ui_style_add_rule(styles, ui_component_layout_rule("toolbar", "toolbar_row", "4px 8px", "1.25", "flex", "row", "", "6px"))
styles = ui_style_add_rule(styles, ui_component_layout_rule("content", "content_grid", "0", "1.5", "grid", "", "minmax(0, 1fr) 320px", "16px"))

val css = ui_style_to_css(styles)

expect(css).to_contain("margin: 4px 8px;")
expect(css).to_contain("line-height: 1.25;")
expect(css).to_contain("display: flex;")
expect(css).to_contain("display: grid;")
expect(css).to_contain("grid-template-columns: minmax(0, 1fr) 320px;")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/ui/style_ui_authoring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- style{} typed authoring surface
- ui{} widget style bindings
- style{} browser compatibility CSS

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
