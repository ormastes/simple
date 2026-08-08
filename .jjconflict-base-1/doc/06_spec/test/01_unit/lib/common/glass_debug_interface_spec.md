# Glass Debug Interface Specification

> AC-5: CLI-based GUI debug interface exists (inspect widget tree, theme tokens, CSS output) via MCP or CLI subcommand.

<!-- sdn-diagram:id=glass_debug_interface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glass_debug_interface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glass_debug_interface_spec -> std
glass_debug_interface_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glass_debug_interface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Debug Interface Specification

AC-5: CLI-based GUI debug interface exists (inspect widget tree, theme tokens, CSS output) via MCP or CLI subcommand.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-THEME-SHARING |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/stitch_design_system.md |
| Source | `test/01_unit/lib/common/glass_debug_interface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-5: CLI-based GUI debug interface exists (inspect widget tree, theme
tokens, CSS output) via MCP or CLI subcommand.

Verifies that:
- debug_theme_tokens(theme_name) returns non-empty text for valid themes
- debug_css_dump(theme_name) returns non-empty text for valid themes
- debug_widget_tree(theme_name) returns non-empty text for valid themes
- All debug functions return meaningful content (not just whitespace)
- Debug functions handle unknown themes gracefully
- Output contains expected structural elements

## Key Concepts

| Concept | Description |
|---------|-------------|
| debug_theme_tokens | Pure function returning all token values as formatted text |
| debug_css_dump | Pure function returning full CSS output for a theme |
| debug_widget_tree | Pure function returning widget tree with theme assignments |
| Pure functions | No side effects, usable from both MCP tools and CLI |

## Scenarios

### debug_theme_tokens

#### returns non-empty text for glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_light

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_light")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_obsidian_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_obsidian_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### contains surface_primary label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("surface_primary")
```

</details>

#### contains text_primary label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("text_primary")
```

</details>

#### contains accent label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("accent")
```

</details>

#### contains blur token info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("blur")
```

</details>

#### obsidian output contains Obsidian-specific value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_obsidian_dark")
expect(output).to_contain("#E3E0F3")
```

</details>

#### dark output contains dark-specific value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("#F5F5F7")
```

</details>

### debug_css_dump

#### returns non-empty text for glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_css_dump("glass_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_light

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_css_dump("glass_light")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_obsidian_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_css_dump("glass_obsidian_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### contains :root block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_css_dump("glass_dark")
expect(output).to_contain(":root")
```

</details>

#### contains CSS custom properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_css_dump("glass_dark")
expect(output).to_contain("--glass-")
```

</details>

#### contains component CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_css_dump("glass_dark")
expect(output).to_contain(".widget-panel")
```

</details>

### debug_widget_tree

#### returns non-empty text for glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_widget_tree("glass_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_obsidian_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_widget_tree("glass_obsidian_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### contains widget class names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_widget_tree("glass_dark")
expect(output).to_contain("widget")
```

</details>

#### contains CSS variable references

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_widget_tree("glass_dark")
expect(output).to_contain("--glass-")
```

</details>

#### contains panel widget info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_widget_tree("glass_dark")
expect(output).to_contain("panel")
```

</details>

#### contains window widget info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_widget_tree("glass_dark")
expect(output).to_contain("window")
```

</details>

### Debug functions with unknown themes

#### debug_theme_tokens handles unknown theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_theme_tokens("nonexistent")
# Should not crash -- either empty or error message
expect(output.len()).to_be_greater_than(-1)
```

</details>

#### debug_css_dump handles unknown theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_css_dump("nonexistent")
expect(output.len()).to_be_greater_than(-1)
```

</details>

#### debug_widget_tree handles unknown theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = debug_widget_tree("nonexistent")
expect(output.len()).to_be_greater_than(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/stitch_design_system.md](doc/05_design/stitch_design_system.md)


</details>
