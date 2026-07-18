# Widget Coverage Specification

> 1. expect h len

<!-- sdn-diagram:id=widget_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_coverage_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Coverage Specification

## Scenarios

### Widget Coverage

#### parses the kitchen sink demo without error

1. expect h len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match result:
    case Ok(h):
        expect h.len() > 0 to_equal true
    case Err(e):
        expect e to_equal ""
```

</details>

#### contains panel widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "widget panel"
```

</details>

#### contains text widget with content

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "Kitchen Sink Demo"
```

</details>

#### contains button widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"action_btn\""
```

</details>

#### contains checkbox widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"option_a\""
```

</details>

#### contains input widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"search_input\""
```

</details>

#### contains textfield widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"edit_field\""
```

</details>

#### contains textarea widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"notes_area\""
```

</details>

#### contains dropdown widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"mode_dropdown\""
```

</details>

#### contains list widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "class=\"list\""
```

</details>

#### contains table widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"data_table\""
```

</details>

#### contains tree widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"file_tree\""
```

</details>

#### contains treenode widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"d_src\""
```

</details>

#### contains tabs widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"nav_tabs\""
```

</details>

#### contains menubar widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "menubar"
```

</details>

#### contains statusbar widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "statusbar"
```

</details>

#### contains progress widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "class=\"progress\""
```

</details>

#### contains image widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"app_icon\""
```

</details>

#### contains divider widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"sidebar_divider\""
```

</details>

#### contains tooltip widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"search_tip\""
```

</details>

#### contains dialog widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"modal_dialog\""
```

</details>

#### contains scroll widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect html to_contain "id=\"scroll_area\""
```

</details>

#### has all 21 widget types present

<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify key structural markers from each category are present
# Panels
val has_panel = html.contains("widget panel")
# Text content
val has_text = html.contains("Kitchen Sink Demo")
# Interactive controls
val has_button = html.contains("id=\"action_btn\"")
val has_checkbox = html.contains("id=\"option_a\"")
val has_input = html.contains("id=\"search_input\"")
val has_textfield = html.contains("id=\"edit_field\"")
val has_textarea = html.contains("id=\"notes_area\"")
val has_dropdown = html.contains("id=\"mode_dropdown\"")
# Collections
val has_list = html.contains("class=\"list\"")
val has_table = html.contains("id=\"data_table\"")
val has_tree = html.contains("id=\"file_tree\"")
val has_treenode = html.contains("id=\"d_src\"")
# Navigation
val has_tabs = html.contains("id=\"nav_tabs\"")
val has_menubar = html.contains("menubar")
val has_statusbar = html.contains("statusbar")
# Display
val has_progress = html.contains("class=\"progress\"")
val has_image = html.contains("id=\"app_icon\"")
val has_divider = html.contains("id=\"sidebar_divider\"")
val has_tooltip = html.contains("id=\"search_tip\"")
# Overlay / Container
val has_dialog = html.contains("id=\"modal_dialog\"")
val has_scroll = html.contains("id=\"scroll_area\"")

var count = 0
if has_panel: count = count + 1
if has_text: count = count + 1
if has_button: count = count + 1
if has_checkbox: count = count + 1
if has_input: count = count + 1
if has_textfield: count = count + 1
if has_textarea: count = count + 1
if has_dropdown: count = count + 1
if has_list: count = count + 1
if has_table: count = count + 1
if has_tree: count = count + 1
if has_treenode: count = count + 1
if has_tabs: count = count + 1
if has_menubar: count = count + 1
if has_statusbar: count = count + 1
if has_progress: count = count + 1
if has_image: count = count + 1
if has_divider: count = count + 1
if has_tooltip: count = count + 1
if has_dialog: count = count + 1
if has_scroll: count = count + 1

expect count to_equal 21
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/widget_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Widget Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
