# Demo Render Specification

> <details>

<!-- sdn-diagram:id=demo_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=demo_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

demo_render_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=demo_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Demo Render Specification

## Scenarios

### Demo UI Rendering

#### renders demo_basics.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_basics.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Basic Widgets Demo"
        expect html to_contain "Hello, Simple UI!"
        expect html to_contain "Welcome"
        expect html to_contain "Text Variants"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_controls.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_controls.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Interactive Controls Demo"
        expect html to_contain "Buttons"
        expect html to_contain "Checkboxes"
        expect html to_contain "Dropdown"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_forms.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_forms.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Form Inputs Demo"
        expect html to_contain "Text Inputs"
        expect html to_contain "Validation States"
        expect html to_contain "Text Areas"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_collections.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_collections.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Collections Demo"
        expect html to_contain "List"
        expect html to_contain "Table"
        expect html to_contain "File Browser"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_navigation.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_navigation.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Navigation Demo"
        expect html to_contain "menubar"
        expect html to_contain "Dashboard"
        expect html to_contain "Quick Stats"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_display.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_display.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Display Widgets Demo"
        expect html to_contain "progress"
        expect html to_contain "Progress Bars"
        expect html to_contain "Tooltip Example"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_layouts.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_layouts.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Layout Demo"
        expect html to_contain "hbox"
        expect html to_contain "Grid Layout"
        expect html to_contain "Deep Nesting"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_overlays.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_overlays.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Overlays Demo"
        expect html to_contain "Scroll Container"
        expect html to_contain "Log entry 1"
        expect html to_contain "Confirm Action"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_themes.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_themes.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Theme Showcase"
        expect html to_contain "Navigation"
        expect html to_contain "Widget Gallery"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_kitchen_sink.ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_file("examples/06_io/ui/demo_kitchen_sink.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Kitchen Sink"
        expect html to_contain "Sidebar"
        expect html to_contain "Main Content"
        expect html to_contain "Kitchen Sink Demo"
    case Err(msg):
        expect false to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/demo_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Demo UI Rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
