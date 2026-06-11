# Ui Shared Mdi Titlebar Widget Specification

> <details>

<!-- sdn-diagram:id=ui_shared_mdi_titlebar_widget_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_shared_mdi_titlebar_widget_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_shared_mdi_titlebar_widget_spec -> std
ui_shared_mdi_titlebar_widget_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_shared_mdi_titlebar_widget_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Shared Mdi Titlebar Widget Specification

## Scenarios

### shared MDI titlebar widget HTML

#### keeps Terminal titlebar button, body button, input, and CSS in the shared renderer source

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = shared_mdi_terminal_window_html()

expect(html).to_contain("simple-app-window")
expect(html).to_contain("simple-titlebar-label")
expect(html).to_contain("Terminal")
expect(html).to_contain("simple-titlebar-widgets")
expect(html).to_contain("data-simple-titlebar-widget=\"button\"")
expect(html).to_contain("data-action=\"mdi_terminal_action\"")
expect(html).to_contain("<button data-action=\"mdi_terminal_action\">Run</button>")
expect(html).to_contain("data-target-id=\"mdi_terminal_input\"")
expect(html).to_contain("value=\"ready\"")
expect(html).to_contain(".simple-titlebar-widget{background:rgb(18,58,52);border-color:rgb(52,211,153);color:rgb(236,254,255);}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui_shared_mdi_titlebar_widget_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared MDI titlebar widget HTML

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
