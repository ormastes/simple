# Tray Specification

> <details>

<!-- sdn-diagram:id=tray_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tray_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tray_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tray_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tray Specification

## Scenarios

### Desktop System Tray API

#### creates TrayMenuItem struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = TrayMenuItem(label: "Quit", action_id: "quit", checked: false, separator: false)
expect item.label == "Quit"
expect item.action_id == "quit"
```

</details>

#### creates TrayConfig struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TrayConfig(tooltip: "My App", icon_path: "/icon.png", menu_items: [])
expect config.tooltip == "My App"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/tray_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop System Tray API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
