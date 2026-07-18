# Dialog Specification

> <details>

<!-- sdn-diagram:id=dialog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dialog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dialog_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dialog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dialog Specification

## Scenarios

### Desktop Dialog API

#### creates DialogFilter struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = DialogFilter(name: "Images", patterns: ["*.png", "*.jpg"])
expect f.name == "Images"
```

</details>

#### creates DialogOptions struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = DialogOptions(title: "Open", default_path: "", filters: [], multiple: false)
expect opts.title == "Open"
expect opts.multiple == false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/dialog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop Dialog API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
