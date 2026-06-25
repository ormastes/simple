# Global Shortcut Specification

> <details>

<!-- sdn-diagram:id=global_shortcut_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=global_shortcut_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

global_shortcut_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=global_shortcut_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Global Shortcut Specification

## Scenarios

### Desktop Global Shortcut API

#### creates Shortcut struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Shortcut(modifiers: ["ctrl", "shift"], key: "p")
expect s.key == "p"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/global_shortcut_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop Global Shortcut API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
