# Window Scene Taskbar Guard Specification

> <details>

<!-- sdn-diagram:id=window_scene_taskbar_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_scene_taskbar_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_scene_taskbar_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_scene_taskbar_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Taskbar Guard Specification

## Scenarios

### window scene taskbar guard

#### guards taskbar pinned slot below zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/common/ui/window_scene.spl") ?? ""
expect(source).to_contain("if slot >= 0 and slot < taskbar.pinned.len():")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/ui/window_scene_taskbar_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- window scene taskbar guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
