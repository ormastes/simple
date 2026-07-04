# Window Scene Layout Key Specification

> <details>

<!-- sdn-diagram:id=window_scene_layout_key_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_scene_layout_key_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_scene_layout_key_spec -> std
window_scene_layout_key_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_scene_layout_key_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Layout Key Specification

## Scenarios

### shared WM scene layout key

#### keeps exact window-sensitive cache key format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = shared_wm_scene_layout_key(_scene(80))

expect(key).to_equal("w=800;h=600;backend=simple;count=2;surf1:surf1:10,40,300,200:z1:minfalse:focusfalse;surf2:surf2:80,40,300,200:z2:minfalse:focustrue")
```

</details>

#### changes when window geometry changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_wm_scene_layout_key(_scene(80))).to_contain("surf2:surf2:80,40,300,200")
expect(shared_wm_scene_layout_key(_scene(120))).to_contain("surf2:surf2:120,40,300,200")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_layout_key_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared WM scene layout key

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
