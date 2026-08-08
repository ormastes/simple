# Viewport Specification

> <details>

<!-- sdn-diagram:id=viewport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=viewport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

viewport_spec -> std
viewport_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=viewport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Viewport Specification

## Scenarios

### Viewport

#### creates default viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = default_viewport()
expect vp.width to_equal 80
expect vp.height to_equal 24
expect vp.active_backend to_equal "none"
```

</details>

#### creates custom viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(1920, 1080, "tauri")
expect vp.width to_equal 1920
expect vp.height to_equal 1080
expect vp.active_backend to_equal "tauri"
```

</details>

#### computes area

1. expect vp area


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(80, 24, "tui")
expect vp.area() to_equal 1920
```

</details>

#### detects active state

1. expect vp1 is active
2. expect vp2 is active


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp1 = default_viewport()
expect vp1.is_active() to_equal false
val vp2 = new_viewport(80, 24, "tui")
expect vp2.is_active() to_equal true
```

</details>

#### describes itself

1. expect vp describe


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(120, 40, "electron")
expect vp.describe() to_equal "120x40 (electron)"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/viewport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Viewport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
