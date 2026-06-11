# Html Compat Geometry Probe Specification

> <details>

<!-- sdn-diagram:id=html_compat_geometry_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_compat_geometry_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_compat_geometry_probe_spec -> std
html_compat_geometry_probe_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_compat_geometry_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Compat Geometry Probe Specification

## Scenarios

### wm_compare html_compat geometry probe

#### matches the focused fixture geometry set

-  check block and controls
-  check css and basic flex
-  check weighted flex
-  check wrapping and baseline


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_check_block_and_controls()
_check_css_and_basic_flex()
_check_weighted_flex()
_check_wrapping_and_baseline()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/html_compat_geometry_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare html_compat geometry probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
