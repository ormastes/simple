# Tmp Test66 Specification

> <details>

<!-- sdn-diagram:id=tmp_test66_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_test66_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_test66_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_test66_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Test66 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### resolves background shorthand currentColor from the computed text color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; color: #345678; background: currentColor no-repeat'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF345678u32)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_test66_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserRenderer HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
