# Ui Platform Facade Specification

> <details>

<!-- sdn-diagram:id=ui_platform_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_platform_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_platform_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_platform_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Platform Facade Specification

## Scenarios

### nogc_async_mut ui platform facade

#### re-exports platform material CSS helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mat = PlatformMaterial(
    shell_material: "mica",
    transient_material: "acrylic",
    title_bar_style: "hidden",
    supports_blur: true,
    supports_vibrancy: false
)
val css = platform_material_to_css(mat)
expect(css.contains("--shell-material: mica;")).to_equal(true)
expect(css.contains("--transient-material: acrylic;")).to_equal(true)
expect(css.contains("--supports-blur: 1;")).to_equal(true)
expect(css.contains("--supports-vibrancy: 0;")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/ui/ui_platform_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut ui platform facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
