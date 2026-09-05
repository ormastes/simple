# Custom Properties Wpt Specification

> 1. "div { --color: #dc2626; background-color: var

<!-- sdn-diagram:id=custom_properties_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_properties_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_properties_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_properties_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Properties Wpt Specification

## Scenarios

### WPT CSS custom properties

#### var() resolution

#### var() resolves custom property value

1. "div { --color: #dc2626; background-color: var


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    "div { --color: #dc2626; background-color: var(--color); width: 12px; height: 8px; }",
    "<div></div>",
    0xFFDC2626u32
)).to_equal(true)
```

</details>

#### var() with fallback when undefined

1. "div { background-color: var


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    "div { background-color: var(--undefined, #16a34a); width: 12px; height: 8px; }",
    "<div></div>",
    0xFF16A34Au32
)).to_equal(true)
```

</details>

#### custom property inherits to child

1. " parent { --color: #2563eb; }  child { background-color: var


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    ".parent { --color: #2563eb; } .child { background-color: var(--color); width: 12px; height: 8px; }",
    "<div class='parent'><div class='child'></div></div>",
    0xFF2563EBu32
)).to_equal(true)
```

</details>

#### var() nested fallback

1. "div { background-color: var


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    "div { background-color: var(--a, var(--b, #9333ea)); width: 12px; height: 8px; }",
    "<div></div>",
    0xFF9333EAu32
)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/custom_properties_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT CSS custom properties

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
