# Sticky Wpt Specification

> <details>

<!-- sdn-diagram:id=sticky_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sticky_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sticky_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sticky_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sticky Wpt Specification

## Scenarios

### WPT-derived CSS sticky positioning subset

#### CSS position sticky rendering coverage

#### position sticky element renders at scroll-adjusted position

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = ".sticky { position: sticky; top: 0; width: 20px; height: 10px; background-color: #2563eb; }"
val body = "<div class='sticky'></div>"
expect(_renders_color(style, body, 0xFF2563EBu32)).to_equal(true)
```

</details>

#### sticky element stays visible within containing block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = ".sticky { position: sticky; top: 5px; width: 20px; height: 10px; background-color: #16a34a; }"
val body = "<div class='sticky'></div>"
expect(_renders_color(style, body, 0xFF16A34Au32)).to_equal(true)
```

</details>

#### sticky element does not affect sibling non-sticky elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = ".sticky { position: sticky; top: 0; width: 10px; height: 8px; background-color: #dc2626; } .sibling { width: 10px; height: 8px; background-color: #16a34a; }"
val body = "<div class='sticky'></div><div class='sibling'></div>"
expect(_renders_color(style, body, 0xFF16A34Au32)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/sticky_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived CSS sticky positioning subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
