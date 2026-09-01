# Scrollbar Wpt Specification

> <details>

<!-- sdn-diagram:id=scrollbar_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scrollbar_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scrollbar_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scrollbar_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scrollbar Wpt Specification

## Scenarios

### WPT-derived CSS scrollbar subset

#### CSS scrollbar pure function coverage

#### scrollbar renders track when content overflows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
expect(cmds.len() >= 1).to_equal(true)
```

</details>

#### scrollbar thumb proportional to viewport content ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# height=400, content_height=800, ratio=0.5, thumb_h = 400 * 0.5 = 200 (above 16 floor)
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
expect(cmds.len() >= 2).to_equal(true)
val thumb = cmds[1]
expect(approx_i32(thumb.height, 200)).to_equal(true)
```

</details>

#### no thumb when content fits within viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# content_height <= height, so only the track command is generated
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 300.0, 0.0)
expect(cmds.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/scrollbar_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived CSS scrollbar subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
