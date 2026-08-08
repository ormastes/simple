# Widget Draw Cmds Specification

> <details>

<!-- sdn-diagram:id=widget_draw_cmds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_draw_cmds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_draw_cmds_spec -> std
widget_draw_cmds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_draw_cmds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Draw Cmds Specification

## Scenarios

### widget_draw_cmds non-empty — phone

#### cmds non-empty at 390x844

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = phone_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 390, 844)
expect(cmds.len() > 0).to_equal(true)
```

</details>

#### contains cmd for nav_home at 390x844

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = phone_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 390, 844)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
```

</details>

### widget_draw_cmds non-empty — tablet

#### cmds non-empty at 700x1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
expect(cmds.len() > 0).to_equal(true)
```

</details>

#### contains cmd for nav_home at 700x1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
```

</details>

### widget_draw_cmds non-empty — desktop

#### cmds non-empty at 1440x900

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = desktop_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 1440, 900)
expect(cmds.len() > 0).to_equal(true)
```

</details>

#### contains cmd for nav_home at 1440x900

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = desktop_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 1440, 900)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
```

</details>

### widget_draw_cmds phone bottom bar position

#### nav_home cmd y > 422 (below mid-screen, bottom bar)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = phone_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 390, 844)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
expect(cmd.y > 422).to_equal(true)
```

</details>

### widget_draw_cmds tablet rail position

#### nav_home cmd x < 100 (left rail)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
expect(cmd.x < 100).to_equal(true)
```

</details>

#### tablet_root_nav_rail container rect w < 120

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
val rail_cmd = find_rect_for(cmds, "tablet_root_nav_rail")
expect(rail_cmd != nil).to_equal(true)
expect(rail_cmd.w < 120).to_equal(true)
```

</details>

### widget_draw_cmds desktop sidebar width

#### desktop_root_nav_sidebar container rect w >= 200

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = desktop_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 1440, 900)
val sidebar_cmd = find_rect_for(cmds, "desktop_root_nav_sidebar")
expect(sidebar_cmd != nil).to_equal(true)
expect(sidebar_cmd.w >= 200).to_equal(true)
```

</details>

### widget_draw_cmds nav_pattern_probe labels

#### phone probe label == bottom

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = phone_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 390, 844)
val probe = find_probe(cmds)
expect(probe != nil).to_equal(true)
expect(probe.label).to_equal("bottom")
```

</details>

#### tablet probe label == rail

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
val probe = find_probe(cmds)
expect(probe != nil).to_equal(true)
expect(probe.label).to_equal("rail")
```

</details>

#### desktop probe label == sidebar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = desktop_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 1440, 900)
val probe = find_probe(cmds)
expect(probe != nil).to_equal(true)
expect(probe.label).to_equal("sidebar")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_draw_cmds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- widget_draw_cmds non-empty — phone
- widget_draw_cmds non-empty — tablet
- widget_draw_cmds non-empty — desktop
- widget_draw_cmds phone bottom bar position
- widget_draw_cmds tablet rail position
- widget_draw_cmds desktop sidebar width
- widget_draw_cmds nav_pattern_probe labels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
