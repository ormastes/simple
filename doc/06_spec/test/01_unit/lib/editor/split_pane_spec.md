# Split Pane Specification

> <details>

<!-- sdn-diagram:id=split_pane_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=split_pane_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

split_pane_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=split_pane_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Split Pane Specification

## Scenarios

### SplitPaneLayout

#### creates layout with single root pane

- expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = split_pane_create()
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(1)
```

</details>

#### splits pane horizontally

- expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = split_pane_create()
val new_id = split_pane_split(layout, SplitDirection.Horizontal)
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(2)
```

</details>

#### splits pane vertically

- expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = split_pane_create()
val new_id = split_pane_split(layout, SplitDirection.Vertical)
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(2)
```

</details>

#### focus changes active pane

- split pane split
- split pane focus
- expect active to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = split_pane_create()
val panes_before = split_pane_list_panes(layout)
val first_id = panes_before[0]
split_pane_split(layout, SplitDirection.Horizontal)
split_pane_focus(layout, first_id)
val active = split_pane_active(layout)
expect active to_equal(first_id)
```

</details>

#### lists panes correctly after two splits

- split pane split
- split pane split
- expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = split_pane_create()
split_pane_split(layout, SplitDirection.Horizontal)
split_pane_split(layout, SplitDirection.Vertical)
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(3)
```

</details>

#### close pane returns to single

- split pane close
- expect count to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = split_pane_create()
val new_id = split_pane_split(layout, SplitDirection.Horizontal)
split_pane_close(layout, new_id)
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/split_pane_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SplitPaneLayout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
