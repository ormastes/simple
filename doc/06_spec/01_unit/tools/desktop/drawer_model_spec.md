# Drawer Model Specification

> <details>

<!-- sdn-diagram:id=drawer_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=drawer_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

drawer_model_spec -> std
drawer_model_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=drawer_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Drawer Model Specification

## Scenarios

### drawer model

#### contains primary GUI applications

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = primary_drawer_model()

expect(drawer_visible_items(model)[0].name).to_equal("Terminal")
expect(drawer_visible_items(model).len() >= 8).to_equal(true)
```

</details>

#### filters by app name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = drawer_set_query(primary_drawer_model(), "markdown")
val visible = drawer_visible_items(model)

expect(visible.len()).to_equal(1)
expect(visible[0].launch_path).to_equal("/sys/apps/editor")
```

</details>

#### filters by category

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = drawer_set_query(primary_drawer_model(), "games")
val visible = drawer_visible_items(model)

expect(visible[0].name).to_equal("Minesweeper")
```

</details>

#### selects a launch path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = drawer_select_next(primary_drawer_model())

expect(drawer_selected_launch_path(model)).to_equal("/sys/apps/shell")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/desktop/drawer_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- drawer model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
