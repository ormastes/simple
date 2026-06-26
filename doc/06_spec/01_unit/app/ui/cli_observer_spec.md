# Cli Observer Specification

> 1. text widget

<!-- sdn-diagram:id=cli_observer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_observer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_observer_spec -> std
cli_observer_spec -> common
cli_observer_spec -> nogc_sync_mut
cli_observer_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_observer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Observer Specification

## Scenarios

### CLIObserver render_summary

#### includes mode and focused widget

1. text widget
2. expect summary to contain "STATE


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("cli_obs_root1", [
    text_widget("cli_obs_t1", "Hello")
])
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val summary = observer.render_summary()
expect summary to_contain "NORMAL"
expect summary to_contain "STATE (observer)"
```

</details>

#### includes viewport description

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("cli_obs_vp_root", "VP")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val summary = observer.render_summary()
expect summary to_contain "80x24"
```

</details>

#### lists surfaces

1. var session = new session
2. session open surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("cli_obs_surf_root", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val popup_root = text_widget("cli_obs_popup_r", "Popup")
val popup_tree = UITree.new(popup_root)
session.open_surface("popup", popup_tree)
val observer = CLIObserver.new(session)
val summary = observer.render_summary()
expect summary to_contain "main"
expect summary to_contain "popup"
```

</details>

### CLIObserver render_changes

#### shows no recent changes for fresh session

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("cli_obs_chg_root", "Fresh")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val output = observer.render_changes(5)
expect output to_contain "No recent changes"
```

</details>

#### shows changes after tree update

1. text widget
2. var session = new session
3. text widget
4. text widget
5. session update tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root1 = column("cli_obs_chg_upd", [
    text_widget("cli_obs_chg_t1", "Old")
])
val tree1 = UITree.new(root1)
var session = new_session(tree1)
val root2 = column("cli_obs_chg_upd", [
    text_widget("cli_obs_chg_t1", "Old"),
    text_widget("cli_obs_chg_t2", "New")
])
val tree2 = UITree.new(root2)
session.update_tree(tree2)
val observer = CLIObserver.new(session)
val output = observer.render_changes(10)
expect output to_contain "Recent changes"
```

</details>

### CLIObserver render_adaptive

#### renders tiny mode for small line budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("cli_obs_ada_tiny", "Tiny")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new_with_lines(session, 3)
val output = observer.render_adaptive()
expect output to_contain "mode:"
expect output to_contain "NORMAL"
```

</details>

#### renders medium mode for mid-range budget

1. expect output to contain "STATE


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("cli_obs_ada_mid", "Mid")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new_with_lines(session, 8)
val output = observer.render_adaptive()
expect output to_contain "STATE (observer)"
```

</details>

#### renders full mode for large budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("cli_obs_ada_full", "Full")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new_with_lines(session, 30)
val output = observer.render_adaptive()
expect output to_contain "surfaces"
```

</details>

### CLIObserver render_tree_outline

#### renders root node

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("cli_obs_tree_root", "Root")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val outline = observer.render_tree_outline()
expect outline to_contain "cli_obs_tree_root"
```

</details>

#### renders nested children with indentation

1. text widget
2. text widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("cli_obs_tree_nest", [
    text_widget("cli_obs_tree_c1", "Child1"),
    text_widget("cli_obs_tree_c2", "Child2")
])
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val outline = observer.render_tree_outline()
expect outline to_contain "cli_obs_tree_nest"
expect outline to_contain "cli_obs_tree_c1"
expect outline to_contain "cli_obs_tree_c2"
```

</details>

### render_node_outline

#### indents based on depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = text_widget("cli_rno_node", "Test")
val output = render_node_outline(node, 2)
expect output to_start_with "    "
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/cli_observer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CLIObserver render_summary
- CLIObserver render_changes
- CLIObserver render_adaptive
- CLIObserver render_tree_outline
- render_node_outline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
