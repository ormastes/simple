# Ipc Surface Specification

> <details>

<!-- sdn-diagram:id=ipc_surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_surface_spec -> std
ipc_surface_spec -> common
ipc_surface_spec -> nogc_sync_mut
ipc_surface_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Surface Specification

## Scenarios

### IPC surface state

#### reports surface count in state response

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("ipc_surf_root", "Main")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "surface_count"
```

</details>

#### reflects multiple surfaces

1. var session = new session
2. session open surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("ipc_surf_multi_root", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val popup_root = text_widget("ipc_surf_popup_r", "Popup")
val popup_tree = UITree.new(popup_root)
session.open_surface("popup", popup_tree)
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "surface_count"
```

</details>

#### reports viewport in state response

1. var session = new session
2. session set viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("ipc_surf_vp_root", "VP")
val tree = UITree.new(root)
var session = new_session(tree)
session.set_viewport(120, 40, "cli")
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "120x40"
```

</details>

### IPC surface changes

#### captures changes from tree update

1. text widget
2. var session = new session
3. text widget
4. text widget
5. session update tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root1 = column("ipc_chg_root", [
    text_widget("ipc_chg_t1", "V1")
])
val tree1 = UITree.new(root1)
var session = new_session(tree1)
val root2 = column("ipc_chg_root", [
    text_widget("ipc_chg_t1", "V1"),
    text_widget("ipc_chg_t2", "V2")
])
val tree2 = UITree.new(root2)
session.update_tree(tree2)
val response = process_command(session, "{\"command\": \"get_changes\", \"count\": 10}")
expect response to_contain "changes"
```

</details>

### IPC subscribe command

#### returns initial state on subscribe

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("ipc_sub_root", "Sub")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"subscribe\"}")
expect response to_contain "mode"
expect response to_contain "NORMAL"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ipc_surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IPC surface state
- IPC surface changes
- IPC subscribe command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
