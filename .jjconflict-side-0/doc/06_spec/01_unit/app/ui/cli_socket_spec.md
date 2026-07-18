# Cli Socket Specification

> <details>

<!-- sdn-diagram:id=cli_socket_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_socket_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_socket_spec -> std
cli_socket_spec -> common
cli_socket_spec -> nogc_sync_mut
cli_socket_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_socket_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Socket Specification

## Scenarios

### process_command get_state

#### returns mode and focused fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sock_gs_root", "Hello")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "NORMAL"
expect response to_contain "mode"
```

</details>

#### reflects command mode after dispatch

1. var session = new session
2. session dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sock_gs_cmd_root", "Cmd")
val tree = UITree.new(root)
var session = new_session(tree)
session.dispatch(UIEvent.CommandMode)
val response = process_command(session, "{\"command\": \"get_state\"}")
expect response to_contain "COMMAND"
```

</details>

### process_command get_changes

#### returns empty changes for fresh session

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sock_gc_root", "Fresh")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"get_changes\"}")
expect response to_contain "changes"
```

</details>

#### returns changes after tree update

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
val root1 = column("sock_gc_upd", [
    text_widget("sock_gc_t1", "Old")
])
val tree1 = UITree.new(root1)
var session = new_session(tree1)
val root2 = column("sock_gc_upd", [
    text_widget("sock_gc_t1", "Old"),
    text_widget("sock_gc_t2", "New")
])
val tree2 = UITree.new(root2)
session.update_tree(tree2)
val response = process_command(session, "{\"command\": \"get_changes\", \"count\": 5}")
expect response to_contain "changes"
```

</details>

#### respects count parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sock_gc_cnt_root", "Count")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"get_changes\", \"count\": 3}")
expect response to_contain "changes"
```

</details>

### process_command ping

#### responds with pong

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sock_ping_root", "Ping")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"ping\"}")
expect response to_contain "pong"
```

</details>

### process_command errors

#### returns error for empty command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sock_err_empty_root", "Err")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "")
expect response to_contain "error"
```

</details>

#### returns error for unknown command

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sock_err_unk_root", "Err")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{\"command\": \"invalid_cmd\"}")
expect response to_contain "error"
expect response to_contain "unknown command"
```

</details>

#### returns error for empty JSON object

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sock_err_obj_root", "Err")
val tree = UITree.new(root)
val session = new_session(tree)
val response = process_command(session, "{}")
expect response to_contain "error"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/cli_socket_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- process_command get_state
- process_command get_changes
- process_command ping
- process_command errors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
