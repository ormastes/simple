# Tmux Session Model Specification

> <details>

<!-- sdn-diagram:id=tmux_session_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmux_session_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmux_session_model_spec -> std
tmux_session_model_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmux_session_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmux Session Model Specification

## Scenarios

### tmux session model

#### creates a session with one active shell pane

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = tmux_session("dev", "/bin/shell")

expect(session.name).to_equal("dev")
expect(session.windows.len()).to_equal(1)
expect(tmux_active_command(session)).to_equal("/bin/shell")
```

</details>

#### adds a new active window

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = tmux_add_window(tmux_session("dev", "/bin/shell"), "logs", "log")

expect(session.windows.len()).to_equal(2)
expect(session.active_window).to_equal(1)
expect(tmux_active_command(session)).to_equal("log")
```

</details>

#### splits the active pane

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = tmux_split_active_pane(tmux_session("dev", "/bin/shell"), "ssh host")

expect(session.windows[0].panes.len()).to_equal(2)
expect(session.windows[0].panes[1].command).to_equal("ssh host")
```

</details>

#### cycles active windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = tmux_add_window(tmux_session("dev", "/bin/shell"), "pkg", "pkg list")
val cycled = tmux_select_next_window(session)

expect(cycled.active_window).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/desktop/tmux_session_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tmux session model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
