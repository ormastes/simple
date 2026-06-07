# Tmux Facade Specification

> <details>

<!-- sdn-diagram:id=tmux_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmux_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmux_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmux_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmux Facade Specification

## Scenarios

### nogc_async_mut tmux facade

#### re-exports tmux record types without invoking shell-backed tmux operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = TmuxSession(name: "dev", windows: 2, attached: true, created: "now")
expect(session.name).to_equal("dev")
expect(session.windows).to_equal(2)
expect(session.attached).to_equal(true)

val window = TmuxWindow(session: "dev", index: 1, name: "edit", active: false, panes: 3)
expect(window.session).to_equal("dev")
expect(window.index).to_equal(1)
expect(window.panes).to_equal(3)

val pane = TmuxPane(session: "dev", window_index: 1, pane_index: 2, active: true, width: 120, height: 40, current_command: "bash", pid: 42)
expect(pane.active).to_equal(true)
expect(pane.width).to_equal(120)
expect(pane.current_command).to_equal("bash")

val capture = TmuxCaptureResult(content: "output", pane_id: "dev:1.2", rows: 40)
expect(capture.content).to_equal("output")
expect(capture.pane_id).to_equal("dev:1.2")
expect(capture.rows).to_equal(40)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/tmux/tmux_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut tmux facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
