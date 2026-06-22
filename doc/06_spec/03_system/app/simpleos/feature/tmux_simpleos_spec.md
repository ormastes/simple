# Tmux Simpleos Specification

> 1. smux reset for test

<!-- sdn-diagram:id=tmux_simpleos_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmux_simpleos_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmux_simpleos_spec -> std
tmux_simpleos_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmux_simpleos_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmux Simpleos Specification

## Scenarios

### tmux_simpleos feature spec

### REQ-001 session model

#### should create a persistent session with an initial window and pane

1. smux reset for test
   - Expected: session.name equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("dev")
expect(session.name).to_equal("dev")

val windows = smux_list_windows(session.id)
expect(windows.len()).to_be_greater_than(0)

val panes = smux_list_panes(session.id, windows[0].id)
expect(panes.len()).to_be_greater_than(0)
```

</details>

### REQ-002 pane-backed shells

#### should start panes on the native backend

1. smux reset for test
   - Expected: panes[0].backend_kind equals `MuxBackendKind.NativeShell`
   - Expected: panes[0].state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("shells")
val windows = smux_list_windows(session.id)
val panes = smux_list_panes(session.id, windows[0].id)

expect(panes[0].backend_kind).to_equal(MuxBackendKind.NativeShell)
expect(panes[0].state).to_equal("running")
```

</details>

### REQ-003 attach and detach

#### should detach a client without destroying the session

1. smux reset for test
   - Expected: smux_attach(session.id, "client-a", 120, 40).attached is true
   - Expected: smux_detach("client-a") is true
   - Expected: sessions[0].name equals `attach`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("attach")
expect(smux_attach(session.id, "client-a", 120, 40).attached).to_equal(true)
expect(smux_detach("client-a")).to_equal(true)

val sessions = smux_list_sessions()
expect(sessions[0].name).to_equal("attach")
```

</details>

### REQ-004 split and layout

#### should split the active pane and create a second pane

1. smux reset for test
   - Expected: smux_split_pane(session.id, window.id, first.id, "horizontal").is_ok() is true
   - Expected: panes.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("split")
val window = smux_list_windows(session.id)[0]
val first = smux_list_panes(session.id, window.id)[0]

expect(smux_split_pane(session.id, window.id, first.id, "horizontal").is_ok()).to_equal(true)

val panes = smux_list_panes(session.id, window.id)
expect(panes.len()).to_equal(2)
```

</details>

### REQ-005 input and output routing

#### should route sent text and commands to the selected pane

1. smux reset for test
   - Expected: smux_focus_pane(session.id, window.id, pane.id) is true
   - Expected: smux_send_text(session.id, window.id, pane.id, "echo hi") is true
   - Expected: smux_send_command(session.id, window.id, pane.id, "pwd") is true
   - Expected: metrics.send_text_count equals `1`
   - Expected: metrics.send_command_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("io")
val window = smux_list_windows(session.id)[0]
val pane = smux_list_panes(session.id, window.id)[0]

expect(smux_focus_pane(session.id, window.id, pane.id)).to_equal(true)
expect(smux_send_text(session.id, window.id, pane.id, "echo hi")).to_equal(true)
expect(smux_send_command(session.id, window.id, pane.id, "pwd")).to_equal(true)

val metrics = smux_metrics()
expect(metrics.send_text_count).to_equal(1)
expect(metrics.send_command_count).to_equal(1)
```

</details>

### REQ-006 state query API

#### should list sessions windows and panes with stable metadata

1. smux reset for test
   - Expected: sessions[0].name equals `query`
   - Expected: windows[0].session_id equals `session.id`
   - Expected: panes[0].window_id equals `windows[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("query")
val sessions = smux_list_sessions()
expect(sessions[0].name).to_equal("query")

val windows = smux_list_windows(session.id)
expect(windows[0].session_id).to_equal(session.id)

val panes = smux_list_panes(session.id, windows[0].id)
expect(panes[0].window_id).to_equal(windows[0].id)
```

</details>

### REQ-007 capture api

#### should capture pane output and preserve pane identity

1. smux reset for test
   - Expected: capture.pane_id equals `pane.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("capture")
val window = smux_list_windows(session.id)[0]
val pane = smux_list_panes(session.id, window.id)[0]

val capture = smux_capture(session.id, window.id, pane.id, 50)
expect(capture.pane_id).to_equal(pane.id)
expect(capture.rows).to_be_greater_than(0)
```

</details>

### REQ-008 compatibility facing api shape

#### should expose tmux-shaped session window pane operations over the native backend

1. smux reset for test
   - Expected: window.name equals `build`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("compat")
val window = smux_new_window(session.id, "build")
expect(window.name).to_equal("build")

val panes = smux_list_panes(session.id, window.id)
expect(panes.len()).to_be_greater_than(0)
```

</details>

### REQ-009 native first backend

#### should identify the backend as native rather than host tmux

1. smux reset for test
   - Expected: smux_backend_contract_name() equals `smux-native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
expect(smux_backend_contract_name()).to_equal("smux-native")
```

</details>

### REQ-010 backend swap readiness

#### should keep backend identity behind a named contract boundary

1. smux reset for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
expect(smux_backend_contract_name()).to_start_with("smux-")
```

</details>

### REQ-011 explicit non fatal failure handling

#### should return an error for an invalid pane target

1. smux reset for test
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("errors")
val window = smux_list_windows(session.id)[0]

val result = smux_resize(session.id, window.id, "missing-pane", 80, 24)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("pane")
```

</details>

#### should return an error when split target is invalid

1. smux reset for test
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("split-errors")
val window = smux_list_windows(session.id)[0]
val result = smux_split_pane(session.id, window.id, "missing-pane", "vertical")
expect(result.is_err()).to_equal(true)
```

</details>

### REQ-012 initial scope boundary

#### should expose deferred parity features explicitly

1. smux reset for test
   - Expected: smux_is_deferred_feature("copy-mode") is true
   - Expected: smux_is_deferred_feature("mouse") is true
   - Expected: smux_is_deferred_feature("key-table-compat") is true
   - Expected: smux_is_deferred_feature("tmux-conf") is true
   - Expected: smux_is_deferred_feature("control-mode") is true
   - Expected: smux_is_deferred_feature("split-pane") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
expect(smux_is_deferred_feature("copy-mode")).to_equal(true)
expect(smux_is_deferred_feature("mouse")).to_equal(true)
expect(smux_is_deferred_feature("key-table-compat")).to_equal(true)
expect(smux_is_deferred_feature("tmux-conf")).to_equal(true)
expect(smux_is_deferred_feature("control-mode")).to_equal(true)
expect(smux_is_deferred_feature("split-pane")).to_equal(false)
```

</details>

### NFR-007 observability

#### should expose observable startup and operation counters

1. smux reset for test
   - Expected: smux_resize(session.id, window.id, pane.id, 90, 25).is_ok() is true
   - Expected: metrics.resize_count equals `1`
   - Expected: metrics.capture_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("obs")
val window = smux_list_windows(session.id)[0]
val pane = smux_list_panes(session.id, window.id)[0]

expect(smux_resize(session.id, window.id, pane.id, 90, 25).is_ok()).to_equal(true)
val _capture = smux_capture(session.id, window.id, pane.id, 10)
val metrics = smux_metrics()

expect(metrics.startup_count).to_be_greater_than(0)
expect(metrics.last_startup_ns).to_be_greater_than(0u64)
expect(metrics.resize_count).to_equal(1)
expect(metrics.capture_count).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/tmux_simpleos_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tmux_simpleos feature spec
- REQ-001 session model
- REQ-002 pane-backed shells
- REQ-003 attach and detach
- REQ-004 split and layout
- REQ-005 input and output routing
- REQ-006 state query API
- REQ-007 capture api
- REQ-008 compatibility facing api shape
- REQ-009 native first backend
- REQ-010 backend swap readiness
- REQ-011 explicit non fatal failure handling
- REQ-012 initial scope boundary
- NFR-007 observability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
