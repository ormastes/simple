# Smux App Specification

> 1. smux reset for test

<!-- sdn-diagram:id=smux_app_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smux_app_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smux_app_spec -> std
smux_app_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smux_app_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smux App Specification

## Scenarios

### smux app

#### creates a session from the cli entry

1. smux reset for test
   - Expected: smux_run_cmd(["new", "dev"]) equals `0`
   - Expected: sessions.len() equals `1`
   - Expected: sessions[0].name equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
expect(smux_run_cmd(["new", "dev"])).to_equal(0)
val sessions = smux_list_sessions()
expect(sessions.len()).to_equal(1)
expect(sessions[0].name).to_equal("dev")
```

</details>

#### routes the full command to the named session only

1. Create two sessions and address the second by name
2. Capture both panes and require isolation plus complete argv joining
   - Expected: first capture is empty
   - Expected: second capture contains `echo hello world`

<details>
<summary>Executable SSpec</summary>

```simple
smux_reset_for_test()
expect(smux_run_cmd(["new", "first"])).to_equal(0)
expect(smux_run_cmd(["new", "second"])).to_equal(0)
expect(smux_run_cmd(["send", "second", "echo", "hello", "world"])).to_equal(0)
val sessions = smux_list_sessions()
val first_window = smux_list_windows(sessions[0].id)[0]
val second_window = smux_list_windows(sessions[1].id)[0]
val first_pane = smux_list_panes(sessions[0].id, first_window.id)[0]
val second_pane = smux_list_panes(sessions[1].id, second_window.id)[0]
val first_capture = smux_capture(sessions[0].id, first_window.id,
    first_pane.id, 100)
val second_capture = smux_capture(sessions[1].id, second_window.id,
    second_pane.id, 100)
expect(first_capture.content).to_equal("")
expect(second_capture.content).to_contain("echo hello world")
```

</details>

#### fails when a command names an unknown session

1. Reject every pane command before touching another session
   - Expected: send, capture, and split each return `1`

<details>
<summary>Executable SSpec</summary>

```simple
smux_reset_for_test()
expect(smux_run_cmd(["new", "known"])).to_equal(0)
expect(smux_run_cmd(["send", "missing", "echo", "unsafe"])).to_equal(1)
expect(smux_run_cmd(["capture", "missing"])).to_equal(1)
expect(smux_run_cmd(["split", "missing"])).to_equal(1)
```

</details>

#### sends and captures through the active pane commands

1. smux reset for test
   - Expected: smux_run_cmd(["new", "io"]) equals `0`
   - Expected: smux_run_cmd(["send", "io", "echo", "hi"]) equals `0`
   - Expected: smux_run_cmd(["capture", "io"]) equals `0`
   - Expected: pane.id != "" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
expect(smux_run_cmd(["new", "io"])).to_equal(0)
expect(smux_run_cmd(["send", "io", "echo", "hi"])).to_equal(0)
expect(smux_run_cmd(["capture", "io"])).to_equal(0)
val session = smux_list_sessions()[0]
val window = smux_list_windows(session.id)[0]
val pane = smux_list_panes(session.id, window.id)[0]
expect(pane.id != "").to_equal(true)
```

</details>

#### reports deferred features and exposes a filesystem app identity

1. smux reset for test
   - Expected: smux_run_cmd(["deferred", "copy-mode"]) equals `0`
   - Expected: smux_remote_launch_once(42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
expect(smux_run_cmd(["deferred", "copy-mode"])).to_equal(0)
expect(smux_help_text()).to_contain("smux deferred <feature>")
expect(smux_ready_marker(42)).to_contain(SMUX_APP_ID)
expect(smux_remote_launch_once(42)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/smux/smux_app_spec.spl` |
| Updated | 2026-09-02 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- smux app

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
