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
| 3 | 3 | 0 | 0 |

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- smux app

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
