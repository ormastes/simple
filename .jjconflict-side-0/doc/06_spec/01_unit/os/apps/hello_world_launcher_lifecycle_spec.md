# Hello World Launcher Lifecycle Specification

> 1. launcher init

<!-- sdn-diagram:id=hello_world_launcher_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hello_world_launcher_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hello_world_launcher_lifecycle_spec -> std
hello_world_launcher_lifecycle_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hello_world_launcher_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hello World Launcher Lifecycle Specification

## Scenarios

### Hello World launcher lifecycle

#### exposes the built-in hello_world manifest identity

1. launcher init
   - Expected: launcher_get_app_path(0) equals `/sys/apps/hello_world.smf`
   - Expected: launcher_get_app_identity(0) equals `/sys/apps/hello_world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
expect(launcher_get_app_path(0)).to_equal("/sys/apps/hello_world.smf")
expect(launcher_get_app_identity(0)).to_equal("/sys/apps/hello_world")
```

</details>

#### joins launcher pid, shell WM ownership, and compositor on one window

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: shell.compositor.window_process_id(wid) equals `pid`
   - Expected: shell.compositor.window_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: shell.wm.window_owner_process_id(wid) equals `pid`
   - Expected: shell.wm.window_owner_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_window_count(0) equals `1`
   - Expected: launcher_get_app_launch_state(0) equals `running`
   - Expected: launcher_get_app_window_count(0) equals `1`
   - Expected: launcher_get_app_last_pid(0) equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 7101
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", pid, 301))

expect(shell.compositor.window_count()).to_equal(1)
val ids = shell.compositor.windows_for_process(pid)
expect(ids.len()).to_equal(1)
val wid = ids[0]
expect(shell.compositor.window_process_id(wid)).to_equal(pid)
expect(shell.compositor.window_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(shell.wm.window_owner_process_id(wid)).to_equal(pid)
expect(shell.wm.window_owner_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_window_count(0)).to_equal(1)
expect(launcher_get_app_launch_state(0)).to_equal("running")
expect(launcher_get_app_window_count(0)).to_equal(1)
expect(launcher_get_app_last_pid(0)).to_equal(pid)
```

</details>

#### handles graceful exit: window is reaped and app slot returns to exited

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
   - Expected: shell.compositor.window_count() equals `1`
4. launcher note task probe
   - Expected: launcher_get_process_state(0) equals `exited`
   - Expected: launcher_get_running_process_count() equals `0`
5. shell reconcile dead process windows
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(pid) equals `0`
   - Expected: launcher_get_app_launch_state(0) equals `exited`
   - Expected: launcher_get_app_exit_code(0) equals `0`
   - Expected: launcher_get_app_window_count(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 7202
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", pid, 302))
expect(shell.compositor.window_count()).to_equal(1)

# Graceful exit: exit code 0 → classified as "exited".
launcher_note_task_probe(pid, false, 0)
expect(launcher_get_process_state(0)).to_equal("exited")
expect(launcher_get_running_process_count()).to_equal(0)

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)
expect(shell.wm.window_count_for_process(pid)).to_equal(0)
expect(launcher_get_app_launch_state(0)).to_equal("exited")
expect(launcher_get_app_exit_code(0)).to_equal(0)
expect(launcher_get_app_window_count(0)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/hello_world_launcher_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Hello World launcher lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
