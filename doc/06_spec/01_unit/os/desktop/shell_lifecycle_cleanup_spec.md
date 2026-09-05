# Shell Lifecycle Cleanup Specification

> 1. launcher init

<!-- sdn-diagram:id=shell_lifecycle_cleanup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_lifecycle_cleanup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_lifecycle_cleanup_spec -> std
shell_lifecycle_cleanup_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_lifecycle_cleanup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Lifecycle Cleanup Specification

## Scenarios

### Shell lifecycle cleanup

#### graceful exit: windows purge and app slot reads exited

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
   - Expected: launcher_get_app_window_count(0) equals `0`
   - Expected: launcher_get_process_window_count(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 9101
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", pid, 501))
expect(shell.compositor.window_count()).to_equal(1)

launcher_note_task_probe(pid, false, 0)
expect(launcher_get_process_state(0)).to_equal("exited")
expect(launcher_get_running_process_count()).to_equal(0)

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)
expect(shell.wm.window_count_for_process(pid)).to_equal(0)
expect(launcher_get_app_launch_state(0)).to_equal("exited")
expect(launcher_get_app_window_count(0)).to_equal(0)
expect(launcher_get_process_window_count(0)).to_equal(0)
```

</details>

#### terminate from shell: classification stays terminated after reaper

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
4. shell apply wm action
   - Expected: shell.compositor.window_count() equals `2`
   - Expected: launcher_get_process_state(0) equals `terminating`
   - Expected: launcher_get_app_launch_state(5) equals `terminating`
5. launcher note task probe
   - Expected: launcher_get_process_state(0) equals `terminated`
   - Expected: launcher_get_app_launch_state(5) equals `terminated`
   - Expected: launcher_get_running_process_count() equals `0`
6. shell reconcile dead process windows
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(pid) equals `0`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `0`
   - Expected: launcher_get_app_window_count(5) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 9202
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 502))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 503))
expect(shell.compositor.window_count()).to_equal(2)

# Drive the real forced-terminate path:
#   1. launcher_terminate() flips the row to "terminating" and
#      dispatches posix_kill(SIGTERM). The kernel signal path
#      may be unavailable in unit mode, but the state flip
#      captures the operator intent so classification resolves
#      correctly when the reaper probes the death.
#   2. launcher_note_task_probe(alive=false) simulates the
#      kernel task having actually exited after the signal was
#      delivered. The reaper invokes this via
#      launcher_poll_processes() on a live kernel.
expect(launcher_terminate(pid)).to_be(true)
expect(launcher_get_process_state(0)).to_equal("terminating")
expect(launcher_get_app_launch_state(5)).to_equal("terminating")

launcher_note_task_probe(pid, false, 15)
expect(launcher_get_process_state(0)).to_equal("terminated")
expect(launcher_get_app_launch_state(5)).to_equal("terminated")
expect(launcher_get_running_process_count()).to_equal(0)

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)
expect(shell.wm.window_count_for_process(pid)).to_equal(0)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(0)
expect(launcher_get_app_window_count(5)).to_equal(0)
```

</details>

#### crash (nonzero exit): classification is crashed and windows purge

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
   - Expected: shell.compositor.window_count() equals `1`
4. launcher note task probe
   - Expected: launcher_get_process_state(0) equals `crashed`
   - Expected: launcher_get_running_process_count() equals `0`
5. shell reconcile dead process windows
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(pid) equals `0`
   - Expected: launcher_get_app_launch_state(0) equals `crashed`
   - Expected: launcher_get_app_window_count(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 9303
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", pid, 504))
expect(shell.compositor.window_count()).to_equal(1)

launcher_note_task_probe(pid, false, 139)
expect(launcher_get_process_state(0)).to_equal("crashed")
expect(launcher_get_running_process_count()).to_equal(0)

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)
expect(shell.wm.window_count_for_process(pid)).to_equal(0)
expect(launcher_get_app_launch_state(0)).to_equal("crashed")
expect(launcher_get_app_window_count(0)).to_equal(0)
```

</details>

#### idempotent reconcile: running a second pass after cleanup stays clean

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
4. launcher note task probe
5. shell reconcile dead process windows
   - Expected: shell.compositor.window_count() equals `0`
6. shell reconcile dead process windows
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(pid) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 9404
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", pid, 505))

launcher_note_task_probe(pid, false, 0)
shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)
expect(shell.wm.window_count_for_process(pid)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/shell_lifecycle_cleanup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Shell lifecycle cleanup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
