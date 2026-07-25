# Shell Remote Window Specification

> 1. launcher init

<!-- sdn-diagram:id=shell_remote_window_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_remote_window_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_remote_window_spec -> std
shell_remote_window_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_remote_window_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Remote Window Specification

## Scenarios

### DesktopShell remote windows

#### resolves remote create-window identity from launcher process metadata

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: shell.compositor.window_owner_port(wid) equals `91`
   - Expected: shell.compositor.window_process_id(wid) equals `4101`
   - Expected: shell.compositor.window_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: shell.wm.window_owner_process_id(wid) equals `4101`
   - Expected: shell.wm.window_owner_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_app_id_for_pid(4101) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_window_count(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
expect(launcher_record_process(4101, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", 4101, 91))

expect(shell.compositor.window_count()).to_equal(1)
val ids = shell.compositor.windows_for_process(4101)
expect(ids.len()).to_equal(1)
val wid = ids[0]
expect(shell.compositor.window_owner_port(wid)).to_equal(91)
expect(shell.compositor.window_process_id(wid)).to_equal(4101)
expect(shell.compositor.window_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(shell.wm.window_owner_process_id(wid)).to_equal(4101)
expect(shell.wm.window_owner_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_app_id_for_pid(4101)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_window_count(0)).to_equal(1)
```

</details>

#### groups multiple remote windows under one manifest app_id and unwinds on destroy

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
4. shell apply wm action
   - Expected: shell.compositor.window_count() equals `2`
   - Expected: shell.compositor.window_count_for_process(5202) equals `2`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_count_for_process(5202) equals `2`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: launcher_get_process_window_count(0) equals `2`
   - Expected: ids.len() equals `2`
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `1`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `1`
   - Expected: launcher_get_process_window_count(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
expect(launcher_record_process(5202, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", 5202, 101))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", 5202, 102))

expect(shell.compositor.window_count()).to_equal(2)
expect(shell.compositor.window_count_for_process(5202)).to_equal(2)
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_count_for_process(5202)).to_equal(2)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(launcher_get_process_window_count(0)).to_equal(2)

val ids = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids.len()).to_equal(2)

shell.apply_wm_action(WmAction(
    kind: "destroy_window",
    window_id: ids[0],
    title: "",
    x: 0,
    y: 0,
    width: 0,
    height: 0,
    content: "",
    process_id: 0,
    app_id: "",
    owner_port: 0,
    src_port: 101
))

expect(shell.compositor.window_count()).to_equal(1)
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)
expect(launcher_get_process_window_count(0)).to_equal(1)
```

</details>

#### reaps crashed remote windows via the dead-process reconcile path

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: shell.wm.window_count_for_process(6303) equals `1`
4. launcher note task probe
   - Expected: launcher_get_process_state(0) equals `crashed`
   - Expected: launcher_get_running_process_count() equals `0`
5. shell reconcile dead process windows
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(6303) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
expect(launcher_record_process(6303, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", 6303, 201))
expect(shell.compositor.window_count()).to_equal(1)
expect(shell.wm.window_count_for_process(6303)).to_equal(1)

# Simulate an unexpected process death (nonzero exit).
launcher_note_task_probe(6303, false, 137)
expect(launcher_get_process_state(0)).to_equal("crashed")
expect(launcher_get_running_process_count()).to_equal(0)

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)
expect(shell.wm.window_count_for_process(6303)).to_equal(0)
```

</details>

#### reaps graceful exits on reconcile without misclassifying as crashes

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
   - Expected: shell.compositor.window_count() equals `1`
4. launcher note task probe
   - Expected: launcher_get_process_state(0) equals `exited`
5. shell reconcile dead process windows
   - Expected: shell.compositor.window_count() equals `0`
   - Expected: shell.wm.window_count_for_process(6404) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
expect(launcher_record_process(6404, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Hello World", 6404, 202))
expect(shell.compositor.window_count()).to_equal(1)

launcher_note_task_probe(6404, false, 0)
expect(launcher_get_process_state(0)).to_equal("exited")

shell.reconcile_dead_process_windows()
expect(shell.compositor.window_count()).to_equal(0)
expect(shell.wm.window_count_for_process(6404)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/shell_remote_window_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DesktopShell remote windows

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
