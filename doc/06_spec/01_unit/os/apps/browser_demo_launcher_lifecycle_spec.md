# Browser Demo Launcher Lifecycle Specification

> 1. launcher init

<!-- sdn-diagram:id=browser_demo_launcher_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_demo_launcher_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_demo_launcher_lifecycle_spec -> std
browser_demo_launcher_lifecycle_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_demo_launcher_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Demo Launcher Lifecycle Specification

## Scenarios

### Browser Demo launcher lifecycle

#### exposes the built-in browser_demo manifest identity

1. launcher init
   - Expected: launcher_get_app_path(5) equals `/sys/apps/browser_demo.smf`
   - Expected: launcher_get_app_identity(5) equals `/sys/apps/browser_demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
expect(launcher_get_app_path(5)).to_equal("/sys/apps/browser_demo.smf")
expect(launcher_get_app_identity(5)).to_equal("/sys/apps/browser_demo")
```

</details>

#### groups two remote windows under one launcher-owned app_id

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
4. shell apply wm action
   - Expected: shell.compositor.window_count() equals `2`
   - Expected: shell.compositor.window_count_for_process(pid) equals `2`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_count_for_process(pid) equals `2`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/browser_demo`
   - Expected: launcher_get_process_window_count(0) equals `2`
   - Expected: launcher_get_app_window_count(5) equals `2`
   - Expected: launcher_get_app_launch_state(5) equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 8301
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 401))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 402))

expect(shell.compositor.window_count()).to_equal(2)
expect(shell.compositor.window_count_for_process(pid)).to_equal(2)
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_count_for_process(pid)).to_equal(2)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/browser_demo")
expect(launcher_get_process_window_count(0)).to_equal(2)
expect(launcher_get_app_window_count(5)).to_equal(2)
expect(launcher_get_app_launch_state(5)).to_equal("running")
```

</details>

#### keeps grouping stable after a title change on one window

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
4. shell apply wm action
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: ids_before.len() equals `2`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_owner_app_id(first_wid) equals `/sys/apps/browser_demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 8402
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 411))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 412))
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)

val ids_before = shell.compositor.windows_for_app("/sys/apps/browser_demo")
expect(ids_before.len()).to_equal(2)
val first_wid = ids_before[0]

shell.apply_wm_action(WmAction(
    kind: "update_title",
    window_id: first_wid,
    title: "Browser Demo — new-tab.simple",
    x: 0,
    y: 0,
    width: 0,
    height: 0,
    content: "",
    process_id: 0,
    app_id: "",
    owner_port: 0,
    src_port: 411
))

expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_owner_app_id(first_wid)).to_equal("/sys/apps/browser_demo")
```

</details>

#### destroys one window without breaking the other window's ownership

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
4. shell apply wm action
   - Expected: ids.len() equals `2`
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `1`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `1`
   - Expected: launcher_get_process_window_count(0) equals `1`
   - Expected: launcher_get_app_window_count(5) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 8503
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Browser Demo", pid, 421))
shell.apply_wm_action(_create_window_action("Browser Demo Inspector", pid, 422))
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
    src_port: 421
))

expect(shell.compositor.window_count()).to_equal(1)
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(1)
expect(launcher_get_process_window_count(0)).to_equal(1)
expect(launcher_get_app_window_count(5)).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/browser_demo_launcher_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser Demo launcher lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
