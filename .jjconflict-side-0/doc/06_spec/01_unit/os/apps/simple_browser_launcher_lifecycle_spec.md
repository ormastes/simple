# Simple Browser Launcher Lifecycle Specification

> 1. launcher init

<!-- sdn-diagram:id=simple_browser_launcher_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_browser_launcher_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_browser_launcher_lifecycle_spec -> std
simple_browser_launcher_lifecycle_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_browser_launcher_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Browser Launcher Lifecycle Specification

## Scenarios

### Simple Browser launcher lifecycle

#### exposes the built-in simple_browser manifest identity

1. launcher init
   - Expected: launcher_get_app_path(7) equals `/sys/apps/simple_browser.smf`
   - Expected: launcher_get_app_identity(7) equals `/sys/apps/simple_browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
expect(launcher_get_app_path(7)).to_equal("/sys/apps/simple_browser.smf")
expect(launcher_get_app_identity(7)).to_equal("/sys/apps/simple_browser")
```

</details>

#### joins launcher pid, shell WM ownership, and compositor on one browser window

1. launcher init
2. var shell =  make test shell
3. shell apply wm action
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: shell.compositor.window_process_id(wid) equals `pid`
   - Expected: shell.compositor.window_app_id(wid) equals `/sys/apps/simple_browser`
   - Expected: shell.wm.window_owner_process_id(wid) equals `pid`
   - Expected: shell.wm.window_owner_app_id(wid) equals `/sys/apps/simple_browser`
   - Expected: launcher_get_process_app_id_for_pid(pid) equals `/sys/apps/simple_browser`
   - Expected: launcher_get_process_window_count(0) equals `1`
   - Expected: launcher_get_app_launch_state(7) equals `running`
   - Expected: launcher_get_app_window_count(7) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 9105
expect(launcher_record_process(pid, 7, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
shell.apply_wm_action(_create_window_action("Simple Browser", pid, 501))

expect(shell.compositor.window_count()).to_equal(1)
val ids = shell.compositor.windows_for_process(pid)
expect(ids.len()).to_equal(1)
val wid = ids[0]
expect(shell.compositor.window_process_id(wid)).to_equal(pid)
expect(shell.compositor.window_app_id(wid)).to_equal("/sys/apps/simple_browser")
expect(shell.wm.window_owner_process_id(wid)).to_equal(pid)
expect(shell.wm.window_owner_app_id(wid)).to_equal("/sys/apps/simple_browser")
expect(launcher_get_process_app_id_for_pid(pid)).to_equal("/sys/apps/simple_browser")
expect(launcher_get_process_window_count(0)).to_equal(1)
expect(launcher_get_app_launch_state(7)).to_equal("running")
expect(launcher_get_app_window_count(7)).to_equal(1)
```

</details>

#### emits deterministic startup and render markers for about:network

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid: u64 = 9106
val wid: u64 = 77
expect(simple_browser_ready_marker(pid)).to_contain("app_id=/sys/apps/simple_browser")
expect(simple_browser_ready_marker(pid)).to_contain("page={simple_browser_start_page()}")
expect(simple_browser_window_marker(pid, wid)).to_contain("wid=77")
expect(simple_browser_render_marker(pid, wid)).to_contain("page={simple_browser_start_page()}")
expect(simple_browser_render_marker(pid, wid)).to_contain("renderer=simple_web")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/simple_browser_launcher_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Browser launcher lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
