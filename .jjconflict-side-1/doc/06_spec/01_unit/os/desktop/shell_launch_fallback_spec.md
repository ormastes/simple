# Shell Launch Fallback Specification

> 1. launcher init

<!-- sdn-diagram:id=shell_launch_fallback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_launch_fallback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_launch_fallback_spec -> std
shell_launch_fallback_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_launch_fallback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Launch Fallback Specification

## Scenarios

### DesktopShell process launch materialization

#### materializes generic process windows using launcher process identity

1. launcher init
2. var shell =  make test shell
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: shell.compositor.window_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: shell.wm.window_owner_app_id(wid) equals `/sys/apps/hello_world`
   - Expected: launcher_get_process_window_count(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 7501
expect(launcher_record_process(pid, 0, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Hello World", pid)).to_be(true)

expect(shell.compositor.window_count()).to_equal(1)
val ids = shell.compositor.windows_for_process(pid)
expect(ids.len()).to_equal(1)
val wid = ids[0]
expect(shell.compositor.window_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(shell.wm.window_owner_app_id(wid)).to_equal("/sys/apps/hello_world")
expect(launcher_get_process_window_count(0)).to_equal(1)
```

</details>

#### keeps Browser Demo multi-window materialization while using launcher identity

1. launcher init
2. var shell =  make test shell
   - Expected: shell.compositor.window_count_for_process(pid) equals `2`
   - Expected: shell.compositor.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: shell.wm.window_count_for_app("/sys/apps/browser_demo") equals `2`
   - Expected: launcher_get_process_window_count(0) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 7502
expect(launcher_record_process(pid, 5, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Browser Demo", pid)).to_be(true)

expect(shell.compositor.window_count_for_process(pid)).to_equal(2)
expect(shell.compositor.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(shell.wm.window_count_for_app("/sys/apps/browser_demo")).to_equal(2)
expect(launcher_get_process_window_count(0)).to_equal(2)
```

</details>

#### materializes Simple Browser as a single filesystem-backed window

1. launcher init
2. var shell =  make test shell
   - Expected: shell.compositor.window_count() equals `1`
   - Expected: ids.len() equals `1`
   - Expected: wm_ids.len() equals `1`
   - Expected: wm_ids[0] equals `wid`
   - Expected: shell.compositor.window_process_id(wid) equals `pid`
   - Expected: shell.compositor.window_app_id(wid) equals `simple_browser_app_id()`
   - Expected: shell.wm.window_owner_process_id(wid) equals `pid`
   - Expected: shell.wm.window_owner_app_id(wid) equals `simple_browser_app_id()`
   - Expected: shell.compositor.window_title(wid) equals `Simple Browser`
   - Expected: launcher_get_process_window_count(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 7504
expect(launcher_record_process(pid, 7, "running", 0, 0, true)).to_be(true)

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Simple Browser", pid)).to_be(true)

expect(shell.compositor.window_count()).to_equal(1)
val ids = shell.compositor.windows_for_process(pid)
expect(ids.len()).to_equal(1)
val wm_ids = shell.wm.window_ids_for_process(pid)
expect(wm_ids.len()).to_equal(1)
val wid = ids[0]
expect(wm_ids[0]).to_equal(wid)
expect(shell.compositor.window_process_id(wid)).to_equal(pid)
expect(shell.compositor.window_app_id(wid)).to_equal(simple_browser_app_id())
expect(shell.wm.window_owner_process_id(wid)).to_equal(pid)
expect(shell.wm.window_owner_app_id(wid)).to_equal(simple_browser_app_id())
expect(shell.compositor.window_title(wid)).to_equal("Simple Browser")
expect(launcher_get_process_window_count(0)).to_equal(1)
```

</details>

#### refuses process materialization when pid is missing

1. launcher init
2. var shell =  make test shell
   - Expected: shell.compositor.window_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Hello World", 0)).to_be(false)
expect(shell.compositor.window_count()).to_equal(0)
```

</details>

#### refuses process materialization for unknown apps

1. launcher init
2. var shell =  make test shell
   - Expected: shell.compositor.window_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val pid: u64 = 7503

var shell = _make_test_shell()
expect(shell.materialize_process_launch("Unknown App", pid)).to_be(false)
expect(shell.compositor.window_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/shell_launch_fallback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DesktopShell process launch materialization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
