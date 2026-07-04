# Host Wm Runtime Loop Specification

> 1. host taskbar runtime reset

<!-- sdn-diagram:id=host_wm_runtime_loop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_wm_runtime_loop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_wm_runtime_loop_spec -> std
host_wm_runtime_loop_spec -> app
host_wm_runtime_loop_spec -> common
host_wm_runtime_loop_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_wm_runtime_loop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Wm Runtime Loop Specification

## Scenarios

### host web WM runtime loop wiring

#### routes host titlebar pointer steps through the shared WM bridge into session focus

1. host taskbar runtime reset

2. host taskbar runtime enable

3. var session =  session with two windows

4. Err
   - Expected: false is true

5. Ok
   - Expected: bridge.session.active_surface() equals `surf2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
host_taskbar_runtime_reset()
host_taskbar_runtime_enable("embedded", false)
var session = _session_with_two_windows()
val bridge = WmBridge.new(session)

val result = bridge.handle_host_wm_pointer_loop_step(90, 125, "left", "down", 800, 600)

match result:
    Err(_):
        expect(false).to_equal(true)
    Ok(marker):
        expect(marker).to_contain("[host-wm] loop-step command=window_drag_begin")
        expect(marker).to_contain("window=win2")
        expect(bridge.session.active_surface()).to_equal("surf2")
        expect(bridge.last_host_wm_loop_marker()).to_contain("target=surf2")
```

</details>

#### keeps unsupported host pointer gestures ignored without changing focus

1. host taskbar runtime reset

2. host taskbar runtime enable

3. var session =  session with two windows

4. Err
   - Expected: false is true

5. Ok
   - Expected: bridge.session.active_surface() equals `surf1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
host_taskbar_runtime_reset()
host_taskbar_runtime_enable("embedded", false)
var session = _session_with_two_windows()
val bridge = WmBridge.new(session)

val result = bridge.handle_host_wm_pointer_loop_step(90, 125, "right", "down", 800, 600)

match result:
    Err(_):
        expect(false).to_equal(true)
    Ok(marker):
        expect(marker).to_contain("command=ignored")
        expect(bridge.session.active_surface()).to_equal("surf1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/host_wm_runtime_loop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- host web WM runtime loop wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
