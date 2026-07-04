# Shell Wm Runtime Loop Specification

> 1. launcher init

<!-- sdn-diagram:id=shell_wm_runtime_loop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_wm_runtime_loop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_wm_runtime_loop_spec -> std
shell_wm_runtime_loop_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_wm_runtime_loop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Wm Runtime Loop Specification

## Scenarios

### DesktopShell live WM runtime loop wiring

#### consumes pending compositor pointer steps through the SimpleOS WM bridge

1. launcher init
2. var shell =  make test shell
3. shell compositor set window identity
4. shell compositor set window identity
5. shell compositor note pending wm pointer step
6. shell handle pending wm pointer step
   - Expected: shell.compositor.has_pending_wm_pointer_step() is false
   - Expected: shell.wm_runtime_state.focused_window_id equals `{second}`
   - Expected: shell.wm_runtime_state.dragging_surface_id equals `{second}`
   - Expected: shell.compositor.dragging is true
   - Expected: shell.compositor.drag_window_id equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
var shell = _make_test_shell()
val first = shell.compositor.create_window("One", 10, 40, 300, 200)
val second = shell.compositor.create_window("Two", 80, 120, 300, 200)
shell.compositor.set_window_identity(first, 42, "demo.one")
shell.compositor.set_window_identity(second, 43, "demo.two")

shell.compositor.note_pending_wm_pointer_step(90, 125, "left", "down")
shell.handle_pending_wm_pointer_step()

expect(shell.compositor.has_pending_wm_pointer_step()).to_equal(false)
expect(shell.last_wm_loop_marker).to_contain("[simpleos-wm] loop-step command=window_drag_begin")
expect(shell.last_wm_loop_marker).to_contain("window={second}")
expect(shell.wm_runtime_state.focused_window_id).to_equal("{second}")
expect(shell.wm_runtime_state.dragging_surface_id).to_equal("{second}")
expect(shell.compositor.dragging).to_equal(true)
expect(shell.compositor.drag_window_id).to_equal(second)
```

</details>

#### routes live taskbar running-window clicks through shared focus state

1. launcher init
2. var shell =  make test shell
3. shell compositor set window identity
4. shell compositor set window identity
   - Expected: shell.wm_runtime_state.focused_window_id equals `{second}`
   - Expected: shell.compositor.surfaces[shell.compositor.surfaces.len() - 1].id equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
var shell = _make_test_shell()
val first = shell.compositor.create_window("One", 10, 40, 300, 200)
val second = shell.compositor.create_window("Two", 80, 120, 300, 200)
shell.compositor.set_window_identity(first, 42, "demo.one")
shell.compositor.set_window_identity(second, 43, "demo.two")

val marker = shell.handle_wm_pointer_event_loop_step(360, 575, "left", "down")

expect(marker).to_contain("command=window_focus")
expect(shell.wm_runtime_state.focused_window_id).to_equal("{second}")
expect(shell.compositor.surfaces[shell.compositor.surfaces.len() - 1].id).to_equal(second)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/shell_wm_runtime_loop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DesktopShell live WM runtime loop wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
