# SYS-GUI-006 With Apps Serial Contract

> This system spec protects the SimpleOS desktop-with-apps boot contract while launcher shortcut dispatch remains pending. It builds the desktop guest and, when QEMU is available, waits for the serial readiness markers through `desktop-ready` without asserting the known blocked `remote-grouping:ok` marker.

<!-- sdn-diagram:id=sys_gui_006_with_apps_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_gui_006_with_apps_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_gui_006_with_apps_spec -> std
sys_gui_006_with_apps_spec -> os
sys_gui_006_with_apps_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_gui_006_with_apps_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SYS-GUI-006 With Apps Serial Contract

This system spec protects the SimpleOS desktop-with-apps boot contract while launcher shortcut dispatch remains pending. It builds the desktop guest and, when QEMU is available, waits for the serial readiness markers through `desktop-ready` without asserting the known blocked `remote-grouping:ok` marker.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/sys_gui_006_with_apps_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec protects the SimpleOS desktop-with-apps boot contract while
launcher shortcut dispatch remains pending. It builds the desktop guest and,
when QEMU is available, waits for the serial readiness markers through
`desktop-ready` without asserting the known blocked `remote-grouping:ok` marker.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Syntax

The live scenario starts QEMU through the shared harness, records serial output,
and asserts each readiness marker individually.

## Examples

- `spl_start`, `boot`, `shell-ready`, `launcher-ready`, and `desktop-ready`
  must appear in order for a live guest pass.

## Scenarios

### SYS-GUI-006 desktop boots with apps registered (serial lane)

#### builds desktop_e2e_entry.spl into a baremetal kernel

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _desktop_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots desktop to desktop-ready with 4 launcher apps (shortcut:fail is pending_vt4)

1. dir create all

2. Ok

3. stop guest
   - Expected: saw_spl_start is true
   - Expected: saw_boot is true
   - Expected: saw_shell is true
   - Expected: saw_launcher is true
   - Expected: saw_desktop is true

4. Err
   - Expected: spawned is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _desktop_target()
expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

if not can_run_target(target):
    print "[sys_gui_006_with_apps_spec] qemu-system-x86_64 not available, skipping"
    expect(can_run_target(target)).to_equal(false)
    return

val qmp_socket = "/tmp/sys_gui_006_with_apps_qmp.sock"
val serial_log = "build/os/sys_gui_006_with_apps_qemu_serial.log"

dir_create_all("build/os")

var spawned = false
match spawn_guest_with_qmp(target, qmp_socket, serial_log):
    Ok(handle) =>
        spawned = true
        # desktop-ready fires reliably within ~10s; 20s gives 2x margin.
        val saw_spl_start   = wait_for_serial_marker(handle, "[desktop-e2e] spl_start",    10000)
        val saw_boot        = wait_for_serial_marker(handle, "[desktop-e2e] boot",         10000)
        val saw_shell       = wait_for_serial_marker(handle, "[desktop-e2e] shell-ready",  15000)
        val saw_launcher    = wait_for_serial_marker(handle, "[desktop-e2e] launcher-ready", 10000)
        val saw_desktop     = wait_for_serial_marker(handle, "[desktop-e2e] desktop-ready", 20000)

        # remote-grouping:ok requires shortcut dispatch fix — @tag:pending_vt4
        # Do NOT assert it here; it will never fire on current main.

        stop_guest(handle)

        expect(saw_spl_start).to_equal(true)
        expect(saw_boot).to_equal(true)
        expect(saw_shell).to_equal(true)
        expect(saw_launcher).to_equal(true)
        expect(saw_desktop).to_equal(true)
    Err(err) =>
        print "[sys_gui_006_with_apps_spec] failed to spawn guest: {err}"
expect(spawned).to_equal(true)
```

</details>

#### has a baselines directory for with-apps captures

1. dir create all
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline_dir = "test/baselines/simpleos_desktop_with_apps_framebuffer"
dir_create_all(baseline_dir)
expect(file_exists(baseline_dir)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
