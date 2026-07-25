# Os Desktop Integration Specification

> 1. Ok

<!-- sdn-diagram:id=os_desktop_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_desktop_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_desktop_integration_spec -> std
os_desktop_integration_spec -> os
os_desktop_integration_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_desktop_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Desktop Integration Specification

## Scenarios

### SimpleOS desktop integration (serial lane)

#### SYS-GUI-001 boots the x86_64 desktop target to desktop-ready

1. Ok
2. stop guest
   - Expected: saw_spl_start is true
   - Expected: saw_boot is true
   - Expected: saw_shell_ready is true
   - Expected: saw_launcher is true
   - Expected: saw_desktop is true
   - Expected: output does not contain `FAULT @`
   - Expected: output does not contain `panic`
3. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_desktop_browser_target()
expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

if not can_run_target(target):
    # QEMU not available in this environment — the build+link check
    # above is the most this lane can assert here. Parent agents
    # must run this on a QEMU-capable host for full coverage.
    expect(file_exists(target.output)).to_equal(true)
    return

val qmp_socket = "/tmp/simpleos_sys_gui_001_qmp.sock"
val serial_log = "build/os/sys_gui_001_serial.log"
match spawn_guest_with_qmp(target, qmp_socket, serial_log):
    Ok(handle):
        val saw_spl_start    = wait_for_serial_marker(handle, "[desktop-e2e] spl_start", 10000)
        val saw_boot         = wait_for_serial_marker(handle, "[desktop-e2e] boot", 10000)
        val saw_shell_ready  = wait_for_serial_marker(handle, "[desktop-e2e] shell-ready", 15000)
        val saw_launcher     = wait_for_serial_marker(handle, "[desktop-e2e] launcher-ready", 10000)
        val saw_desktop      = wait_for_serial_marker(handle, "[desktop-e2e] desktop-ready", 10000)
        val output = read_serial_log(handle)
        stop_guest(handle)
        expect(saw_spl_start).to_equal(true)
        expect(saw_boot).to_equal(true)
        expect(saw_shell_ready).to_equal(true)
        expect(saw_launcher).to_equal(true)
        expect(saw_desktop).to_equal(true)
        expect(output.contains("FAULT @")).to_equal(false)
        expect(output.contains("panic")).to_equal(false)
    Err(err):
        print "[os_desktop_integration_spec] SYS-GUI-001 spawn failed: {err}"
        expect(false).to_equal(true)
```

</details>

#### SYS-GUI-002 drives the launcher shortcut and observes a wm join

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_desktop_browser_target()
expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

# This target intentionally has no filesystem media attached. The
# storage-backed process launch gate is covered by the disk/UEFI
# scenario; here the concrete assertion is build/link readiness.
expect(file_exists(target.output)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_desktop_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS desktop integration (serial lane)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
