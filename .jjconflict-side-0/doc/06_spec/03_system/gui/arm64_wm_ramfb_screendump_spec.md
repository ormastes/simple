# Arm64 Wm Ramfb Screendump Specification

> 1. Ok

<!-- sdn-diagram:id=arm64_wm_ramfb_screendump_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm64_wm_ramfb_screendump_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm64_wm_ramfb_screendump_spec -> std
arm64_wm_ramfb_screendump_spec -> os
arm64_wm_ramfb_screendump_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm64_wm_ramfb_screendump_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Wm Ramfb Screendump Specification

## Scenarios

### SimpleOS ARM64 WM ramfb screendump

#### captures a real QMP screendump after the WM render marker

1. Ok
2.  print arm64 guest diagnostics
3.  write arm64 wm screendump blocker
4.  cleanup arm64 wm guest
   - Expected: saw_render is true
5.  print arm64 guest diagnostics
6.  write arm64 wm screendump blocker
7.  cleanup arm64 wm guest
   - Expected: dumped is true
8.  cleanup arm64 wm guest
9.  write arm64 wm screendump blocker
   - Expected: rt_file_delete(_arm64_wm_screendump_blocker_path()) is true
   - Expected: capture_ok is true
10. Err
11.  write arm64 wm screendump blocker
12. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if rt_file_exists(_arm64_wm_screendump_blocker_path()):
    expect(rt_file_delete(_arm64_wm_screendump_blocker_path())).to_equal(true)
val scenario = scenario_arm64_wm_ramfb()
val target = scenario_target(scenario)
val built = _build_arm64_wm_once()
if not built:
    print "[arm64_wm_ramfb_screendump_spec] live screendump blocked: ARM64 WM target did not build"
    expect(_write_arm64_wm_screendump_blocker("arm64-wm-target-did-not-build", _arm64_wm_build_failure_detail())).to_equal(true)
else:
    if not can_run_target(target):
        print "[arm64_wm_ramfb_screendump_spec] qemu-system-aarch64 or kernel artifact unavailable, skipping live screendump"
        expect(_write_arm64_wm_screendump_blocker("qemu-or-kernel-artifact-unavailable", "")).to_equal(true)
        expect(file_exists(target.output)).to_equal(true)
    else:
        val cwd = rt_get_cwd()
        val run_id = _arm64_wm_screendump_run_id()
        val qmp_socket = "/tmp/arm64_wm_ramfb_screendump_qmp_{run_id}.sock"
        val serial_log = "build/os/arm64_wm_ramfb_screendump.{run_id}.serial.log"
        val capture_ppm = "{cwd}/build/os/arm64_wm_ramfb_screendump.{run_id}.ppm"
        match spawn_guest_with_qmp(target, qmp_socket, serial_log):
            Ok(handle):
                val saw_render = wait_for_serial_marker(handle, "[WM] Glass desktop rendered!", 45000)
                val serial = read_serial_log(handle)
                if not saw_render:
                    print "[arm64_wm_ramfb_screendump_spec] missing ARM64 WM render marker"
                    val stderr = read_qemu_stderr_log(handle)
                    _print_arm64_guest_diagnostics("[arm64_wm_ramfb_screendump_spec]", serial, stderr)
                    _write_arm64_wm_screendump_blocker("arm64-wm-render-marker-missing", _arm64_wm_guest_failure_detail(serial, stderr))
                    _cleanup_arm64_wm_guest(handle, qmp_socket, serial_log)
                    expect(saw_render).to_equal(true)
                else:
                    val dumped = qemu_screendump_to_file(qmp_socket, capture_ppm)
                    if not dumped:
                        print "[arm64_wm_ramfb_screendump_spec] QMP screendump failed"
                        val stderr = read_qemu_stderr_log(handle)
                        _print_arm64_guest_diagnostics("[arm64_wm_ramfb_screendump_spec]", serial, stderr)
                        _write_arm64_wm_screendump_blocker("qmp-screendump-failed", _arm64_wm_guest_failure_detail(serial, stderr))
                        _cleanup_arm64_wm_guest(handle, qmp_socket, serial_log)
                        expect(dumped).to_equal(true)
                    else:
                        _cleanup_arm64_wm_guest(handle, qmp_socket, serial_log)
                        val header_ok = _ppm_header_valid(capture_ppm)
                        val artwork_ok = _ppm_has_dock_icon_artwork(capture_ppm)
                        val capture_ok = file_exists(capture_ppm) and header_ok and artwork_ok
                        if not capture_ok:
                            _write_arm64_wm_screendump_blocker("ppm-capture-assertion-failed", "ppm_path=\"{capture_ppm}\"\nexists={file_exists(capture_ppm)}\nheader_ok={header_ok}\nartwork_ok={artwork_ok}\n")
                        else:
                            if rt_file_exists(_arm64_wm_screendump_blocker_path()):
                                expect(rt_file_delete(_arm64_wm_screendump_blocker_path())).to_equal(true)
                        expect(capture_ok).to_equal(true)
            Err(err):
                print "[arm64_wm_ramfb_screendump_spec] failed to spawn guest: {err}"
                _write_arm64_wm_screendump_blocker("qemu-spawn-failed", "spawn_error=\"\"\"\n{err}\"\"\"\n")
                fail("arm64 WM ramfb guest spawn failed: " + err)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/arm64_wm_ramfb_screendump_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS ARM64 WM ramfb screendump

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
