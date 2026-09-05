# Simpleos Desktop With Apps Framebuffer Specification

> <details>

<!-- sdn-diagram:id=simpleos_desktop_with_apps_framebuffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_desktop_with_apps_framebuffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_desktop_with_apps_framebuffer_spec -> std
simpleos_desktop_with_apps_framebuffer_spec -> os
simpleos_desktop_with_apps_framebuffer_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_desktop_with_apps_framebuffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Desktop With Apps Framebuffer Specification

## Scenarios

### SimpleOS desktop framebuffer with apps (SYS-GUI-006)

#### builds desktop_e2e_entry.spl into a baremetal kernel

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _desktop_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots desktop, waits for remote-grouping:ok, captures with-apps baseline

1. dir create all
2. dir create all
   - Expected: _run_live_capture(target, qmp_socket, serial_log, capture_ppm, baseline_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _desktop_target()
expect(_build_once(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

if not _live_with_apps_framebuffer_capture_enabled():
    print "[simpleos_desktop_with_apps_fb_spec] live framebuffer capture disabled; set SIMPLEOS_QEMU_DESKTOP_WITH_APPS_FRAMEBUFFER_LIVE=1 to run"
    expect(_live_with_apps_framebuffer_capture_enabled()).to_equal(false)
elif not ensure_desktop_disk_image():
    print "[simpleos_desktop_with_apps_fb_spec] disk image unavailable, skipping live capture"
    expect(file_exists(target.output)).to_equal(true)
elif not can_run_target(target):
    print "[simpleos_desktop_with_apps_fb_spec] qemu-system-x86_64 not available, skipping live capture"
    expect(can_run_target(target)).to_equal(false)
else:
    val qmp_socket = "/tmp/simpleos_desktop_with_apps_qmp.sock"
    val serial_log = "build/os/simpleos_desktop_with_apps_qemu_serial.log"
    val capture_ppm = "/tmp/simpleos_desktop_with_apps_capture.ppm"
    val baseline_dir = "test/baselines/simpleos_desktop_with_apps_framebuffer"
    val baseline_path = "{baseline_dir}/desktop_with_apps_scene.ppm"

    dir_create_all(baseline_dir)
    dir_create_all("build/os")

    expect(_run_live_capture(target, qmp_socket, serial_log, capture_ppm, baseline_path)).to_equal(true)
```

</details>

#### has a baseline directory for simpleos_desktop_with_apps_framebuffer captures

1. dir create all
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline_dir = "test/baselines/simpleos_desktop_with_apps_framebuffer"
dir_create_all(baseline_dir)
expect(file_exists(baseline_dir)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS desktop framebuffer with apps (SYS-GUI-006)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
