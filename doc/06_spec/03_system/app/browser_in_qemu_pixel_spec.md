# Browser In QEMU Pixel Contract

> This slow system spec compares the deterministic browser framebuffer captured from QEMU against `test/baselines/browser_in_qemu/session.ppm`. It keeps the pixel baseline failure mode concrete: missing baseline, failed screendump, spawn failure, and byte mismatch each assert the condition that failed instead of a synthetic false assertion.

<!-- sdn-diagram:id=browser_in_qemu_pixel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_in_qemu_pixel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_in_qemu_pixel_spec -> std
browser_in_qemu_pixel_spec -> os
browser_in_qemu_pixel_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_in_qemu_pixel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser In QEMU Pixel Contract

This slow system spec compares the deterministic browser framebuffer captured from QEMU against `test/baselines/browser_in_qemu/session.ppm`. It keeps the pixel baseline failure mode concrete: missing baseline, failed screendump, spawn failure, and byte mismatch each assert the condition that failed instead of a synthetic false assertion.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser_in_qemu_pixel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This slow system spec compares the deterministic browser framebuffer captured
from QEMU against `test/baselines/browser_in_qemu/session.ppm`. It keeps the
pixel baseline failure mode concrete: missing baseline, failed screendump, spawn
failure, and byte mismatch each assert the condition that failed instead of a
synthetic false assertion.

## Evidence

The capture is written to `build/os/browser_capture_pixel.ppm`; serial evidence
is written to `build/os/browser_qemu_pixel_serial.log`.

## Scenarios

### Browser webrendering in QEMU Simple OS guest pixel regression

<details>
<summary>Advanced: matches the deterministic framebuffer baseline</summary>

#### matches the deterministic framebuffer baseline _(slow)_

1. dir create all
   - Expected: file_exists(baseline_path) is true

2. Ok

3. stop guest
   - Expected: captured is true

4. stop guest
   - Expected: _ppm_capture_matches_baseline(capture_ppm, baseline_path) is true

5. Err
   - Expected: spawned is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _browser_target()
expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

val qemu_available = can_run_target(target)
if not qemu_available:
    print "[browser_in_qemu_pixel_spec] qemu-system-x86_64 not available, skipping live capture"
    expect(qemu_available).to_equal(false)
    return

val qmp_socket = "/tmp/simpleos_browser_pixel_qmp.sock"
val serial_log = "build/os/browser_qemu_pixel_serial.log"
val capture_ppm = "build/os/browser_capture_pixel.ppm"
val baseline_path = "test/baselines/browser_in_qemu/session.ppm"
dir_create_all("build/os")

if not file_exists(baseline_path):
    print "[browser_in_qemu_pixel_spec] missing baseline: {baseline_path}"
    expect(file_exists(baseline_path)).to_equal(true)
    return

var spawned = false
match spawn_guest_with_qmp(target, qmp_socket, serial_log):
    Ok(handle):
        spawned = true
        val saw_marker = wait_for_serial_marker(
            handle,
            "[BE] Frame painted: HTML -> DOM -> layout -> paint -> scene -> software rasterizer -> framebuffer",
            30000)
        if not saw_marker:
            print "[browser_in_qemu_pixel_spec] serial marker not observed before capture; using QMP pixel compare as authority"

        val captured = _capture_qmp_ppm_with_timeout(qmp_socket, capture_ppm)
        if not captured:
            stop_guest(handle)
            print "[browser_in_qemu_pixel_spec] QMP screendump timed out or failed"
            expect(captured).to_equal(true)
            return
        stop_guest(handle)

        expect(_ppm_capture_matches_baseline(capture_ppm, baseline_path)).to_equal(true)
    Err(err):
        print "[browser_in_qemu_pixel_spec] failed to spawn guest: {err}"
expect(spawned).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
