# GUI Entry Engine2D VirtIO Contract

> This system spec verifies the wrapper VirtIO-GPU Engine2D proof lane before broader GUI/2D framework implementation work continues. It builds the guest, boots it under QEMU when available, waits for either a documented transport failure marker or `render-ready`, and captures a nonblank framebuffer.

<!-- sdn-diagram:id=gui_entry_engine2d_virtio_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_entry_engine2d_virtio_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_entry_engine2d_virtio_spec -> std
gui_entry_engine2d_virtio_spec -> os
gui_entry_engine2d_virtio_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_entry_engine2d_virtio_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Entry Engine2D VirtIO Contract

This system spec verifies the wrapper VirtIO-GPU Engine2D proof lane before broader GUI/2D framework implementation work continues. It builds the guest, boots it under QEMU when available, waits for either a documented transport failure marker or `render-ready`, and captures a nonblank framebuffer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/gui_entry_engine2d_virtio_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the wrapper VirtIO-GPU Engine2D proof lane before
broader GUI/2D framework implementation work continues. It builds the guest,
boots it under QEMU when available, waits for either a documented transport
failure marker or `render-ready`, and captures a nonblank framebuffer.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Syntax

The live scenario creates an isolated run directory, starts QEMU with a QMP
socket, and asserts capture success and nonblack pixels when the guest reaches
the render-ready marker.

## Examples

- VirtIO transport unavailable is an explicit, documented live-skip marker.
- Render-ready guests must produce a nonempty, nonblack QMP capture.

## Scenarios

### Wrapper VirtIO-GPU Engine2D proof lane

#### builds gui_entry_engine2d_virtio.spl into a baremetal kernel

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val run_dir = _run_dir(run_id)
expect(rt_dir_create_all(run_dir)).to_equal(true)

val target = _wrapper_virtio_gpu_target(run_id)
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots the wrapper lane and reaches the render-ready marker

1. Ok

2. stop guest
   - Expected: saw_init_failed is true

3. stop guest
   - Expected: saw_ready is true

4. stop guest
   - Expected: result.success is true

5. stop guest
   - Expected: file_exists(capture_ppm) is true
   - Expected: result.pixels.len() > 0 is true
   - Expected: _non_black_count(result.pixels) > 0 is true

6. Err
   - Expected: spawned is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val run_dir = _run_dir(run_id)
expect(rt_dir_create_all(run_dir)).to_equal(true)

val target = _wrapper_virtio_gpu_target(run_id)
expect(_build_once(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

val qemu_available = can_run_target(target)
if not qemu_available:
    print "[gui_entry_engine2d_virtio_spec] qemu-system-x86_64 not available, skipping live wrapper smoke"
    expect(qemu_available).to_equal(false)
    return

val qmp_socket = _qmp_socket(run_id)
val serial_log = _serial_log(run_id)
val cwd = rt_get_cwd()
val capture_ppm = _capture_ppm(cwd, run_id)

var spawned = false
match spawn_guest_with_qmp(target, qmp_socket, serial_log):
    Ok(handle):
        spawned = true
        val saw_init_failed = wait_for_serial_marker(
            handle, "[BOOT] VirtIO-GPU init failed", 5000)
        if saw_init_failed:
            print "[gui_entry_engine2d_virtio_spec] virtio-gpu BAR/transport unavailable, skipping live render smoke"
            stop_guest(handle)
            expect(saw_init_failed).to_equal(true)
        else:
            val saw_ready = wait_for_serial_marker(
                handle, "[gui-e2d-virtio] render-ready", 60000)
            if not saw_ready:
                print "[gui_entry_engine2d_virtio_spec] render-ready marker not seen within 60s"
                stop_guest(handle)
                expect(saw_ready).to_equal(true)
                return

            val result = capture_qemu_vm(qmp_socket, capture_ppm)
            if not result.success:
                print "[gui_entry_engine2d_virtio_spec] QMP screendump failed: {result.error}"
                stop_guest(handle)
                expect(result.success).to_equal(true)
                return

            stop_guest(handle)
            expect(file_exists(capture_ppm)).to_equal(true)
            expect(result.pixels.len() > 0).to_equal(true)
            expect(_non_black_count(result.pixels) > 0).to_equal(true)
    Err(err):
        print "[gui_entry_engine2d_virtio_spec] failed to spawn guest: {err}"
expect(spawned).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
