# GUI Entry Engine2D VirtIO Contract

> This system spec verifies the wrapper VirtIO-GPU Engine2D proof lane before broader GUI/2D framework implementation work continues. It builds the guest, boots it under QEMU when available, waits for either a documented transport failure marker or `render-ready`, and captures a nonblank framebuffer.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds gui_entry_engine2d_virtio.spl into a baremetal kernel
   - Expected: dir_create_all(run_dir) is true
   - Expected: ok is true
   - Expected: file_exists(target.output) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds gui_entry_engine2d_virtio.spl into a baremetal kernel")
val run_id = _run_id()
val run_dir = _run_dir(run_id)
expect(dir_create_all(run_dir)).to_equal(true)

val target = _wrapper_virtio_gpu_target(run_id)
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots the wrapper lane and reaches the render-ready marker

- boots the wrapper lane and reaches the render-ready marker
   - Expected: dir_create_all(run_dir) is true
   - Expected: _build_once(target) is true
   - Expected: file_exists(target.output) is true
   - Expected: qemu_available is false
   - Expected: saw_init_failed is true
   - Expected: saw_ready is true
   - Expected: result.success is true
   - Expected: file_exists(capture_ppm) is true
   - Expected: result.pixels.len() > 0 is true
   - Expected: _non_black_count(result.pixels) > 0 is true
   - Expected: spawned is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the wrapper lane and reaches the render-ready marker")
val run_id = _run_id()
val run_dir = _run_dir(run_id)
expect(dir_create_all(run_dir)).to_equal(true)

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
val working_dir = cwd()
val capture_ppm = _capture_ppm(working_dir, run_id)

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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c1757c4c08b91fe4618121f8c2f34e1a79940c4c9c6f0ead8dcdd88f1f50c269`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1757c4c08b91fe4618121f8c2f34e1a79940c4c9c6f0ead8dcdd88f1f50c269`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1757c4c08b91fe4618121f8c2f34e1a79940c4c9c6f0ead8dcdd88f1f50c269`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/03_system/gui/gui_entry_engine2d_virtio_spec.spl
mirror: doc/06_spec/03_system/gui/gui_entry_engine2d_virtio_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/gui_entry_engine2d_virtio_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/gui_entry_engine2d_virtio_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/gui_entry_engine2d_virtio_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds gui_entry_engine2d_virtio.spl into a baremetal kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
