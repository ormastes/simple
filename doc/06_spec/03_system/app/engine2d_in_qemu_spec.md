# Engine2D In QEMU System Contract

> This system spec verifies the SimpleOS Engine2D guest contract while the parallel GUI/2D framework work continues elsewhere. It builds the baremetal guest, waits for the Engine2D paint marker, captures a QMP framebuffer, checks that it is nonblank, and compares it against the text-tolerant PPM baseline.

<!-- sdn-diagram:id=engine2d_in_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_in_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_in_qemu_spec -> std
engine2d_in_qemu_spec -> os
engine2d_in_qemu_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_in_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D In QEMU System Contract

This system spec verifies the SimpleOS Engine2D guest contract while the parallel GUI/2D framework work continues elsewhere. It builds the baremetal guest, waits for the Engine2D paint marker, captures a QMP framebuffer, checks that it is nonblank, and compares it against the text-tolerant PPM baseline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/engine2d_in_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the SimpleOS Engine2D guest contract while the
parallel GUI/2D framework work continues elsewhere. It builds the baremetal
guest, waits for the Engine2D paint marker, captures a QMP framebuffer, checks
that it is nonblank, and compares it against the text-tolerant PPM baseline.

## Evidence

The live guest writes serial evidence to `build/os/engine2d_qemu_serial.log`.
The capture is compared with `test/baselines/engine2d_in_qemu/verification_scene.ppm`;
`UPDATE_BASELINE=1` rewrites that baseline after a nonblank capture.

## Scenarios

### Engine2D in QEMU Simple OS guest

#### builds gui_entry_engine2d_min.spl into a baremetal kernel

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _engine2d_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots guest, captures framebuffer via QMP, and matches baseline

1. dir create all

2. dir create all

3. Ok

4. nonblank =  assert nonblack ppm with python

5. print "[engine2d in qemu spec] UPDATE BASELINE=1 wrote baseline: {baseline path}

6. stop guest
   - Expected: captured and nonblank and wrote is true

7. stop guest
   - Expected: file_exists(baseline_path) is true

8. stop guest
   - Expected: compared is true

9. print read serial log

10. stop guest
   - Expected: saw_painted is true

11. Err
   - Expected: spawned is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _engine2d_target()
expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

# Host may not have qemu-system-x86_64 — skip the live capture
# step but leave the build assertion as the hard gate.
if not can_run_target(target):
    print "[engine2d_in_qemu_spec] qemu-system-x86_64 not available, skipping live capture"
    expect(file_exists(target.output)).to_equal(true)
    return

val qmp_socket = "/tmp/simpleos_engine2d_qmp.sock"
val serial_log = "build/os/engine2d_qemu_serial.log"
val capture_ppm = "/tmp/engine2d_capture.ppm"
val baseline_dir = "test/baselines/engine2d_in_qemu"
val baseline_path = "{baseline_dir}/verification_scene.ppm"

dir_create_all(baseline_dir)
dir_create_all("build/os")

# Self-spawn QEMU with a QMP server socket and stdout/stderr
# redirected to serial_log. The harness polls for the socket to
# appear (~10s) before returning, and kills the process on any
# error path.
var spawned = false
match spawn_guest_with_qmp(target, qmp_socket, serial_log):
    Ok(handle):
        spawned = true
        # Wait for Engine2D to paint at least once. Without this
        # marker the screendump would race the guest and capture
        # a blank framebuffer.
        val saw_painted = wait_for_serial_marker(
            handle, "[E2D] Engine2D verification frame painted", 30000)
        if saw_painted:
            val captured = _capture_engine2d_ppm_with_python(qmp_socket, capture_ppm)
            var nonblank = false
            if captured:
                nonblank = _assert_nonblack_ppm_with_python(capture_ppm)
            if _update_baseline_requested():
                val cp_result = rt_process_run_timeout("cp", [capture_ppm, baseline_path], 5000)
                val wrote = cp_result[2] == 0 and file_exists(baseline_path)
                print "[engine2d_in_qemu_spec] UPDATE_BASELINE=1 wrote baseline: {baseline_path} (ok={wrote})"
                stop_guest(handle)
                expect(captured and nonblank and wrote).to_equal(true)
            else:
                if not file_exists(baseline_path):
                    print "[engine2d_in_qemu_spec] missing baseline: {baseline_path}"
                    stop_guest(handle)
                    expect(file_exists(baseline_path)).to_equal(true)
                else:
                    val compared = captured and nonblank and _compare_baseline_ppm_with_python(capture_ppm, baseline_path)
                    stop_guest(handle)
                    expect(compared).to_equal(true)
        else:
            print "[engine2d_in_qemu_spec] Engine2D paint marker not seen within 30s"
            print "[engine2d_in_qemu_spec] serial log follows:"
            print read_serial_log(handle)
            stop_guest(handle)
            expect(saw_painted).to_equal(true)
    Err(err):
        print "[engine2d_in_qemu_spec] failed to spawn guest: {err}"
expect(spawned).to_equal(true)
```

</details>

#### has a baseline directory for engine2d_in_qemu captures

1. dir create all
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline_dir = "test/baselines/engine2d_in_qemu"
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
