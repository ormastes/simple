# Engine2D Primitive Rendering Contract

> This system spec verifies the Engine2D primitive demo contract without changing the 2D framework implementation lane. It builds the primitive guest, waits for the paint marker when QEMU is available, captures a framebuffer, and validates that the primitive colors are present.

<!-- sdn-diagram:id=engine2d_primitives_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_primitives_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_primitives_spec -> std
engine2d_primitives_spec -> os
engine2d_primitives_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_primitives_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Primitive Rendering Contract

This system spec verifies the Engine2D primitive demo contract without changing the 2D framework implementation lane. It builds the primitive guest, waits for the paint marker when QEMU is available, captures a framebuffer, and validates that the primitive colors are present.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/engine/engine2d_primitives_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the Engine2D primitive demo contract without changing
the 2D framework implementation lane. It builds the primitive guest, waits for
the paint marker when QEMU is available, captures a framebuffer, and validates
that the primitive colors are present.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Syntax

The live scenario uses the shared QEMU harness and a Python PPM probe to assert
capture success and primitive pixel evidence.

## Examples

- The guest must emit `[E2D-PRIM] Engine2D primitive frame painted`.
- The captured PPM must contain the expected primitive color evidence.

## Scenarios

### Engine2D primitive draw verification in QEMU

#### builds gui_engine2d_primitives_entry.spl into a baremetal kernel

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _primitives_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots guest, captures framebuffer, and asserts each primitive pixel

1. dir create all

2. dir create all

3. Ok

4. stop guest
   - Expected: all_ok is true

5. print read serial log

6. stop guest
   - Expected: saw_painted is true

7. Err
   - Expected: spawned is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _primitives_target()
val built = build_os(target)
expect(built).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

# Host may not have qemu-system-x86_64 — skip the live capture
# step but leave the build assertion as the hard gate.
if not built or not file_exists(target.output):
    print "[engine2d_primitives_spec] kernel build unavailable, skipping live capture"
    expect(file_exists(target.output)).to_equal(true)
elif not can_run_target(target):
    print "[engine2d_primitives_spec] qemu-system-x86_64 not available, skipping live capture"
    expect(can_run_target(target)).to_equal(false)
else:
    val qmp_socket = "/tmp/simpleos_engine2d_primitives_qmp.sock"
    val serial_log = "build/os/engine2d_primitives_qemu_serial.log"
    val capture_ppm = "build/os/engine2d_primitives_capture.ppm"
    val baseline_dir = "doc/08_tracking/baselines"
    val baseline_path = "{baseline_dir}/engine2d_primitives.ppm"
    val baseline_serial = "{baseline_dir}/engine2d_primitives.serial.log"

    dir_create_all(baseline_dir)
    dir_create_all("build/os")

    var spawned = false
    match spawn_guest_with_qmp(target, qmp_socket, serial_log):
        Ok(handle):
            spawned = true
            val saw_painted = wait_for_serial_marker(
                handle, "[E2D-PRIM] Engine2D primitive frame painted", 30000)
            if saw_painted:
                val captured = _capture_primitive_ppm_with_python(qmp_socket, capture_ppm)
                val all_ok = captured and _assert_primitive_ppm_with_python(capture_ppm)
                stop_guest(handle)
                expect(all_ok).to_equal(true)
            else:
                print "[engine2d_primitives_spec] primitive paint marker not seen within 30s"
                print "[engine2d_primitives_spec] serial log follows:"
                print read_serial_log(handle)
                stop_guest(handle)
                expect(saw_painted).to_equal(true)
        Err(err):
            print "[engine2d_primitives_spec] failed to spawn guest: {err}"
    expect(spawned).to_equal(true)
```

</details>

#### has a baseline directory for engine2d primitive captures

1. dir create all
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline_dir = "doc/08_tracking/baselines"
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
