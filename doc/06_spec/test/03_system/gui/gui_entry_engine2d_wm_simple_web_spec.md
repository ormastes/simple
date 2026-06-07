# GUI Entry Engine2D WM Simple Web QEMU Specification

> This scenario is the live x86_64 QEMU release gate for the SimpleOS Engine2D, WM, Simple Web, and MDI demo. It builds the freestanding `gui_entry_engine2d.spl` kernel, boots it with QMP enabled, waits for the guest render-ready marker, and captures the visible QEMU framebuffer.

<!-- sdn-diagram:id=gui_entry_engine2d_wm_simple_web_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_entry_engine2d_wm_simple_web_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_entry_engine2d_wm_simple_web_spec -> std
gui_entry_engine2d_wm_simple_web_spec -> os
gui_entry_engine2d_wm_simple_web_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_entry_engine2d_wm_simple_web_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Entry Engine2D WM Simple Web QEMU Specification

This scenario is the live x86_64 QEMU release gate for the SimpleOS Engine2D, WM, Simple Web, and MDI demo. It builds the freestanding `gui_entry_engine2d.spl` kernel, boots it with QMP enabled, waits for the guest render-ready marker, and captures the visible QEMU framebuffer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/gui_hardening_current_plan/state.md |
| Design | doc/05_design/gui_color_image_pipeline_8k.md |
| Research | doc/01_research/local/gui_color_image_pipeline_8k.md |
| Source | `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario is the live x86_64 QEMU release gate for the SimpleOS Engine2D,
WM, Simple Web, and MDI demo. It builds the freestanding
`gui_entry_engine2d.spl` kernel, boots it with QMP enabled, waits for the guest
render-ready marker, and captures the visible QEMU framebuffer.

## Acceptance Criteria

- The kernel image builds and QEMU can launch it with `-vga std`.
- Serial output proves WM, Engine2D, Simple Web, top command lane, taskbar,
  HTML renderability, and the canonical five shared MDI surfaces.
- QMP `pmemsave 0xfd000000` captures the BGA framebuffer and converts it to a
  1024x768 PPM with more than 100000 non-black pixels and exact sampled colors
  for the red MMIO probe, browser header, web body bands, top command lane, and
  taskbar/background surface.
- A failed serial marker, failed QMP capture, blank framebuffer, or stale MDI
  surface count fails the scenario explicitly.

## Artifacts

Each run writes a unique artifact directory under
`build/tmp/gui_entry_engine2d_wm_simple_web_spec_<pid>_<micros>/` containing the
serial log and captured PPM. The QMP socket path also includes the same run id
to avoid collisions between parallel test runs.

## Examples

Run the live gate with:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple test \
  test/system/gui_entry_engine2d_wm_simple_web_spec.spl \
  --mode=interpreter --timeout 420 --clean --format json
```

A passing capture prints `capture_method=pmemsave`, `pmem_addr=0xfd000000`,
`ppm_dims=1024x768`,
`nonblack=<large count>`, and all checks as true:

```text
checks=[probe=True,header=True,bodyA=True,bodyB=True,top=True,taskbar=True]
```

If the serial markers are present but the QMP capture is blank, the failure is
in the framebuffer presentation path rather than the MDI service contract. If
`shared-mdi-ready surfaces=5` or `windows-ready count=5` is missing, the
canonical shared-MDI surface setup regressed before the bitmap gate.

## Failure Diagnostics

- Missing marker failures print the full guest serial log and QEMU stderr.
- Bitmap failures leave `capture.ppm` in the run artifact directory for manual
  sampling.
- The red probe at `(10,0)` proves basic framebuffer MMIO visibility.
- The browser, top-lane, and taskbar samples prove the WM/MDI scene is not a
  one-pixel or blank-frame false pass.

**Requirements:** N/A
**Plan:** .spipe/gui_hardening_current_plan/state.md
**Design:** doc/05_design/gui_color_image_pipeline_8k.md
**Research:** doc/01_research/local/gui_color_image_pipeline_8k.md

## Scenarios

### WM Simple Web Engine2D BGA QEMU check

#### builds, boots, reaches render markers, and captures Simple Web pixels

1. dir create all
2. Ok
3.  print guest diagnostics
4. stop guest
   - Expected: _pass_fail(saw_probe and saw_wm and saw_engine and saw_web and saw_mdi and saw_top and saw_taskbar and saw_html and saw_ready) equals `pass`
5.  print guest diagnostics
6. stop guest
   - Expected: _pass_fail(captured) equals `pass`
7. stop guest
   - Expected: _pass_fail(file_exists(capture_ppm)) equals `pass`
8. Err
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_wm_simple_web_check_target()
expect(_pass_fail(_build_once(target))).to_equal("pass")
expect(_pass_fail(file_exists(target.output))).to_equal("pass")
val capture_target = _capture_hold_target(target)

if not can_run_target(capture_target):
    print "[gui_entry_engine2d_wm_simple_web_spec] qemu-system-x86_64 not available, skipping live capture"
    expect(_pass_fail(file_exists(target.output))).to_equal("pass")
    return

val run_id = _run_id()
val artifact_dir = _run_dir(run_id)
val qmp_socket = _qmp_socket(run_id)
val serial_log = _serial_log(run_id)
val cwd = rt_get_cwd()
val capture_ppm = _capture_ppm(cwd, run_id)

dir_create_all(artifact_dir)
val _deleted_qmp_socket = rt_file_delete(qmp_socket)
val _deleted_capture_ppm = rt_file_delete(capture_ppm)

match spawn_guest_with_qmp(capture_target, qmp_socket, serial_log):
    Ok(handle):
        val saw_ready = wait_for_serial_marker(handle, "[integrated-demo] render-ready", 60000)
        val serial = read_serial_log(handle)
        val saw_wm = serial.contains("[wm-demo] wm-service-ready")
        val saw_engine = serial.contains("[e2d-demo] engine-core-ready")
        val saw_web = serial.contains("[web-demo] pixels-ready")
        val saw_mdi = serial.contains("[mdi-demo] shared-mdi-ready surfaces=5") and serial.contains("[mdi-demo] windows-ready count=5")
        val saw_top = serial.contains("[mdi-demo] top-command-lane-ready")
        val saw_taskbar = serial.contains("[mdi-demo] taskbar-ready")
        val saw_html = serial.contains("[mdi-demo] html-renderable window=browser")
        val saw_probe = serial.contains("[GUI] mmio-probe-painted")

        if not saw_probe or not saw_wm or not saw_engine or not saw_web or not saw_mdi or not saw_top or not saw_taskbar or not saw_html or not saw_ready:
            print "[gui_entry_engine2d_wm_simple_web_spec] missing marker probe={saw_probe} wm={saw_wm} e2d={saw_engine} web={saw_web} mdi={saw_mdi} top={saw_top} taskbar={saw_taskbar} html={saw_html} ready={saw_ready}"
            _print_guest_diagnostics("[gui_entry_engine2d_wm_simple_web_spec]", serial, read_qemu_stderr_log(handle))
            stop_guest(handle)
            expect(_pass_fail(saw_probe and saw_wm and saw_engine and saw_web and saw_mdi and saw_top and saw_taskbar and saw_html and saw_ready)).to_equal("pass")
        else:
            val captured = _capture_and_assert_web_ppm_retry(qmp_socket, capture_ppm, 1)
            if not captured:
                print "[gui_entry_engine2d_wm_simple_web_spec] QMP pmemsave framebuffer or web pixel assertion failed"
                _print_guest_diagnostics("[gui_entry_engine2d_wm_simple_web_spec]", serial, read_qemu_stderr_log(handle))
                stop_guest(handle)
                expect(_pass_fail(captured)).to_equal("pass")
            else:
                stop_guest(handle)
                expect(_pass_fail(file_exists(capture_ppm))).to_equal("pass")
    Err(err):
        print "[gui_entry_engine2d_wm_simple_web_spec] failed to spawn guest: {err}"
        expect(err).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/gui_hardening_current_plan/state.md](.spipe/gui_hardening_current_plan/state.md)
- **Design:** [doc/05_design/gui_color_image_pipeline_8k.md](doc/05_design/gui_color_image_pipeline_8k.md)
- **Research:** [doc/01_research/local/gui_color_image_pipeline_8k.md](doc/01_research/local/gui_color_image_pipeline_8k.md)


</details>
