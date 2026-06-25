# Wm Input Qemu Smoke Specification

> <details>

<!-- sdn-diagram:id=wm_input_qemu_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_input_qemu_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_input_qemu_smoke_spec -> std
wm_input_qemu_smoke_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_input_qemu_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Input Qemu Smoke Specification

## Scenarios

### SimpleOS WM input smoke in QEMU

#### builds the WM input test entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _wm_input_target()
expect(_build_or_report_blocker(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots and emits focus plus drag markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _wm_input_target()
val built = _build_or_report_blocker(target)
if not built:
    val blocker_evidence = _known_build_blocker_evidence(target)
    expect(blocker_evidence.contains("live WM input smoke blocked")).to_equal(true)
    expect(blocker_evidence.contains(target.output)).to_equal(true)
    expect(blocker_evidence.contains(target.entry)).to_equal(true)
else:
    if not can_run_target(target):
        print "[wm_input_qemu_smoke_spec] qemu-system-x86_64 not available, skipping live WM input smoke"
        expect(file_exists(target.output)).to_equal(true)
    else:
        val result = run_os_qemu_with_target_via_timeout(target, "20s", 30000)
        val serial = result[0] + result[1]
        val saw_init = serial.contains("[wm-input-test] Init synthetic input path")
        val saw_focus = serial.contains("[wm-input-test] focus click OK")
        val saw_focus_command = serial.contains("[wm-input-test] focus command_kind=focus_window window_id=1")
        val saw_titlebar_button = serial.contains("[wm-input-test] titlebar_button_click action=close window_id=1")
        val saw_text_input = serial.contains("[wm-input-test] text_input_edit window_id=1 field=search before='' after='abc'")
        val saw_css_pixels = serial.contains("[wm-input-test] css_pixels viewport=1024x768 browser=320x202 scale=1")
        val saw_drag = serial.contains("[wm-input-test] drag OK -> 444,252")
        val saw_drag_command = serial.contains("[wm-input-test] drag command_kind=move_window window_id=1 from=320,180 to=444,252")
        val saw_pass = serial.contains("[PASS] wm_input_test_entry")
        val saw_test_passed = serial.contains("TEST PASSED")

        if not saw_init or not saw_focus or not saw_focus_command or not saw_titlebar_button or not saw_text_input or not saw_css_pixels or not saw_drag or not saw_drag_command or not saw_pass or not saw_test_passed:
            print "[wm_input_qemu_smoke_spec] missing marker init={saw_init} focus={saw_focus} focus_command={saw_focus_command} titlebar_button={saw_titlebar_button} text_input={saw_text_input} css_pixels={saw_css_pixels} drag={saw_drag} drag_command={saw_drag_command} pass={saw_pass} test_passed={saw_test_passed} exit={result[2]}"
            print "[wm_input_qemu_smoke_spec] serial follows:\n{serial}"

        expect(saw_init).to_equal(true)
        expect(saw_focus).to_equal(true)
        expect(saw_focus_command).to_equal(true)
        expect(saw_titlebar_button).to_equal(true)
        expect(saw_text_input).to_equal(true)
        expect(saw_css_pixels).to_equal(true)
        expect(saw_drag).to_equal(true)
        expect(saw_drag_command).to_equal(true)
        expect(saw_pass).to_equal(true)
        expect(saw_test_passed).to_equal(true)
```

</details>

#### captures framebuffer markers for focus and drag state

- Ok
-  print guest diagnostics
- stop guest
   - Expected: saw_fb is true
-  print guest diagnostics
- stop guest
   - Expected: captured is true
- stop guest
   - Expected: file_exists(capture_ppm) is true
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = _wm_input_target()
val built = _build_or_report_blocker(target)
if not built:
    val blocker_evidence = _known_build_blocker_evidence(target)
    expect(blocker_evidence.contains("known linker blocker")).to_equal(true)
    expect(blocker_evidence.contains(target.output)).to_equal(true)
    expect(blocker_evidence.contains(target.entry)).to_equal(true)
else:
    if not can_run_target(target):
        print "[wm_input_qemu_smoke_spec] qemu-system-x86_64 not available, skipping framebuffer smoke"
        expect(file_exists(target.output)).to_equal(true)
    else:
        val cwd = rt_get_cwd()
        val run_id = _run_id()
        val run_dir = _run_dir(run_id)
        expect(rt_dir_create_all(run_dir)).to_equal(true)
        val qmp_socket = _qmp_socket(run_id)
        val serial_log = _serial_log(run_id)
        val capture_ppm = _capture_ppm(cwd, run_id)
        match spawn_guest_with_qmp(target, qmp_socket, serial_log):
            Ok(handle):
                val saw_fb = wait_for_serial_marker(handle, "[wm-input-test] framebuffer marker OK", 30000)
                val serial = read_serial_log(handle)
                if not saw_fb:
                    print "[wm_input_qemu_smoke_spec] missing framebuffer marker"
                    _print_guest_diagnostics("[wm_input_qemu_smoke_spec]", serial, read_qemu_stderr_log(handle))
                    stop_guest(handle)
                    expect(saw_fb).to_equal(true)
                else:
                    val captured = _capture_and_assert_input_ppm(qmp_socket, capture_ppm)
                    if not captured:
                        print "[wm_input_qemu_smoke_spec] QMP screendump or framebuffer pixel assertion failed"
                        _print_guest_diagnostics("[wm_input_qemu_smoke_spec]", serial, read_qemu_stderr_log(handle))
                        stop_guest(handle)
                        expect(captured).to_equal(true)
                    else:
                        stop_guest(handle)
                        expect(file_exists(capture_ppm)).to_equal(true)
            Err(err):
                print "[wm_input_qemu_smoke_spec] failed to spawn guest: {err}"
                fail("WM input QEMU guest spawn failed: " + err)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_input_qemu_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS WM input smoke in QEMU

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
