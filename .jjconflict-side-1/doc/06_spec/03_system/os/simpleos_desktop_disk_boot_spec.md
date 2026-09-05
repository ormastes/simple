# Simpleos Desktop Disk Boot Specification

> <details>

<!-- sdn-diagram:id=simpleos_desktop_disk_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_desktop_disk_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_desktop_disk_boot_spec -> std
simpleos_desktop_disk_boot_spec -> os
simpleos_desktop_disk_boot_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_desktop_disk_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Desktop Disk Boot Specification

## Scenarios

### SimpleOS desktop boot with FAT32 disk (SYS-GUI-007)

#### materializes the selected desktop disk artifact

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disk_ok = ensure_disk_image_or_skip()
if disk_ok:
    val img_path = desktop_disk_image_path()
    expect(file_exists(img_path)).to_equal(true)
```

</details>

#### boots the desktop disk lane and proves editor save/readback

1. Ok
2. rt file write text
3. stop guest
   - Expected: saw_pass is true
   - Expected: output contains `[vfs] mounted fat32`
   - Expected: output contains `[desktop-e2e] memory-bootstrap:ok`
   - Expected: output contains `[desktop-e2e] desktop-ready`
   - Expected: output contains `[desktop-e2e] remote-grouping:ok`
   - Expected: output contains `[desktop-e2e] editor-shortcut:ok`
   - Expected: output contains `[desktop-e2e] editor-save:ok`
   - Expected: output contains `[desktop-e2e] cli-verify:ok`
   - Expected: output contains `[desktop-e2e] simple-cli:ok app=info`
   - Expected: output contains `[desktop-e2e] process-backed:ok app=browser_demo`
   - Expected: output contains `[desktop-e2e] process-backed:ok app=hello_world`
   - Expected: output contains `[desktop-e2e] process-backed:ok app=editor`
   - Expected: output contains `[launcher] process-backed app_id=/sys/apps/browser_demo pid=`
   - Expected: output contains `[launcher] process-backed app_id=/sys/apps/hello_world pid=`
   - Expected: output contains `[launcher] process-backed app_id=/sys/apps/editor pid=`
   - Expected: output contains `[launcher] spawned app_id=/sys/apps/browser_demo.smf pid=1001`
   - Expected: output contains `[launcher] spawned app_id=/sys/apps/hello_world.smf pid=1002`
   - Expected: output contains `[launcher] spawned app_id=/sys/apps/editor.smf pid=1003`
   - Expected: output does not contain `[desktop-e2e] process-backed:resident`
   - Expected: output does not contain `[desktop-e2e] process-backed:unknown`
   - Expected: output does not contain `[desktop-e2e] editor-save:fail`
   - Expected: output does not contain `[desktop-e2e] editor-launch:fail`
   - Expected: output does not contain `[desktop-e2e] cli-verify:fail`
   - Expected: output does not contain `[desktop-e2e] simple-cli:fail app=info`
   - Expected: output does not contain `FAULT @`
   - Expected: output does not contain `EXCEPTION`
   - Expected: output does not contain `cr2=`
   - Expected: output does not contain `cr3=`
   - Expected: output does not contain `panic`
   - Expected: output does not contain `PANIC`
4. Err
   - Expected: false is true
   - Expected: disk_live is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disk_ok = ensure_disk_image_or_skip()
val disk_live = live_desktop_disk_boot_enabled()
if not disk_ok:
    expect(disk_ok).to_equal(false)
else:
    if disk_live:

        val target = get_desktop_browser_target()
        expect(build_os(target)).to_equal(true)
        expect(file_exists(target.output)).to_equal(true)

        if not can_run_target(target):
            print "[simpleos_desktop_disk_boot_spec] qemu-system-x86_64 not available, skipping live boot"
            expect(can_run_target(target)).to_equal(false)
        else:

            val scenario = scenario_x64_desktop_disk()
            val qmp_socket = "/tmp/simpleos_desktop_disk_editor_qmp.sock"
            val serial_log = "build/os/simpleos_desktop_disk_editor_serial.log"

            match spawn_guest_with_qmp_scenario(target, scenario, qmp_socket, serial_log):
                Ok(handle):
                    val saw_pass = wait_for_serial_marker(handle, "TEST PASSED", 60000)
                    val output = read_serial_log(handle)
                    if not saw_pass:
                        rt_file_write_text("build/os/simpleos_desktop_disk_editor_failure_serial.log", output)
                    stop_guest(handle)

                    expect(saw_pass).to_equal(true)
                    expect(output.contains("[vfs] mounted fat32")).to_equal(true)
                    expect(output.contains("[desktop-e2e] memory-bootstrap:ok")).to_equal(true)
                    expect(output.contains("[desktop-e2e] desktop-ready")).to_equal(true)
                    expect(output.contains("[desktop-e2e] remote-grouping:ok")).to_equal(true)
                    expect(output.contains("[desktop-e2e] editor-shortcut:ok")).to_equal(true)
                    expect(output.contains("[desktop-e2e] editor-save:ok")).to_equal(true)
                    expect(output.contains("[desktop-e2e] cli-verify:ok")).to_equal(true)
                    expect(output.contains("[desktop-e2e] simple-cli:ok app=info")).to_equal(true)
                    expect(output.contains("[desktop-e2e] process-backed:ok app=browser_demo")).to_equal(true)
                    expect(output.contains("[desktop-e2e] process-backed:ok app=hello_world")).to_equal(true)
                    expect(output.contains("[desktop-e2e] process-backed:ok app=editor")).to_equal(true)
                    expect(output.contains("[launcher] process-backed app_id=/sys/apps/browser_demo pid=")).to_equal(true)
                    expect(output.contains("[launcher] process-backed app_id=/sys/apps/hello_world pid=")).to_equal(true)
                    expect(output.contains("[launcher] process-backed app_id=/sys/apps/editor pid=")).to_equal(true)
                    expect(output.contains("[launcher] spawned app_id=/sys/apps/browser_demo.smf pid=1001")).to_equal(true)
                    expect(output.contains("[launcher] spawned app_id=/sys/apps/hello_world.smf pid=1002")).to_equal(true)
                    expect(output.contains("[launcher] spawned app_id=/sys/apps/editor.smf pid=1003")).to_equal(true)
                    expect(output.contains("[desktop-e2e] process-backed:resident")).to_equal(false)
                    expect(output.contains("[desktop-e2e] process-backed:unknown")).to_equal(false)
                    expect(output.contains("[desktop-e2e] editor-save:fail")).to_equal(false)
                    expect(output.contains("[desktop-e2e] editor-launch:fail")).to_equal(false)
                    expect(output.contains("[desktop-e2e] cli-verify:fail")).to_equal(false)
                    expect(output.contains("[desktop-e2e] simple-cli:fail app=info")).to_equal(false)
                    expect(output.contains("FAULT @")).to_equal(false)
                    expect(output.contains("EXCEPTION")).to_equal(false)
                    expect(output.contains("cr2=")).to_equal(false)
                    expect(output.contains("cr3=")).to_equal(false)
                    expect(output.contains("panic")).to_equal(false)
                    expect(output.contains("PANIC")).to_equal(false)
                Err(err):
                    print "[simpleos_desktop_disk_boot_spec] failed to spawn guest: {err}"
                    expect(false).to_equal(true)
    else:
        print "[simpleos_desktop_disk_boot_spec] live desktop disk boot disabled; set SIMPLEOS_QEMU_DESKTOP_DISK_LIVE=1 to run"
        expect(disk_live).to_equal(false)
```

</details>

#### boots the UEFI desktop lane when explicitly enabled

1. Ok
2. stop guest
   - Expected: saw_pass is true
   - Expected: output contains `[desktop-e2e] desktop-ready`
   - Expected: output does not contain `[desktop-e2e] process-backed:resident`
   - Expected: output does not contain `[desktop-e2e] process-backed:unknown`
   - Expected: output does not contain `FAULT @`
   - Expected: output does not contain `EXCEPTION`
   - Expected: output does not contain `cr2=`
   - Expected: output does not contain `cr3=`
   - Expected: output does not contain `panic`
   - Expected: output does not contain `PANIC`
3. Err
   - Expected: false is true
   - Expected: uefi_live is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disk_ok = ensure_disk_image_or_skip()
val uefi_live = live_desktop_uefi_boot_enabled()
if not disk_ok:
    expect(disk_ok).to_equal(false)
else:
    if uefi_live:
        val target = get_desktop_browser_target()
        expect(build_os(target)).to_equal(true)
        expect(file_exists(target.output)).to_equal(true)
        val uefi_media_ok = ensure_desktop_uefi_boot_image(target.output)

        if not uefi_media_ok:
            print "[simpleos_desktop_disk_boot_spec] UEFI boot media unavailable"
            expect(desktop_uefi_boot_media_ready()).to_equal(false)
        elif not can_run_target(target):
            print "[simpleos_desktop_disk_boot_spec] qemu-system-x86_64 not available, skipping UEFI live boot"
            expect(can_run_target(target)).to_equal(false)
        else:
            val scenario = scenario_x64_desktop_uefi()
            val qmp_socket = "/tmp/simpleos_desktop_uefi_qmp.sock"
            val serial_log = "build/os/simpleos_desktop_uefi_serial.log"

            match spawn_guest_with_qmp_scenario(target, scenario, qmp_socket, serial_log):
                Ok(handle):
                    val saw_pass = wait_for_serial_marker(handle, "TEST PASSED", 90000)
                    val output = read_serial_log(handle)
                    stop_guest(handle)

                    expect(saw_pass).to_equal(true)
                    expect(output.contains("[desktop-e2e] desktop-ready")).to_equal(true)
                    expect(output.contains("[desktop-e2e] process-backed:resident")).to_equal(false)
                    expect(output.contains("[desktop-e2e] process-backed:unknown")).to_equal(false)
                    expect(output.contains("FAULT @")).to_equal(false)
                    expect(output.contains("EXCEPTION")).to_equal(false)
                    expect(output.contains("cr2=")).to_equal(false)
                    expect(output.contains("cr3=")).to_equal(false)
                    expect(output.contains("panic")).to_equal(false)
                    expect(output.contains("PANIC")).to_equal(false)
                Err(err):
                    print "[simpleos_desktop_disk_boot_spec] failed to spawn UEFI guest: {err}"
                    expect(false).to_equal(true)
    else:
        print "[simpleos_desktop_disk_boot_spec] live UEFI desktop boot disabled; set SIMPLEOS_QEMU_DESKTOP_UEFI_LIVE=1 to run"
        expect(uefi_live).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_desktop_disk_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS desktop boot with FAT32 disk (SYS-GUI-007)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
