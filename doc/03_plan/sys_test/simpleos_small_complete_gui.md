# SimpleOS Small Complete GUI — System Test Plan

## Scope

This plan defines the system tests required to call the `x86_64` SimpleOS QEMU desktop path a small but complete GUI OS.

It intentionally focuses on:

- real QEMU guest boot
- real desktop-shell integration
- real launcher-spawned apps
- real framebuffer output capture

It does not treat hosted mode alone as sufficient proof.

## Test Matrix

### SYS-GUI-001 Boot to desktop

Goal:

- prove the GUI guest boots and reaches desktop-ready state

Method:

- boot the `x86_64` GUI target in QEMU
- assert serial markers for boot, shell-ready, launcher-ready, and desktop-ready

Pass:

- expected markers appear within timeout
- no `FAULT @`, panic, or timeout

Likely implementation base:

- `src/os/qemu_runner.spl`
- `test/system/browser_engine_in_qemu_spec.spl`

### SYS-GUI-002 Launcher and shortcut join

Goal:

- prove the real desktop path handles launcher startup and one shortcut dispatch

Method:

- wait for launcher ready marker
- inject or trigger one launcher shortcut
- assert app launch marker and WM join marker

Pass:

- app launch is visible in serial output
- launcher and WM agree the app is running

### SYS-GUI-003 Hello World single-window app

Goal:

- prove one real single-window GUI app works through the launcher-owned path

Method:

- launch `Hello World`
- assert one remote window is created
- assert app identity is stable across launcher, shell, and WM views

Pass:

- exactly one expected window group appears
- no fallback title-only grouping is needed

### SYS-GUI-004 Browser Demo multi-window app

Goal:

- prove one real multi-window GUI app works through the launcher-owned path

Method:

- launch `Browser Demo`
- assert at least two windows are created
- assert both windows remain grouped under one `app_id`

Pass:

- multi-window grouping is stable
- title changes do not split ownership

### SYS-GUI-005 Lifecycle cleanup

Goal:

- prove live cleanup for exit, terminate, and crash

Method:

- run three sub-scenarios:
- graceful app exit
- terminate from shell action
- crash or forced nonzero exit

Pass:

- launcher state becomes `exited`, `terminated`, or `crashed` as appropriate
- stale windows are removed or invalidated
- no orphaned WM ownership remains

### SYS-GUI-006 Framebuffer output baseline compare

Goal:

- prove the guest rendered the expected desktop pixels

Method:

- boot a GUI-enabled QEMU target with QMP enabled
- wait for a paint marker
- capture framebuffer via `qemu_capture`
- compare with a baseline PPM using the agreed tolerance profile

Pass:

- screendump succeeds
- non-black pixel count is sane
- comparison meets threshold

Likely implementation base:

- `test/system/engine2d_in_qemu_spec.spl`
- `src/os/compositor/qemu_capture.spl`

### SYS-GUI-007 Disk-backed smoke

Goal:

- prove the GUI path still works with the intended real storage environment

Method:

- boot with the real disk-image path
- reach desktop-ready
- launch one app

Pass:

- desktop boots with storage enabled
- app launch still works

Priority:

- next milestone

Status (2026-04-14):

- [x] disk-lane boot-green. Direct QEMU boot of
  `build/os/simpleos_desktop_e2e_32.elf` with `build/os/fat32.img`
  attached as an NVMe `-drive`+`-device nvme` emits, in order,
  `[vfs] mounted fat32 device=nvme0 volume=simpleos`,
  `[desktop-e2e] desktop-ready`, and `[desktop-e2e] launcher-ready apps=4`.
  Baselines under `doc/08_tracking/baselines/sys_gui_007_disk.{serial.txt,ppm}`.
  Spec at `test/system/simpleos_desktop_disk_boot_spec.spl`.
- [ ] per-app launcher spawn marker is still blocked by `shortcut:fail`
  (SYS-GUI-002, owned by Agent SF). Scoped out of the disk-lane
  assertion — tracked in
  `doc/08_tracking/todo/sys_gui_007_live_blocker_2026-04-14.md`.

## Recommended Artifacts

- serial logs under `build/os/*_serial.log`
- captured PPM under `build/os/*.ppm`
- checked-in baselines under `test/baselines/`

## Gate Definition

Required for the first milestone:

- `SYS-GUI-001`
- `SYS-GUI-002`
- `SYS-GUI-003`
- `SYS-GUI-004`
- `SYS-GUI-005`
- `SYS-GUI-006`

Recommended next:

- `SYS-GUI-007`

## Notes

- `test/system/os_desktop_integration_spec.spl` should be upgraded or replaced; in its current state it is still descriptive rather than milestone-grade proof.
- The best existing model for real GUI-output verification is `test/system/engine2d_in_qemu_spec.spl`, not the placeholder desktop integration spec.
