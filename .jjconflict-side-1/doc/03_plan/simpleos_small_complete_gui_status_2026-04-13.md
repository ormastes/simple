# SimpleOS Small Complete GUI Plan

## Goal

Define the smallest x86_64 SimpleOS milestone that is honestly complete as a GUI OS on the real QEMU framebuffer path.

For this repo, "small complete GUI OS" means:

- one repeatable `x86_64` QEMU boot path that lands in the desktop without relying only on hosted mode
- one usable desktop shell with compositor, WM, launcher, taskbar or dock, keyboard, and mouse active together
- one single-window real app and one multi-window real app launched through the real launcher path
- stable app ownership across launcher, shell, WM, and compositor
- close, terminate, graceful exit, and crash cleanup proven on the live desktop path
- one real GUI-output regression lane based on QEMU framebuffer capture, not just serial logs

This is intentionally narrower than "full feature-complete desktop OS". It is the minimum bar for saying SimpleOS is a complete GUI OS in a small but credible form.

## Minimum Needed Features

### 1. Boot and platform

- `x86_64` GUI entry that boots under QEMU into the desktop path
- serial-enabled debug lane for the same GUI build
- one supported framebuffer path with repeatable resolution and stable boot markers
- build and run path wired through `bin/simple os build|run|test`

Current anchors:

- `examples/simple_os/arch/x86_64/gui_entry.spl`
- `src/os/qemu_runner.spl`
- `src/os/cli.spl`

### 2. Desktop shell

- shell initializes launcher, WM, compositor, app registry, and desktop chrome
- launcher can enumerate and start built-in GUI apps
- desktop shows a taskbar or dock and an app/window list
- shell can reconcile launcher state with remote windows

Current anchors:

- `src/os/desktop/shell.spl`
- `src/os/desktop/app_manifest.spl`
- `src/os/services/launcher/launcher.spl`

### 3. Window management and compositor

- create, focus, move, close, and destroy windows on the real desktop path
- z-order and active-window state are visible
- remote-window ownership is tied to stable launcher-owned `app_id`
- multi-window grouping works even when titles change
- cursor, decorations, wallpaper, and app content all render on the framebuffer

Current anchors:

- `src/os/compositor/compositor.spl`
- `src/os/compositor/desktop_chrome.spl`
- `src/os/compositor/app_content.spl`
- `src/os/services/wm/wm_service.spl`

### 4. Input

- keyboard events reach launcher and shell shortcuts
- mouse events reach compositor hit-testing and focus routing
- one launcher shortcut is proven on the real path

Current anchors:

- `src/os/gui/input_event.spl`
- `src/os/gui/shortcut.spl`
- compositor input handling in `src/os/compositor/compositor.spl`

### 5. Minimum app set

Required for the milestone:

- `Hello World` as the single-window proof
- `Browser Demo` as the multi-window proof
- one shell or terminal surface visible from the desktop stack

Useful but not required for the milestone:

- file manager
- editor
- settings
- calculator or clock

Rationale:

- the minimum bar is proving the GUI OS joins up under real process and window ownership
- a larger app catalog is valuable, but it should not block the first complete milestone

### 6. Persistence and file access

Minimum required:

- enough VFS or storage support for launcher and app startup to behave consistently
- no requirement yet for full disk-management UX before the milestone is declared complete

Required before claiming a broader desktop OS milestone:

- file manager backed by real storage
- write path verified on a real disk image or equivalent persistent medium

### 7. Debuggability and observability

- serial markers for boot, shell ready, launcher ready, app launch, window create, cleanup, and pass or fail
- QEMU QMP-based framebuffer capture path for visual assertions
- baseline artifacts stored for the visual lane

## What Already Exists

### Real desktop and app path pieces

- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` boots a real launcher-driven desktop test path
- `src/os/apps/hello_world/hello_world.spl` and `src/os/apps/browser_demo/browser_demo.spl` provide real remote-window app entrypoints
- `src/os/services/launcher/launcher.spl`, `src/os/services/wm/wm_service.spl`, and `src/os/desktop/shell.spl` already contain the ownership-join logic for launcher, WM, and shell

### Existing QEMU and GUI infrastructure

- `src/os/qemu_runner.spl` already exposes GUI and desktop test scenarios
- `src/os/compositor/qemu_capture.spl` already supports QMP screendump capture and PPM decode
- `test/system/engine2d_in_qemu_spec.spl` already proves the serial-marker-plus-framebuffer-compare pattern

### Existing useful coverage

- `test/unit/os/desktop/shell_remote_window_spec.spl`
- `test/unit/os/services/wm/wm_service_metadata_spec.spl`
- `test/unit/os/services/launcher/launcher_spec.spl`
- `test/system/browser_engine_in_qemu_spec.spl`
- `test/system/os/hosted_wm_system_test.spl`

## Remaining Gaps

### Gap 1. The desktop system spec is still placeholder-heavy

`test/system/os_desktop_integration_spec.spl` currently documents the intended system tests, but the assertions are still placeholders. It should not be treated as milestone proof until it becomes a real QEMU-backed spec or is replaced by a real one.

### Gap 2. `x64-desktop-test` is not yet the final GUI-proof lane

The scenario routing exists, but the current path still behaves like a serial-driven integration lane more than a full GUI-output proof lane. The milestone needs both:

- a serial assertion lane for fast diagnosis
- a framebuffer capture lane for visual proof

### Gap 3. GUI-output proof is split across unrelated specs

Right now the repo has real framebuffer capture proof for Engine2D and browser rendering, but not one explicit desktop-shell milestone test that captures the actual complete GUI OS result.

### Gap 4. Exit and crash cleanup are not yet proven end to end

Targeted unit coverage exists, but one live desktop scenario still needs to prove:

- graceful exit
- terminate from shell
- crash or nonzero exit cleanup

### Gap 5. Persistent-storage proof is still weaker than the GUI core

The first milestone can defer a rich storage UX, but any claim beyond "small complete GUI OS" needs real persistence validation on a disk image path.

## Required System Tests

The minimum system-test set for this milestone is:

### ST-001 QEMU GUI boot smoke

- boot the `x86_64` GUI target in QEMU
- assert serial markers for boot, shell-ready, and desktop-ready
- fail on `FAULT @`, panic, or timeout

### ST-002 Desktop shell join test

- assert launcher, shell, WM, and compositor all initialize on the real path
- assert at least one launcher shortcut is handled
- assert the desktop creates the expected root or chrome surfaces

### ST-003 Single-window app live test

- launch `Hello World` through the real launcher path
- assert launcher state, WM ownership, and one visible window agree on the same app identity

### ST-004 Multi-window app live test

- launch `Browser Demo` through the real launcher path
- assert at least two windows appear
- assert both windows group under one stable `app_id`
- assert title changes do not break grouping

### ST-005 Cleanup and lifecycle live test

- graceful exit removes or invalidates owned windows
- shell terminate updates launcher state and removes owned windows
- crash path lands in `crashed` and leaves no orphaned ownership

### ST-006 GUI framebuffer baseline compare

- boot a real QEMU guest with GUI enabled
- wait for a stable paint marker
- capture framebuffer with QMP screendump
- compare against a baseline with a tolerance profile

### ST-007 Disk-backed smoke for the broader OS claim

- boot with the intended disk-image path
- prove launcher and one app still work with the real storage-backed environment

This test is recommended for the next milestone, but it is not required to close the first "small complete GUI OS" slice if the GUI stack itself is otherwise proven.

## QEMU and GUI Output Test Strategy

### Lane A. Fast serial-only regression

Purpose:

- catch boot and integration regressions quickly
- keep failure output easy to diagnose

Expected path:

- `bin/simple os test --scenario=x64-desktop-test`

Assertions:

- serial markers only
- no framebuffer compare required

### Lane B. Real GUI-output verification

Purpose:

- prove the desktop really rendered on the guest framebuffer
- catch visual regressions that serial logs cannot see

Expected pattern:

1. boot GUI guest under QEMU with QMP enabled
2. wait for a paint marker that indicates the frame is ready
3. use `src/os/compositor/qemu_capture.spl` to capture the framebuffer
4. compare captured PPM against a checked-in baseline with an agreed tolerance profile

Recommended starting point:

- copy the structure of `test/system/engine2d_in_qemu_spec.spl`
- retarget it to the complete desktop-shell milestone entry rather than the Engine2D entry

### Lane C. Manual debug GUI lane

Purpose:

- inspect failures visually while keeping serial output available

Expected path:

- `bin/simple os run --arch=x86_64 --debug-gui`

### Baseline policy

- first capture or `UPDATE_BASELINE=1` should record the baseline artifact
- baseline updates require an intentional visual review
- the first desktop baseline should contain desktop chrome plus the minimum app proof state

## Recommended Execution Order

1. Fix the remaining host build and toolchain issues that block the real desktop lane.
2. Decide whether `src/os/test/desktop_e2e_test.spl` is upgraded or replaced by the newer real desktop entry.
3. Add a real `Hello World` live desktop test.
4. Add a real `Browser Demo` multi-window live desktop test.
5. Add live graceful-exit, terminate, and crash cleanup assertions.
6. Add one QMP framebuffer capture desktop spec and record its baseline.
7. Use the serial lane plus the visual lane together as the milestone gate.

## Out of Scope for This Milestone

- non-`x86_64` GUI parity
- polished typography or macOS-level visual quality
- large bundled app catalog as a release gate
- advanced storage management UX
- hardware validation beyond the supported QEMU path

## Exit Criteria

The milestone is complete when all of the following are true:

- `x86_64` GUI boot works reliably under QEMU
- desktop shell, launcher, WM, compositor, keyboard, and mouse are joined on the real path
- `Hello World` and `Browser Demo` both launch through the real launcher path
- single-window and multi-window ownership are stable by `app_id`
- graceful exit, terminate, and crash cleanup are proven live
- one serial regression lane passes
- one framebuffer capture regression lane passes
