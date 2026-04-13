# SimpleOS Small Complete GUI Status

## Goal

Define the smallest GUI slice that is still meaningfully complete on the real x86_64 path.

For this repo, "small but complete GUI" should mean:

- one bootable desktop path with compositor, WM, shell, launcher, keyboard, and mouse wired together
- one real single-window launcher-spawned app (`Hello World`)
- one real multi-window launcher-spawned app (`Browser Demo`)
- stable launcher-owned `app_id` shared across launcher, WM, shell, and compositor
- close, terminate, and crash cleanup proven on the live desktop path
- one repeatable QEMU regression lane that exercises the real remote-window flow

This is intentionally narrower than "full desktop feature complete". It is the minimum slice that proves the GUI architecture actually joins up under process ownership.

## What Already Exists

### Real desktop boot path

- [desktop_e2e_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/desktop_e2e_entry.spl) now boots a minimal real desktop stack
- it launches `Browser Demo` through the shell and launcher
- it waits for two remote windows grouped under `/sys/apps/browser_demo`

### Real remote-window app paths

- [hello_world.spl](/home/ormastes/dev/pub/simple/src/os/apps/hello_world/hello_world.spl) has a built-in remote app runner
- [browser_demo.spl](/home/ormastes/dev/pub/simple/src/os/apps/browser_demo/browser_demo.spl) has a built-in remote app runner that creates multiple windows
- [launcher.spl](/home/ormastes/dev/pub/simple/src/os/services/launcher/launcher.spl) spawns those built-in app entrypoints and keeps launcher-owned process identity

### Identity and ownership joining

- [wm_service.spl](/home/ormastes/dev/pub/simple/src/os/services/wm/wm_service.spl) resolves missing window `app_id` from launcher process truth before falling back to title-derived identity
- [shell.spl](/home/ormastes/dev/pub/simple/src/os/desktop/shell.spl) drains WM actions in normal desktop runtime and avoids local placeholder windows for remote-owned apps
- launcher, WM, shell, and compositor now have a consistent path for remote window ownership by manifest app identity

### Scenario routing

- [qemu_runner.spl](/home/ormastes/dev/pub/simple/src/os/qemu_runner.spl), [cli.spl](/home/ormastes/dev/pub/simple/src/os/cli.spl), and [main.spl](/home/ormastes/dev/pub/simple/src/app/cli/main.spl) route `./bin/simple os run --scenario=x64-desktop-test` to the dedicated desktop test target

## System-Level Tests That Exist

### Relevant live or system specs

- [engine2d_in_qemu_spec.spl](/home/ormastes/dev/pub/simple/test/system/engine2d_in_qemu_spec.spl)
  - covers Engine2D/QEMU rendering path
- [os_desktop_integration_spec.spl](/home/ormastes/dev/pub/simple/test/system/os_desktop_integration_spec.spl)
  - covers broader desktop integration expectations
- [browser_engine_in_qemu_spec.spl](/home/ormastes/dev/pub/simple/test/system/browser_engine_in_qemu_spec.spl)
  - covers browser rendering path in QEMU
- [hosted_wm_system_test.spl](/home/ormastes/dev/pub/simple/test/system/os/hosted_wm_system_test.spl)
  - covers WM behavior in hosted mode

### High-value unit/regression coverage already added

- [shell_remote_window_spec.spl](/home/ormastes/dev/pub/simple/test/unit/os/desktop/shell_remote_window_spec.spl)
  - remote window grouping by launcher-owned app identity
  - launcher window-count updates
  - dead-process cleanup path
- [wm_service_metadata_spec.spl](/home/ormastes/dev/pub/simple/test/unit/os/services/wm/wm_service_metadata_spec.spl)
  - WM fallback from PID to launcher-owned app identity
- [launcher_spec.spl](/home/ormastes/dev/pub/simple/test/unit/os/services/launcher/launcher_spec.spl)
  - launcher process and window ownership behavior
- [window_spec.spl](/home/ormastes/dev/pub/simple/test/unit/os/userlib/window_spec.spl)
  - window client behavior relevant to remote-window creation

## Important Gap In Current Coverage

[desktop_e2e_test.spl](/home/ormastes/dev/pub/simple/src/os/test/desktop_e2e_test.spl) is still on the older synthetic path and still calls `wm_notify_app_launched()`.

That means the repo currently has:

- strong targeted unit coverage for identity and cleanup logic
- partial system coverage for graphics, desktop, and browser paths
- a newer real baremetal desktop entry that exercises the right launcher-driven flow
- but not yet one finished live regression lane that proves the full joined path end to end under the current desktop-test harness

## What Remains

### 1. Unblock the live desktop-test build

Current blocker:

- `./bin/simple os run --scenario=x64-desktop-test` reaches the correct target, but build execution is blocked by missing host toolchain support such as `llvm-objcopy`

Until this is fixed, the real QEMU lane cannot be treated as reliable regression coverage.

### 2. Align or replace the old desktop test harness

- update [desktop_e2e_test.spl](/home/ormastes/dev/pub/simple/src/os/test/desktop_e2e_test.spl) to match the real launcher -> WM -> shell path
- or retire it if [desktop_e2e_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/x86_64/desktop_e2e_entry.spl) is now the authoritative live lane

The current mismatch is a maintenance risk because the repo now has two different stories for the same desktop scenario.

### 3. Prove the minimum complete app set live

- live-launch `Hello World` as the single-window proof
- live-launch `Browser Demo` as the multi-window proof
- verify manifest-owned `app_id` grouping survives title changes and stays stable across compositor and WM ownership views

### 4. Prove cleanup behavior live

Need one live lane that shows:

- graceful app exit removes or invalidates owned windows correctly
- shell terminate path updates launcher state and removes owned windows
- crash path lands in `crashed` and does not leave orphaned ownership or stale grouped windows

### 5. Freeze one regression lane

Once the above is working, keep one debug-friendly desktop QEMU scenario as the stable regression target for:

- launch
- remote `create_window`
- identity join
- multi-window grouping
- exit / terminate / crash cleanup

## Recommended Order

1. Fix the host build/toolchain blocker for `x64-desktop-test`.
2. Make `desktop_e2e_test.spl` match the real launcher-driven path or delete the duplicate path.
3. Prove `Hello World` live as the minimum single-window app.
4. Prove `Browser Demo` live as the minimum multi-window app.
5. Add live assertions for graceful exit, terminate, and crash cleanup.
6. Treat that lane as the minimum complete GUI regression target.

## Overall Assessment

The architecture is close.

The repo already has most of the hard joining logic:

- launcher-owned process truth
- WM identity fallback
- shell-side reconciliation
- real remote-window app entrypoints
- a real desktop-test boot path

What is still missing is not another large design pass. The missing piece is one finished live-system proof that the current pieces work together under QEMU on the real path, plus cleanup coverage strong enough to call the GUI slice complete.
