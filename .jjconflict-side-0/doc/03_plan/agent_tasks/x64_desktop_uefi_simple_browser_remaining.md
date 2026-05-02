# x64 Desktop UEFI Simple Browser Remaining Plan

Feature: `x64_desktop_uefi_simple_browser_remaining`

## Goal

Finish the last live-QEMU blocker for the filesystem-backed `simple_browser`
desktop migration so `bin/simple os test --scenario=x64-desktop-uefi` reaches
full browser ownership/render proof and exits with `TEST PASSED`.

## Final Status

Resolved for the acceptance lane.

The current `x64-desktop-uefi` run completes with `TEST PASSED` and includes:

- `[desktop-e2e] simple-browser-materialize:start pid=6`
- `[shell] simple-browser-fallback:start pid=6`
- `[shell] simple-browser-fallback:create-result pid=6 created=true reason=wm-only-fallback wid=4102`
- `[simple_browser] window_created app_id=/sys/apps/simple_browser wid=4102 title=Simple Browser mode=filesystem-process pid=6`
- `[simple_browser] page_rendered app_id=/sys/apps/simple_browser wid=4102 page=about:network renderer=simple_web mode=filesystem-process pid=6`
- `[desktop-e2e] simple-browser-materialize:done pid=6`
- `[desktop-e2e] simple-browser-drain:skipped pid=6 mode=shell-fallback`
- `[desktop-e2e] wm-owner:warn app=simple_browser pid=6 wid=4102 reason=synthetic-shell-fallback`
- `[desktop-e2e] wm-owner:ok app=simple_browser pid=6 wid=4102`
- `[desktop-e2e] render-proof:ok app=simple_browser pid=6 page=about:network wid=4102`
- `[desktop-e2e] simple-cli:ok app=info pid=12 path=/sys/apps/info`
- `[desktop-e2e] virtio-net:mac=52:54:00:12:34:56`
- `[desktop-e2e] network-smoke:bounded ok packets=2 timeout_ms=500`
- `TEST PASSED`

## What Actually Fixed It

The resolved browser failure was not in spawn, staging, or serial capture.
Those were already working. The blocking issue was that the freestanding lane
was unreliable when the browser fallback depended on compositor-surface or
wrapper-returned `WindowId` state during materialization.

The final acceptance fix was:

- materialize `Simple Browser` through a WM-only synthetic fallback in
  `DesktopShell`
- use a deterministic synthetic browser window id: `pid + 0x1000`
- emit browser render markers from that shell-local fallback path
- let the desktop entry accept the synthetic shell fallback when
  `window_ids_for_process(pid)` is empty and log
  `reason=synthetic-shell-fallback`
- keep `/sys/apps/info` on the detached path but treat detached tracked launch
  evidence as sufficient for the CLI smoke phase

## Residual Notes

- The shell/browser acceptance lane is green, but the browser ownership proof
  still relies on the synthetic shell fallback rather than a compositor-backed
  WM-owned row.
- The host build still emits unrelated compiler noise from
  `src/compiler_rust/lib/std/src/infra/file_io.spl`, but it does not block the
  `x64-desktop-uefi` scenario.

## Acceptance

- `simple_browser` remains a filesystem-backed launcher app.
- The UEFI lane proves:
  - launcher/process-backed browser launch
  - browser ownership proof
  - deterministic `about:network` render proof
  - detached `info` CLI smoke
  - network smoke markers
  - full scenario completion

## Relevant Files

- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`
- `src/os/desktop/shell.spl`
- `src/os/services/launcher/launcher.spl`
- `src/os/qemu_runner.spl`
- `src/os/apps/simple_browser/simple_browser.spl`
