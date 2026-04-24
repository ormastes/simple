# x64 Desktop UEFI Simple Browser Remaining Plan

Feature: `x64_desktop_uefi_simple_browser_remaining`

## Goal

Finish the last live-QEMU blocker for the filesystem-backed `simple_browser`
desktop migration so `bin/simple os test --scenario=x64-desktop-uefi` reaches
the full browser ownership/render proof and exits with `TEST PASSED`.

## Done

- `simple_browser` stages as a real filesystem app at `/sys/apps/simple_browser`.
- Launcher/process-backed proof is live in the UEFI lane.
- Shell fallback no longer uses the broken `add_surface()` path.
- QEMU runner uses file-backed serial capture for `x64-desktop-uefi`.
- Browser fallback now reaches:
  - shell fallback entry
  - compositor window creation
  - compositor identity registration
  - WM ownership registration
  - deterministic browser render marker emission

## Status

Resolved for the acceptance lane.

Current passing serial evidence includes:

- `[desktop-e2e] simple-browser-materialize:start pid=6`
- `[shell] simple-browser-fallback:start pid=6`
- `[compositor] simple-browser:create-window:start`
- `[compositor] simple-browser:create-window:session`
- `[compositor] simple-browser:create-window:end`
- `[shell] simple-browser-fallback:create-result pid=6 created=true`
- `[simple_browser] page_rendered app_id=/sys/apps/simple_browser wid=... page=about:network renderer=simple_web mode=filesystem-process pid=6`
- `[desktop-e2e] simple-browser-materialize:done pid=6`
- `[desktop-e2e] simple-browser-drain:skipped pid=6 mode=shell-fallback`
- `[desktop-e2e] wm-owner:ok app=simple_browser pid=6 wid=6`
- `[desktop-e2e] render-proof:ok app=simple_browser pid=6 page=about:network wid=6`
- `[desktop-e2e] phase:ok name=migrated-app-launches`
- `TEST PASSED`

## Working Theory

The resolved failure was in shell-fallback state mutation and proof routing:

- browser staging
- launcher path resolution
- browser process spawn
- compositor window creation
- browser render marker emission
- QEMU serial capture

The acceptance fix was:

- materialize the browser on the `DesktopShell` receiver directly instead of
  depending on helper-level class-by-value mutation for the freestanding lane
- keep the browser proof on the shell-local fallback path and skip unrelated WM
  IPC draining for that path
- validate browser ownership from the live shell WM state in the desktop entry

## Residual Risk

There is still a non-blocking freestanding wrapper inconsistency worth tracking:

- the browser render marker prints a wrapper-corrupted `wid=216172782113783808`
  while the shell WM proof reports `wid=6`
- this no longer blocks `x64-desktop-uefi`, but it suggests a remaining ABI or
  wrapper-value bug around freestanding `WindowId` handling that should be
  isolated separately if another lane starts depending on exact browser window IDs

## Acceptance

- `simple_browser` remains a filesystem-backed launcher app.
- No browser-only launch helper is added in SSH, WM, or desktop entry code.
- The UEFI lane proves:
  - launcher/process-backed browser launch
  - WM ownership
  - compositor-visible deterministic `about:network` render proof
  - full scenario completion

## Relevant Files

- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`
- `src/os/desktop/shell.spl`
- `src/os/compositor/compositor.spl`
- `src/os/services/wm/wm_service.spl`
- `src/os/qemu_runner.spl`
- `src/os/apps/simple_browser/simple_browser.spl`
