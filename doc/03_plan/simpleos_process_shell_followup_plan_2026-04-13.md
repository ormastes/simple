# SimpleOS Process-Shell Follow-Up Plan

## Scope

This document captures the remaining work after the current process-shell implementation pass.

What is done:
- launcher now owns richer process truth, including stable app identity and exit classification
- WM/shell now carry process/app identity metadata instead of grouping purely by title
- shell now exposes process selection, focus, terminate, and relaunch actions
- `bin/simple os` dispatch is repaired and now reaches the real OS build/run path
- QEMU GUI mode now supports quiet default behavior plus an explicit debug-serial lane

What still remains:
- the real `bin/simple os build --arch=x86_64` lane times out in the underlying build path
- end-to-end desktop validation is still incomplete for real remote-window identity and exit cleanup behavior

## Remaining Items

### 1. Resolve `os build` timeout on the real x86_64 path

Current state:
- `./bin/simple os targets` works
- `./bin/simple os build --arch=x86_64` no longer fails silently
- the build now reaches `native-build` and fails with `Process timed out`

Why it matters:
- wrapper correctness is no longer the blocker
- the normal OS build lane is still not trustworthy for release or regression use

Required work:
- trace where the timeout occurs inside the `native-build` path
- determine whether the issue is compile latency, deadlock, repeated scanning, or a stuck subprocess
- add or tighten diagnostics so future timeouts identify the slow phase directly
- decide whether the fix is:
  - raising timeout for this lane based on measured reality
  - reducing avoidable work in the build path
  - fixing an actual stall or regression

Files likely involved:
- `src/os/qemu_runner.spl`
- `src/app/io/cli_compile.spl`
- `src/compiler_rust/driver/**`
- native-build implementation files reached from the CLI path

Acceptance:
- `./bin/simple os build --arch=x86_64` completes successfully, or
- it fails with explicit phase-level diagnostics instead of a generic timeout

### 2. Prove real remote-window identity handshake on live app paths

Current state:
- WM accepts an identity extension in create-window payloads
- userlib window client can now send process/app identity
- shell normalizes app identity back to launcher-owned process truth when available

Risk:
- not all real app paths may set the window client app identity before creating windows
- some apps may still arrive with fallback identity instead of manifest-backed identity

Required work:
- identify which app/window startup paths instantiate `WindowClient`
- ensure each launcher-spawned GUI app sets a stable manifest-owned `app_id`
- verify multi-window apps group by stable app identity even after title changes

Files likely involved:
- `src/os/userlib/window.spl`
- app entrypoints that create remote windows
- launcher-to-app startup seams where manifest identity can be injected

Acceptance:
- at least one real launched app with multiple windows groups under one process identity
- renaming a window title does not affect grouping
- shell/WM/compositor report the same process/app identity for owned windows

### 3. Verify end-to-end exit/crash cleanup on the real desktop path

Current state:
- launcher classifies `exited`, `crashed`, and `terminated`
- shell can reconcile dead-process windows and remove stale ownership records
- targeted unit coverage exists, but real runtime proof is still missing

Risk:
- runtime death notifications may still be incomplete for unexpected process loss
- stale windows may persist until shell reconciliation instead of closing immediately

Required work:
- validate graceful exit flow from a real launched desktop app
- validate forced terminate flow from shell process actions
- validate unexpected nonzero exit or crash path
- confirm that WM ownership records, compositor surfaces, and launcher counts all converge correctly

Files likely involved:
- `src/os/services/launcher/launcher.spl`
- `src/os/services/wm/wm_service.spl`
- `src/os/desktop/shell.spl`
- desktop runtime test harnesses

Acceptance:
- terminate from shell removes or invalidates owned windows without manual refresh
- graceful exit and forced terminate remain distinguishable in launcher state
- crash path lands in `crashed` and does not leave orphaned window ownership

### 4. Add live-system regression coverage for the desktop lane

Current state:
- targeted unit tests cover launcher state, WM identity parsing, and QEMU serial policy
- Rust driver tests cover `os` CLI dispatch
- live desktop/QEMU coverage is still thinner than the feature now requires

Required work:
- add one integration or system scenario for:
  - app launch -> process row appears
  - remote window create -> process/window identity matches
  - terminate -> windows removed and process state updated
- add a debug-friendly lane if serial assertions are needed while GUI is enabled

Files likely involved:
- `src/os/test/desktop_e2e_test.spl`
- `test/system/**`
- `test/qemu/os/**`

Acceptance:
- at least one live-system test covers launch, identity join, and exit cleanup together
- failures produce actionable serial or captured-log output

## Recommended Execution Order

1. Fix or characterize the `native-build` timeout on `os build`.
2. Audit real GUI app startup paths and ensure they set stable `app_id` before `create_window`.
3. Run live desktop validation for launch, multi-window grouping, terminate, and crash cleanup.
4. Convert the successful live validation path into regression coverage.

## Verification Checklist

- `./bin/simple os targets`
- `./bin/simple os build --arch=x86_64`
- targeted Simple specs for launcher, WM metadata, and QEMU runner
- Rust driver `os` dispatch tests
- one live desktop/QEMU scenario covering process identity and exit cleanup

## Exit Criteria

- normal `os build` path is trustworthy again
- real GUI apps consistently use launcher-owned app identity in WM/shell grouping
- process exit, terminate, and crash cleanup are proven on the live desktop path
- regression coverage exists for the critical joined process/window behavior
