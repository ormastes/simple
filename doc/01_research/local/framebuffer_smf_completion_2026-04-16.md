<!-- codex-research -->
# Framebuffer + SMF Completion Research

Date: 2026-04-16
Scope: remaining work after desktop serial/editor lane reached green.

## Current green baseline

Verified locally:

- `bin/simple os test --scenario=x64-desktop-test` passes.
- The x86_64 desktop lane reaches:
  - `shell-ready`
  - `desktop-ready`
  - `paint-settle:done`
  - `remote-grouping:ok`
  - `editor-save:ok`
  - `cli-verify:ok`
  - `TEST PASSED`

This means the boot, launcher, compositor ownership, editor launch, and FAT32-backed persistence path are no longer the blocking issues.

## Remaining blocker 1: framebuffer QMP capture is still not live-green

### What is fixed already

- `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl` no longer crashes on `Option::None.len()` in baseline-read fallback logic.
- `src/lib/nogc_sync_mut/qemu/qmp_client.spl` now:
  - retries initial connect/greeting,
  - waits for concrete `return` / `error` replies,
  - no longer treats the first QMP line as the command reply.
- `src/os/compositor/qemu_capture.spl` now:
  - deletes stale capture files before screendump,
  - waits briefly for a fresh non-empty capture file,
  - falls back from JSON `screendump` to HMP `screendump`.
- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` now gives the framebuffer lanes longer post-marker capture windows.

### What still fails

These still fail live:

- `test/system/simpleos_desktop_framebuffer_spec.spl`
- `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`
- `test/system/engine2d_in_qemu_spec.spl`

Observed failure shape:

- serial marker wait succeeds on the desktop lane,
- QMP socket path exists,
- QMP client reaches connect attempts,
- but no screendump file is materialized,
- capture falls back to `0x0` / empty-file failure,
- compare path fails on missing or dimension-mismatch capture.

### Strong evidence

- The desktop serial/editor lane still passes under `-display none -vga std`.
- The framebuffer specs still fail to materialize a PPM even after:
  - moving output paths to `/tmp`,
  - waiting longer after marker points,
  - retrying connect/greeting,
  - reading true QMP replies,
  - trying both JSON `screendump` and HMP `screendump`.
- Flipping the framebuffer spec targets to `gui_mode: true` made the guest stop reaching the expected paint marker on this host, so that is not a safe completion path for CI-like headless environments.

### Working hypothesis

The remaining problem is not generic desktop rendering anymore. It is the host-side QEMU screenshot contract for these headless BGA lanes.

Most likely candidates:

1. `spawn_guest_with_qmp()` only waits for socket-file existence, not full QMP readiness or screendump readiness.
2. QEMU in the current headless `-display none -vga std` configuration may expose the control socket before the display surface behind `screendump` is actually usable.
3. The desktop specs and `engine2d_in_qemu_spec` still share the same fragile capture contract, so the failure is systemic rather than scene-specific.

## Remaining blocker 2: SMF test mode is still not a real execution lane

### Evidence in source

- `src/compiler_rust/driver/src/cli/test_runner/runner.rs:709-710`
  prints:
  - `"[INFO] SMF mode for tests not supported, using safe mode"`
- `test/baselines/simpleos_desktop_framebuffer/README.md:83-84`
  documents that `--mode smf` still falls back to safe/static behavior.
- `test/system/multi_mode_test_runner_spec.spl`
  still treats loader/SMF as an execution-mode distinction rather than a proven end-to-end compiled system-test path.

### Meaning

The framebuffer specs and the broader system-test lane cannot be considered harmonized across interpreter / safe / SMF until `--mode smf` actually executes the same test bodies rather than degrading to safe mode.

## Remaining blocker 3: framebuffer specs still contain duplicated logic

The bare desktop, with-apps, and engine2d QMP specs still each carry:

- local PPM writers,
- local baseline readers,
- local baseline bootstrap logic,
- local marker wait policy,
- local capture/compare sequencing.

This duplication is why fixes landed unevenly:

- the with-apps spec needed its own `Option::None` fix,
- the bare spec and with-apps spec diverged on capture paths and wait markers,
- engine2d still carries the old broken fallback pattern.

## Completion constraints

- Do not regress the green serial/editor lane.
- Do not require GUI-host display availability.
- Keep QEMU capture lanes deterministic and CI-capable.
- Make SMF an actual execution mode for tests, not a message plus fallback.

## Recommended completion direction

1. First fix the shared QMP capture contract once, below the specs:
   - `test/qemu/os/common/qemu_os_harness.spl`
   - `src/os/compositor/qemu_capture.spl`
   - `src/lib/nogc_sync_mut/qemu/qmp_client.spl`

2. Then deduplicate the framebuffer spec boilerplate into shared helpers so:
   - bare desktop,
   - with-apps desktop,
   - engine2d QMP
   all use the same baseline/capture/error contract.

3. Separately make SMF test mode execute real test bodies, then rerun the framebuffer specs in:
   - default mode,
   - interpreter mode,
   - SMF mode.
