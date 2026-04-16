## Framebuffer + SMF Completion Plan

Date: 2026-04-16
Goal: finish the remaining non-green test lanes without regressing the working x64 desktop serial/editor path.

### Phase 1: Fix the shared QMP capture contract

Files:

- `test/qemu/os/common/qemu_os_harness.spl`
- `src/os/compositor/qemu_capture.spl`
- `src/lib/nogc_sync_mut/qemu/qmp_client.spl`

Work:

1. Replace socket-file-exists polling with a real QMP-ready probe.
   - `wait_for_qmp_socket()` should not stop at filesystem existence.
   - It should verify a connect + greeting + capabilities round-trip before the harness returns success.

2. Separate “QMP control ready” from “capture file ready”.
   - `capture_qemu_vm()` should return immediately on QMP command failure.
   - It should only proceed into decode when a new file is confirmed present and non-empty.

3. Add one diagnostic branch that records which step failed:
   - socket absent,
   - connect/greeting failure,
   - capabilities failure,
   - screendump command failure,
   - output file missing,
   - output file empty,
   - PPM decode failure.

Acceptance:

- `test/system/engine2d_in_qemu_spec.spl` produces a real non-zero-sized capture or fails with a precise shared capture error.
- No spec should continue into compare/bootstrap logic after a failed capture.

### Phase 2: Unify framebuffer spec behavior

Files:

- `test/system/simpleos_desktop_framebuffer_spec.spl`
- `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`
- `test/system/engine2d_in_qemu_spec.spl`
- optional shared helper under `test/system/gui/helpers/` or `test/qemu/os/common/`

Work:

1. Move duplicated helpers into one shared capture helper module:
   - local PPM write,
   - baseline read,
   - bootstrap-baseline creation,
   - compare branch,
   - capture failure handling.

2. Standardize capture markers:
   - bare desktop waits on `paint-settle:done`
   - with-apps waits on `remote-grouping:ok`
   - engine2d waits on its explicit frame-painted marker

3. Standardize capture output paths under `/tmp`.

4. Standardize failure behavior:
   - no `0x0` compare attempts after capture failure,
   - no baseline bootstrap on failed capture,
   - no stale file reuse.

Acceptance:

- All three QMP specs follow the same control flow.
- The with-apps spec no longer has unique fallback bugs.
- Engine2D and desktop lanes fail or pass for the same shared reasons.

### Phase 3: Make SMF a real test execution mode

Files:

- `src/compiler_rust/driver/src/cli/test_runner/runner.rs`
- nearby test-runner mode/execution files under `src/compiler_rust/driver/src/cli/test_runner/`
- relevant std test-runner files under `src/lib/nogc_sync_mut/test_runner/`

Work:

1. Remove the current fallback behavior at:
   - `runner.rs:709-710`
   where SMF mode prints “not supported” and degrades to safe mode.

2. Make `--mode smf` actually:
   - compile test modules to SMF,
   - execute test bodies through the intended compiled path,
   - preserve timeouts and result reporting.

3. Ensure system specs that spawn subprocess/QEMU still work from SMF mode.

Acceptance:

- `bin/simple test --mode smf test/system/simpleos_desktop_framebuffer_spec.spl`
  runs a real body, not a safe-mode fallback.
- Same for the with-apps framebuffer spec and one simpler system spec.

### Phase 4: Re-verify all lanes

Required runs:

1. `bin/simple os test --scenario=x64-desktop-test`
2. `bin/simple test --force-rebuild --timeout 180 test/system/simpleos_desktop_framebuffer_spec.spl`
3. `bin/simple test --force-rebuild --timeout 180 test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`
4. `bin/simple test --force-rebuild --timeout 180 test/system/engine2d_in_qemu_spec.spl`
5. `bin/simple test --mode smf --timeout 180 test/system/simpleos_desktop_framebuffer_spec.spl`

Success criteria:

- serial/editor lane remains green,
- all framebuffer lanes capture real non-black images,
- SMF mode executes the spec bodies directly,
- no stale-file or `Option::None.len()` fallback behavior remains.

### Ordering rationale

Do Phase 1 before anything else.

Reason:

- Framebuffer specs are still blocked by a shared capture contract problem.
- SMF harmonization does not help if the underlying QMP capture path still cannot produce a valid image.
- Once the shared capture layer is fixed, the spec cleanup and SMF enablement become much easier to verify.
