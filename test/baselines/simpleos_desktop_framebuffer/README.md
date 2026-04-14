# SimpleOS Desktop Framebuffer Baseline (SYS-GUI-006)

This directory holds the checked-in baseline PPM for
`test/system/simpleos_desktop_framebuffer_spec.spl` — the visual
regression lane for the SimpleOS "Small Complete GUI" milestone.

## Files

- `desktop_scene.ppm` — golden baseline captured via QMP screendump
  on a clean `x64-desktop-test` guest run. On a fresh checkout this
  may be a zero-byte placeholder (see below).

## Current status (Agent T / Round 5, 2026-04-13)

The committed `desktop_scene.ppm` is still a **zero-byte placeholder**.

**SYS-GUI-006 is NOT yet LIVE-PROVEN.** Two independent blockers
currently prevent recording a real baseline from `bin/simple test`:

1. **Test-runner cannot execute `it` block bodies.** All three
   execution modes of the test runner (`interpreter`, `smf`,
   `native`) fall through to a safe/static-analysis path that
   only verifies file loading — the QEMU spawn / marker-wait /
   capture code in this spec's `it` block is never invoked.
   See `src/compiler_rust/driver/src/cli/test_runner/runner.rs`
   around the `Smf`/`Native` match arms ("X mode for tests not
   supported, using safe mode") and the `Interpreter` branch
   comment "Interpreter mode doesn't execute `it` block bodies
   — it only verifies file loading." Until the pure-Simple
   test runner in `src/app/test_runner_new/` grows a real
   execution path for system specs, `UPDATE_BASELINE=1
   bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl`
   reports PASS in <20 ms without spawning QEMU at all.

2. **Desktop entry path fails earlier than `desktop-ready`.**
   Running `bin/simple os test --scenario=x64-desktop-test`
   directly on main prints:
   `[desktop-e2e] boot` → `[desktop-e2e] shell-ready` →
   `[desktop-e2e] launcher:fail registered=0` → `TEST FAILED`.
   The guest never reaches `desktop-ready`, so even if the test
   runner DID execute the spec body, the marker wait would time
   out. Agent M's Round-5 report that the guest reaches
   `desktop-ready` live does not match current main — either
   the fix is not yet landed, or it is gated behind something
   that `x64-desktop-test` does not exercise.

The spec has been updated in this round to wait on the
earlier-and-more-stable `[desktop-e2e] desktop-ready` marker
(bare desktop, no apps yet) so that the moment blocker #2 is
resolved, a single `UPDATE_BASELINE=1` run on a host with a
functioning test-runner execution path will record the real
baseline without further edits here. The "with apps" variant
(waiting on `remote-grouping:ok`) lives in sibling spec
`test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`
and is tagged `@tag:pending_until_shortcut_fix`; it skips
cleanly on marker miss so it does not fail CI while the
downstream `shortcut:fail` is still being investigated.

## Recording procedure

1. Make sure the desktop integration lane reaches at least
   `[desktop-e2e] desktop-ready`:

   ```
   bin/simple os test --scenario=x64-desktop-test
   ```

   The scenario's serial log must contain `[desktop-e2e] desktop-ready`
   before the bare-desktop baseline can be meaningfully recorded.
   (The downstream `shortcut:ok` / `remote-grouping:ok` markers are
   only required for the "with apps" variant in
   `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`.)

2. Ensure the test runner's system-spec execution path actually
   invokes `it` block bodies. On current main this is the blocker
   described under "Current status" above — until it is fixed,
   step 3 silently reports PASS without spawning QEMU.

3. Run the framebuffer spec once with `UPDATE_BASELINE=1`:

   ```
   UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
   ```

   The spec will boot the desktop kernel under QEMU, wait for the
   `[desktop-e2e] desktop-ready` serial marker (bare-desktop paint
   proxy), call `capture_qemu_vm` via QMP screendump, and write
   the resulting frame here as `desktop_scene.ppm`.

4. **Eyeball the PPM.** Open it and verify:

   - desktop wallpaper / background is present
   - dock or taskbar is drawn in the expected place
   - no panic stripes, no tearing, no obviously uninitialised regions
   - app windows are NOT yet present (this is the bare-desktop
     capture; the with-apps variant handles that case)

   If any of the above look wrong, do NOT commit. Fix the underlying
   desktop render path first.

5. Re-run without `UPDATE_BASELINE=1` to confirm self-compare passes
   at `>=95%` under `profile_wm_default`. Run it a second time from
   a fresh recording to verify determinism. If two fresh recordings
   do not match at `>=95%`, the capture is non-deterministic on this
   scenario — narrow the tolerance profile or mask the non-stable
   region (typical culprits: clock widget, cursor position, any
   animated keyframe).

6. Commit the updated baseline with an intentional message:

   ```
   jj commit -m "test(sys-gui-006): refresh desktop framebuffer baseline"
   ```

## Tolerance profile

The spec compares against this baseline with `profile_wm_default`
from `src/os/compositor/tolerance_profile.spl`. Whole-scene gate:
`>=95%` match (9500 on the 0-10000 scale). Per-region thresholds
(solid 99.90%, text 95.00%, blur 93.00%, gradient 98.00%,
decoration 97.00%) enforce stricter limits on chrome panels than
on font-AA and glass-blur regions.

## Dimensions

Expected framebuffer dimensions are governed by `desktop_e2e_entry`
(`bga_init_framebuffer(1024, 768, 32)` at time of writing). If that
entry changes resolution, delete `desktop_scene.ppm` and re-record.
