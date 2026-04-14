# SYS-GUI-006 With-Apps Framebuffer Baseline — Resume Checklist

**Owner:** Agent zeta (with-apps variant)
**Spec:** `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`
**Baseline dir:** `test/baselines/simpleos_desktop_with_apps_framebuffer/`
**Tag:** `@tag:pending_until_shortcut_fix`
**Status at 2026-04-14:** PENDING — blockers not landed during Agent zeta's slice

> **Round-10 update (2026-04-14):** The shared interpreter blocker
> (`semantic: method X86_64 not found on type Architecture`) is now
> **CLEARED** by commit `e516e2a0f484 fix(interpreter): add GLOBAL_ENUMS
> fallback for cross-module enum variant lookup`. The with-apps spec is
> still PENDING because the live-boot blockers below (shortcut:fail /
> launcher:fail) remain active and still gate
> `[desktop-e2e] remote-grouping:ok`. See
> `doc/08_tracking/todo/sys_gui_006_round10_status_2026-04-14.md` for
> the bare-lane verification evidence and Blocker 2 handoff details —
> the same OS-side fix will unblock both variants.

## Blockers (from Agents alpha + beta)

Both blockers must land before this spec can capture a real baseline:

1. Module-level array storage bug (baremetal global arrays) — Agent alpha
2. Cross-module `val` constant evaluation bug — Agent beta

Downstream symptom: desktop entry path emits `[desktop-e2e] shortcut:fail` /
`launcher:fail` and never reaches `[desktop-e2e] remote-grouping:ok`, so the
spec's serial-marker wait times out at 60s and takes the documented
PENDING skip path.

In addition, on 2026-04-14 the spec fails in interpreter mode with
`semantic: method X86_64 not found on type Architecture` coming from
`get_desktop_browser_target()`. The sibling bare-desktop spec
(`test/system/simpleos_desktop_framebuffer_spec.spl`) fails with the same
error, so this is a shared upstream state that the blocker fixes are
expected to clear along with the live boot. Do NOT try to fix it from the
with-apps spec side.

> **Round-10 update:** The `Architecture.X86_64` interpreter error
> described in the preceding paragraph is CLEARED on `main@origin`. The
> live-boot blockers #1 and #2 above remain active.

## Tolerance Profile Decision

**Chosen:** `profile_wm_default`
**Rationale:**
- Inherits text-region relaxed thresholds (threshold 10, YIQ 0.35) which
  cover Browser Demo + hello_world rendered text AA variance.
- Keeps solid-region strict gate (threshold 2, min_match_pct 9990) for
  the desktop chrome underneath the app windows.
- Whole-scene gate in the spec is `cmp.match_percentage >= 9500`
  (i.e. 95%), matching the with-apps contract. This is loose enough
  for rendered app content but strict enough to catch real regressions.
- Keeps parity with the bare-desktop spec so both variants share a
  profile and diffs between them are attributable to app rendering,
  not tolerance tuning.
- `profile_text_tolerant` would also work but its default_threshold is
  8 across the whole scene — strictly more permissive than needed
  given the spec's 95% whole-scene gate already compensates. Prefer
  `profile_wm_default` for stricter chrome checking.

If post-unblock recordings show <95% similarity between two fresh
captures, the fallback ladder is:

1. Keep `profile_wm_default`, investigate non-deterministic region
   (cursor, clock, animation frame) and mask it.
2. Switch to `profile_text_tolerant` (wider default threshold).
3. Add a settling wait between `remote-grouping:ok` and capture.

## Resume Commands (run in order)

```bash
cd /home/ormastes/dev/pub/simple

# 1. Verify blockers landed (look for alpha/beta commit descriptions)
jj log --no-graph -T 'description.first_line() ++ "\n"' --limit 20

# 2. Rebuild x86_64 SimpleOS
bin/simple os build --arch=x86_64

# 3. Run the desktop scenario live and grep for the unblocked marker
bin/simple os test --scenario=x64-desktop-test 2>&1 | tee /tmp/x64-desktop.log
grep 'remote-grouping:ok' /tmp/x64-desktop.log
# Expected: [desktop-e2e] remote-grouping:ok

# 4. If remote-grouping:ok appears, capture the with-apps baseline
UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_with_apps_framebuffer_spec.spl

# 5. Validate the captured PPM
ls -la test/baselines/simpleos_desktop_with_apps_framebuffer/desktop_with_apps_scene.ppm
# Expected: > 10000 bytes
head -c 40 test/baselines/simpleos_desktop_with_apps_framebuffer/desktop_with_apps_scene.ppm
# Expected: P6\n<W> <H>\n255\n

# 6. Record two fresh comparisons back-to-back for determinism check
bin/simple test test/system/simpleos_desktop_with_apps_framebuffer_spec.spl --no-cache
bin/simple test test/system/simpleos_desktop_with_apps_framebuffer_spec.spl --no-cache
# Expected: both runs print >= 95% match, both pass

# 7. Remove the pending tag from the spec
# Edit test/system/simpleos_desktop_with_apps_framebuffer_spec.spl:
# - Delete line  "# @tag:pending_until_shortcut_fix"
# - Update the header comment block to drop the "intentionally gated"
#   paragraph and the PENDING block in the it{} body (lines 146-162)
# - Retain the UPDATE_BASELINE instructions and tolerance rationale.

# 8. Commit on main (no branches, no push)
jj commit -m "test(sys-gui-006): capture with-apps desktop framebuffer baseline

Blockers from Agents alpha + beta landed; the desktop entry path now
reaches [desktop-e2e] remote-grouping:ok after shell launches the
default apps. Captured a real PPM baseline under profile_wm_default
with >=95% self-compare similarity across two fresh runs."
```

## Determinism Watchlist (post-unblock)

The with-apps scene contains rendered Browser Demo + hello_world windows.
Potential non-determinism sources to check during the two-fresh-runs
similarity test:

- Cursor position (if any mouse event is injected before the marker)
- Clock widget (if shell draws wall time)
- Animation frame phase (compositor easing, window slide-in)
- Font AA variance (already covered by text region tolerance)

The trigger marker `[desktop-e2e] remote-grouping:ok` is emitted AFTER
the compositor has drawn the windows and is the correct stable trigger.
If flakiness persists, see the fallback ladder above.

## Do NOT

- Fake a baseline. The spec fails loud rather than green-washing a
  missing capture, and that's the correct state.
- Touch `src/os/**`, `examples/simple_os/**`, `src/compiler_rust/**`,
  `src/os/compositor/qemu_capture.spl`,
  `src/os/compositor/tolerance_profile.spl`,
  `src/os/qemu_runner.spl`, or
  `test/qemu/os/common/qemu_os_harness.spl`. These are owned by other
  agents.
- Touch `test/system/simpleos_desktop_framebuffer_spec.spl` or
  `test/baselines/simpleos_desktop_framebuffer/` — Agent eta's bare
  variant.
- Create a git branch. Work lands on `main` via jj only.
