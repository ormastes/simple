# Bug: `install_generated_simpleos_wm_theme` has zero production callers — its own comment contradicts that

**Date:** 2026-07-27
**Status:** closed — invalid (finding contradicted by working copy, 2026-07-28)
**Found:** side-finding while agents worked on other tasks, 2026-07-27
**Area:** OS compositor (`src/os/compositor/simpleos_wm_theme_bootstrap.spl`) — freestanding SimpleOS WM theme boot path
**Severity:** Medium — a feature believed present (the guest boot theme install) that cannot execute

## Finding

`install_generated_simpleos_wm_theme` is defined at
`src/os/compositor/simpleos_wm_theme_bootstrap.spl:11`:

```
# Freestanding-safe SimpleOS WM theme bootstrap owner.
#
# SimpleOS media does not carry the hosted package registry. Both canonical
# desktop entries install the exact generated snapshot before constructing
# their compositor so the first frame cannot observe Aqua defaults.

use common.ui.generated.aetheric_dark_theme_snapshot.{aetheric_dark_theme_render_snapshot}
use common.ui.theme_render_snapshot.{ThemeRenderSnapshot}
use common.ui.wm_chrome_theme.{apply_theme_render_snapshot_to_wm_chrome}

fn install_generated_simpleos_wm_theme() -> ThemeRenderSnapshot:
    # Unlike the hosted bootstrap, the boot image deliberately has no package
    # registry. Do not inherit a process-global selection either: that can be
    # a prior hosted/Aqua scene in an in-process test harness. The guest's
    # canonical desktop contract is the generated, manifest-stamped Aetheric
    # material from its first frame onward.
    val snapshot = aetheric_dark_theme_render_snapshot()
    apply_theme_render_snapshot_to_wm_chrome(snapshot)
    snapshot
```

The module-level comment (lines 3-5) explicitly asserts it is used at boot:
**"Both canonical desktop entries install the exact generated snapshot before
constructing their compositor so the first frame cannot observe Aqua
defaults."**

A repo-wide grep for `install_generated_simpleos_wm_theme` finds exactly one
hit: the `fn` declaration itself
(`src/os/compositor/simpleos_wm_theme_bootstrap.spl:11`). There is no caller
anywhere in `src/` — production or otherwise. The only other reference to
this function in the whole tree is a unit-test spec,
`test/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.spl:12,18`,
which imports and calls it directly to exercise the function in isolation —
this proves the function itself works, but a test-only caller does not wire
it into any boot path; it is not evidence the "canonical desktop entries"
claim in the comment is true.

Supporting evidence that the described callers don't exist: the actual
hosted desktop entry point, `src/os/hosted/hosted_entry.spl`, along with
`src/os/compositor/host_compositor_bootstrap.spl`, call
`install_default_host_wm_theme` / `install_host_wm_theme` from
`host_wm_theme_bootstrap.spl` instead — the *hosted* (package-registry-backed)
bootstrap path, not the freestanding generated-snapshot path this file
implements. No freestanding/guest entry point calling
`install_generated_simpleos_wm_theme` was found.

## Impact

The freestanding SimpleOS guest boot path has no code path that installs the
generated Aetheric theme snapshot before first frame, despite a
module comment asserting that contract is upheld by "both canonical desktop
entries." If the guest boot path relies on this function to avoid observing
"Aqua defaults" on first frame (per the comment's stated intent), that
guarantee currently does not hold — the function is well-formed and
unit-tested, but unreachable from any real boot entry point.

## Suggested fix

Either:
1. Wire `install_generated_simpleos_wm_theme()` into the actual freestanding
   SimpleOS desktop entry point(s) before compositor construction, matching
   what the comment already claims is true, or
2. If the intended callers were removed/renamed and the freestanding boot
   path now gets its theme some other way, correct the misleading comment at
   `src/os/compositor/simpleos_wm_theme_bootstrap.spl:3-5` and confirm via
   the guest boot path what (if anything) currently guards against observing
   default/Aqua theme colors on first frame.

This doc does not identify which freestanding entry point(s) are the
intended "canonical desktop entries" — that requires locating the current
SimpleOS guest boot/desktop-construction call sites, which was not resolved
during this verification pass and should be treated as unverified until a
follow-up locates them.

## Related

- `test/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.spl` — the
  only other reference to this function in the tree; a unit test, not a
  production caller.
- `src/os/compositor/host_wm_theme_bootstrap.spl` — the parallel *hosted*
  bootstrap path (`install_default_host_wm_theme`), which is actually called
  from `src/os/hosted/hosted_entry.spl` and
  `src/os/compositor/host_compositor_bootstrap.spl`.
- `doc/08_tracking/bug/theme_web_frame_acceptance_unguarded_2026-07-27.md` —
  a separate theme-identity gap found the same day in the same theme/WM
  subsystem.

## Resolution (2026-07-28)

Re-verified against the current working copy: **the "zero production
callers" finding does not hold.** `install_generated_simpleos_wm_theme` is
called from four real freestanding boot entry points, all wired into actual
build/QEMU-preflight scripts:

- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:296`
  (used by `scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs` and
  `check-simpleos-x86-64-wm-qemu-readiness.shs`)
- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl:339`
- `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl:130`
  (used by `scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs`
  and `check-simpleos-arm64-wm-qemu-readiness.shs`)
- `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl:73`

`git log -S` confirms these call sites are long-standing, not something
added after the bug was filed. The likely explanation is that the original
"repo-wide grep" was run against a torn/stale working copy — this same repo
has independent, contemporaneous history of a pushed jj-conflict-tree /
mass-file-deletion incident touching these exact files (see
`src/os/compositor/simpleos_wm_theme_bootstrap.spl` git log:
`37cda4befdc fix(vcs): restore main from pushed jj conflict tree`; and
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` git log:
`369a3725bbe revert: restore 13,174 files mass-deleted by e3e22d19da
torn-working-copy commit`) — so the `examples/` callers were transiently
absent from disk when the original grep ran.

**Action taken:** no code deletion, no rewiring — the function is live and
correctly used. Tightened the module comment at
`src/os/compositor/simpleos_wm_theme_bootstrap.spl:3-5` only: it previously
said "Both canonical desktop entries," which undercounts the four real
callers (x86_64 desktop + engine2d, arm64 desktop, riscv64 desktop); it now
names all four call sites by path so the comment can't drift out of sync
with the caller count again. The unit test
(`test/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.spl`) is kept —
it is a normal unit test for a function that also has real callers, not the
dead-code test this bug alleged.
