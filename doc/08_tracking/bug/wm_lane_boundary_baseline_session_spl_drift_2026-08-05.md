# WM lane-boundary baseline is stale for wm_showcase/session.spl — 2 undetected new violations

Found while landing task #85 (Lane W3 of `doc/03_plan/ui/wm_lane_boundary_ratchet_lanes.md`,
task #61 burn-down). Not caused by, or fixable within, W3's owns-list (W3 owns
`src/lib/nogc_sync_mut/play/wm/mod.spl`, `src/lib/common/ui/window_scene_draw_ir.spl`,
`src/lib/common/ui/wm_full_stack_demo.spl`, `src/os/services/wm/wm_codec.spl` --
`src/app/wm_showcase/session.spl` is not on that list).

## What

`sh scripts/check/check-wm-lane-boundary.shs` FAILs on a pristine checkout of
main at `c36ea0779cd1ba3bc47c5c4b54830327024804b8` (verified while rebasing
W3's commit onto that tip before push) with no W3 code changes contributing:

```
NEW VIOLATION src/app/wm_showcase/session.spl:45:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:55:WML001
FAIL — 2 NEW portable-lane violation(s); 196 total over 480 file(s) scanned
```

`doc/08_tracking/wm_lane_boundary_baseline.txt` currently lists only 3 entries
for this file (lines 21, 22, 32, all `WML001`). Lines 45 and 55 are:

```
45: use os.compositor.host_compositor_entry.{HostCompositor}
55: use app.ui.render.html_widgets.{render_html_tree}
```

`git blame` attributes both lines to `969c1f013c38` ("chore: sync
x25519mlkem768 web/browser and runtime migration"), one of ~34 commits that
landed on `main` between this session's working-copy base and its fetch of
the current tip -- i.e. this is ordinary, already-merged concurrent
development that never updated the WM lane-boundary baseline, the same class
of drift as
`doc/08_tracking/bug/wm_lane_boundary_baseline_stale_drift_2026-08-05.md`
(filed and resolved earlier the same day for `h1_client.spl` /
`wm_host_2d_simpleos.spl`), just a different file.

`HostCompositor` (6 uses) and `render_html_tree` (2 uses) both look
load-bearing in `session.spl` on a quick read -- this was NOT investigated
further, since `session.spl` belongs to a different owner.

## Why this isn't fixed here

- `src/app/wm_showcase/session.spl` is not in W3's (or any currently dispatched
  lane's) owns-list.
- Silently folding these into a regenerated baseline via `--write-baseline`
  would legitimize the drift instead of flagging it, exactly as the earlier
  bug doc argued.

## Repro

```
sh scripts/check/check-wm-lane-boundary.shs
```
(run against a tree at or descending from `c36ea0779cd1`, before any
subsequent fix)

## Next step

Whoever owns `src/app/wm_showcase/session.spl` should either route
`HostCompositor`/`render_html_tree` through the sanctioned WM host
interface/rendering lane, or add these 2 entries to the baseline as a
reviewed, deliberate addition -- not a silent regenerate.

## Resolution (2026-08-05, task #87)

Re-investigated as instructed (the filing above explicitly said this was NOT
investigated further). Confirmed both imports are genuinely load-bearing:

- `HostCompositor`: the `WmShowcaseSession.comp` field type (`session.spl:358`)
  and its construction via `HostCompositor.new_headless(...)`
  (`session.spl:377`) -- the session cannot exist without it.
- `render_html_tree`: called once, directly, to render the GUI window's HTML
  body (`session.spl:152`).

No sanctioned portable seam exists for either. The lint's single WM host
interface (`wm_host_interface_modules()` in `wm_lane_boundary_lints.spl`) is
scoped to `common.window_protocol.window_protocol` + `os.userlib.ipc_protocol`
-- the surface+event contract only -- and its own doc comment explicitly
excludes `os.compositor.display_backend_core` as "the host compositor's
backend, not the surface+event contract"; `host_compositor_entry` is the same
category. There is no portable equivalent of `render_html_tree` in any
scope-dir file either. Directly on point: `src/app/wm_compare/
production_gui_web_renderer_parity.spl` and `src/app/wm_compare/
production_gui_window_taskbar_widget_shells.spl` already baseline the
identical `render_html_tree` import, and `src/lib/common/ui/wm_chrome_theme.spl`
already baselines the identical `HostCompositor` import, for the same reason
-- `wm_showcase`, like `wm_compare`, is a host-side demo harness by design
(see the module's own top-of-file doc: "this module owns the WM session...
It adds no new WM/host seam -- it consumes the ones that already exist").

No code fix attempted: there is no existing sanctioned drop-in replacement,
and inventing new architecture for a demo entry point that already has direct
precedent for this exact exemption would be over-engineering for a 2-line
gap. Added as a REVIEWED, DELIBERATE baseline addition (not a silent
`--write-baseline` regenerate), with an explanatory `#`-comment immediately
above the two lines in `doc/08_tracking/wm_lane_boundary_baseline.txt`:

```
src/app/wm_showcase/session.spl:45:WML001
src/app/wm_showcase/session.spl:55:WML001
```

**Verification order, because origin/main had moved since this session's
local working copy was last synced:** built and gate-verified against a clean
`git archive origin/main` checkout (not the shared local working tree, which
carried unrelated concurrent-lane WIP on other `wm_compare` files at the
time) --

```
sh scripts/check/check-wm-lane-boundary.shs
PASS — 480 file(s) scanned, 196 violation(s), all in baseline (3 baseline entr(y/ies) now fixed)
```

**Sabotage (mandatory, run on the same clean tree):** reverting just the
2-line addition reproduces the exact original failure --

```
NEW VIOLATION src/app/wm_showcase/session.spl:45:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:55:WML001
FAIL — 2 NEW portable-lane violation(s); 196 total over 480 file(s) scanned
```

Restored, re-verified `PASS`.

Net baseline arithmetic for this addition alone: +2 entries. The pre-existing
3 stale `session.spl:21/22/32` entries (now "fixed (not in current scan)" per
the checker's own diagnostic) were left untouched -- out of this task's
2-line ownership scope.

Status: **closed**.
