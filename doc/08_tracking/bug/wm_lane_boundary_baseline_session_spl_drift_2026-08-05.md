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
