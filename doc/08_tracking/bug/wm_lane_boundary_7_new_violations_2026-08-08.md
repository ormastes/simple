# Bug: wm-lane-boundary ratchet has 7 new uncaught violations

**Found**: 2026-08-08, via `scripts/check/check-wm-lane-boundary.shs` (an
unwired guard under triage in the guard-wiring campaign — currently nothing
runs this gate, so these violations have been silently accumulating).

## Symptom

```
NEW VIOLATION src/app/wm_showcase/session.spl:51:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:61:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:62:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:63:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:64:WML001
NEW VIOLATION src/lib/common/ui/window_scene_draw_ir.spl:196:WML002
NEW VIOLATION src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:40:WML001
FAIL — 7 NEW portable-lane violation(s); 131 total over 501 file(s) scanned
```

Ratchet baseline: `doc/08_tracking/wm_lane_boundary_baseline.txt`.
Scanner: `bin/simple run src/app/check/wm_lane_boundary_check.spl`.

WML001 = use of `fs`/`net`/`process`/`env`/`timers` outside the WM/GUI
portable lane. WML002 = raw platform `extern` outside the lane.

## Impact

These 7 sites have drifted past the recorded ratchet baseline with nothing
catching it — the exact "unwired guard = silent regression" failure mode this
guard-wiring campaign exists to close.

## Next step (owner decision needed)

Either:
1. Fix the 7 sites (`src/app/wm_showcase/session.spl` lines 51/61-64,
   `src/lib/common/ui/window_scene_draw_ir.spl:196`,
   `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:40`) to stay
   inside the portable-lane contract, or
2. Re-baseline `doc/08_tracking/wm_lane_boundary_baseline.txt` with an
   explicit, reviewed justification for each new entry.

Once resolved, wire `check-wm-lane-boundary.shs` into
`scripts/check/pre-push-conflict-tree-guard.shs` (fast, deterministic, no
hardware deps — it should already have been there per its own header).
