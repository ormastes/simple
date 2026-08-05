# WM lane-boundary baseline is stale relative to main — 3 undetected new violations

Found while executing Lane W3 of `doc/03_plan/ui/wm_lane_boundary_ratchet_lanes.md`
(task #61 burn-down). Not caused by, or fixable within, W3's owns-list.

## What

`sh scripts/check/check-wm-lane-boundary.shs` FAILs on a pristine checkout of
main (verified at commit `826cb1bf785b602a6e16b78de660aa81b6f0ec4a` and again at
`5e03a0dd7398bb5801a066447eb8f4b9fb28534f` — identical result, no drift between
those two tips) **with no code changes from this lane applied**:

```
NEW VIOLATION src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:20:WML001
NEW VIOLATION src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:22:WML002
NEW VIOLATION src/os/services/wm/wm_host_2d_simpleos.spl:66:WML002
FAIL — 3 NEW portable-lane violation(s); 216 total over 468 file(s) scanned
```

`doc/08_tracking/wm_lane_boundary_baseline.txt` currently lists 219 entries, so
the visible count looks unchanged, but the *set* has drifted: some commit(s)
already landed on main added these 3 host-boundary violations without updating
the baseline, while (coincidentally, same count) some other 3 previously
baselined entries were independently fixed without baseline shrink. Net effect:
the gate has been silently FAILing on a plain scan of main since before this
session started, for reasons unrelated to any of the W1/W2/W3 lanes.

## Why this isn't fixed here

- `h1_client.spl` is explicitly W4's territory (`browser_engine net cluster`,
  deferred in the same plan doc — "h1_client 9" edges already expected there).
- `wm_host_2d_simpleos.spl` is not in any lane's owns-list (W1: lib timers: W2:
  wm_compare; W3: play/wm/mod.spl, common/ui, wm_codec.spl).
- Silently folding these into a regenerated baseline via `--write-baseline`
  would legitimize a real regression instead of flagging it — the ratchet
  exists specifically to catch this class of drift, not launder it.

## Repro

```
git archive 5e03a0dd7398bb5801a066447eb8f4b9fb28534f | tar -x -C /tmp/wm_check
cd /tmp/wm_check
SIMPLE_BIN=<repo>/bin/release/x86_64-unknown-linux-gnu/simple \
  sh scripts/check/check-wm-lane-boundary.shs
```

## Next step

Whoever owns `h1_client.spl` / `wm_host_2d_simpleos.spl` (or a future W4/adjacent
tranche) should either fix the 2 new host edges or add them to the baseline as a
reviewed, deliberate addition — not a silent regenerate.
