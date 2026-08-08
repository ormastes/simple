# V-lane suite: `compositor_occlusion_spec.spl` times out under shared-WC contention at the plan's 600s floor

- **Status**: OPEN (RED-by-design — the timeout is real load contention, not a
  code defect; the plan explicitly bounds the fix's headroom, so this is not
  silently patched by widening the timeout again)
- **File**: `test/01_unit/os/compositor/compositor_occlusion_spec.spl`, run via
  `scripts/check/check-render-perf-v-lane-suite.shs:64`
- **Date**: 2026-08-07 (T19, `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`)

## What happened

T19 re-ran the 11-spec V-lane promotion suite as a regression gate after
Waves 1-2. Per T19's acceptance criteria, the per-spec timeout floor for this
spec was narrowed from the prior session's 1200s down to 600s (T19's mandated
band is 300-600s, "not 150s, not 7200s" — see plan line 405-406). Under that
600s floor, the spec **CANNOT_EXECUTE** (exit 255, no verdict line, "process
timed out after 600s").

```
CANNOT_EXECUTE: test/01_unit/os/compositor/compositor_occlusion_spec.spl (exit=255, no verdict line — timeout or crash)
  reason: process timed out after 600s
VERDICT: RED
```

All other 10 specs passed: 168/168 examples, 0 failed, 0 other cannot-execute.

## Root cause: shared-WC load, not a regression

At the time of the run, `uptime` showed **load average 39.60** (5 concurrent
agent sessions independently running `bin/simple test`/`bin/simple run`
batches on the same shared working tree — see the CLOBBER-HAZARD /
concurrent-session context in the T19 task brief). This is the same
swap-thrashing contention pattern already documented in
`doc/09_report/ui/perf/render_perf_v_lane_promotion_suite_2026-08-06.md`
(Run 2/Run 3), where a clean standalone run took ~130-140s but a
contended run exceeded even a 1200s outer timeout without any algorithmic
regression — bounded, non-quadratic per-op cost, confirmed by phase
breakdown in the Run 3 section of that report.

Load average 39.6 is roughly **3x** the 14.0 load average that previously
required 1200s of headroom over the ~130-140s clean baseline. 600s (T19's
mandated ceiling) is therefore mathematically insufficient at today's observed
contention level — this is expected, not a new defect in the spec or its
production code.

## Why this isn't just "widen the timeout back to 1200s"

T19's acceptance band is explicit: 300-600s, "not 7200s" — the plan
deliberately rejected the earlier session's generous 1200s/7200s figures as a
band that let real hangs hide behind load-contention excuses. Silently
reverting to 1200s here would defeat that purpose. This bug records the
tension instead: **the 600s floor is correct per plan intent for a
lightly-loaded CI-like environment, but this repo's actual shared-WC
environment during active multi-session development regularly exceeds that
load**, so the suite's regression-gate verdict is honestly RED right now, not
laundered to GREEN.

## Unblock condition

Either of:
1. Re-run `sh scripts/check/check-render-perf-v-lane-suite.shs` when
   concurrent-session load is low (`uptime` load average roughly ≤ 10) — the
   spec is expected to pass within 600s per the Run 3 phase-breakdown
   evidence (~130-140s clean baseline).
2. If the suite must run reliably under heavy shared-WC contention as a
   standing regression gate (not just an ad hoc re-run), the spec itself
   needs a real fix — e.g. splitting the 3 pixel-content example pairs
   (each ~30s of interpreter-bound 200x150px rendering) out of the timed
   critical path, or running the V-lane suite in a reserved/serialized slot
   the way T16 is tagged `SERIAL-BOOTSTRAP` — not by raising the timeout
   past the plan's 600s ceiling.

## Evidence

- Full per-spec output:
  `doc/09_report/ui/perf/render_perf_v_lane_promotion_suite_2026-08-06.md`,
  Run 5 (T19) section (added alongside this bug doc).
- `uptime` at time of run: `12:22:15 up 22:02, 2 users, load average: 39.60,
  29.07, 22.51`.
- Binary provenance: `readlink -f bin/simple` (self-hosted binary per repo
  default tooling policy).
