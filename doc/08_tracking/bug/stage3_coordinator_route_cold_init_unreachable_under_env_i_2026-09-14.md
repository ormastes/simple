# Stage 3 coordinator route is unusable on a cold checkout: its own remedy cannot reach the child

- **Filed:** 2026-09-14
- **Status:** OPEN
- **Tree:** `origin/main` `4f4d0e12832`

## Symptom

Setting `SIMPLE_NATIVE_BUILD_THREADS=5` switches the Stage 3 resume to
`requested_route=coordinator`. On a checkout that has never built, it fails in
under two minutes with a one-line log:

```
SCV-E-ADMISSION: compile-event-journal-missing (first build in this checkout:
                 rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)
```

Re-running with `SIMPLE_SCV_INVENTORY_COLD_INIT=1` exported produces the
**identical** failure.

## Why the remedy cannot work

`scripts/bootstrap/resume-stage3-from-admitted.sh` states it twice in its own
comments (lines 577 and 603): the Stage 3 child runs under `env -i`, so an
outer variable never reaches it. Only variables the script explicitly bakes
into the invocation are forwarded — `SIMPLE_NATIVE_BUILD_THREADS` is one,
`SIMPLE_SCV_INVENTORY_COLD_INIT` is not.

So the error prescribes a fix that the script makes unreachable. The
coordinator route is therefore unusable on a cold checkout, and the
multi-threaded Stage 3 path is closed, by any means available to an operator.

## Second finding: the declared fallback never fires

Both failing runs recorded `requested_route=coordinator fallback_route=direct`
and then failed outright. The declared `direct` fallback did not engage. A
fallback that is recorded but never taken is worth a separate look.

## Not fixed here

Two candidate fixes — adding the variable to the forwarded allowlist, or having
the script cold-initialise the journal itself when it is missing — are both
behaviour changes to an admission-bearing script and were not made
speculatively. Measured on macOS arm64 (`hw.ncpu=10`), F74 round 3.


## Triage 2026-11-10 (p3-lib2 lane, work/p3-lib2-20261110)

**Verdict: SUPERSEDED — finding 1 (remedy unreachable) fixed in
`scripts/bootstrap/resume-stage3-from-admitted.sh`; finding 2 (fallback never
engaged) superseded by the route redesign. PR #7597, 2026-11-07.**

- Finding 1: the script now implements the doc's first candidate fix as a
  deliberate, single-variable pass-through (lines 931-976): the operator's
  `SIMPLE_SCV_INVENTORY_COLD_INIT` is validated to be exactly `1`, baked into
  the Stage 3 args hash (line 1003), and forwarded into all four `env -i` child
  invocations (lines 1041, 1054, 1082, 1091). The comment block cites this
  bug's exact F74 symptom ("identical SCV-E-ADMISSION ... with the variable
  set"). `sh -n` clean.
- Finding 2: the `requested_route=coordinator / fallback_route=direct` pair the
  doc observed no longer drives routing — the Stage 3 build path was
  redesigned (user policy 2026-11-05) to a per-file worker-pool coordinator
  (`src/app/cli/bootstrap_main.spl:284 run_bootstrap_native_build_coordinator`,
  positional route at 593-606). The coordinator "owns process/cache sharding,
  failure fallback, and MemAvailable fanout clamping" (bootstrap_main.spl:570);
  the env pair is still recorded on receipts for lineage only.
- Host-limit: a full cold-checkout Stage 3 coordinator run is not executable in
  this lane (no admitted Stage 2 + self-hosted binary chain on this Windows
  host); the script-level forwarding and the driver-side route ownership are
  the verified evidence.
