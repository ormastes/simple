# Self-hosted MIR lowering pathologically slow on the bootstrap_main closure (2026-10-22)

Status: OPEN — blocks the provisional stage3 self-recompile; worked around by
warm-cache retry grinds (per-module MIR artifacts persist in the native cache).

## Evidence

Lane: stage2 candidate (`simple.rejected`, release_phase3 @ ~4f41ac876d8 +
poll/future fix) compiling `src/app/cli/bootstrap_main.spl --entry-closure`
(1438 modules) with `--mode one-binary`:

- HIR phase: completes (~1438 modules, cacheable in minutes once warm).
- MIR phase: **4/1438 modules in ~18 minutes**, single-threaded worker,
  RSS pinned at exactly 32,324,452 KB across independent runs (an allocation
  cap; the worker thrashes against it), 0 `.mir` artifacts visible in the
  cache dir. Extrapolation at the observed rate is ~100 h — not viable.
- The same module set lowers through the seed-side pipeline in minutes
  (stage2 build: 1485 modules, whole build ~5 min at 20 jobs).

The first modules are the monolithic driver modules (compiler.driver et al.),
so per-module cost is front-loaded; lib modules may flow faster, but the four
largest already dominate.

## Impact

Stage 3 (self-host recompile) cannot complete in a sane wall-clock budget on
this host until either (a) MIR lowering runs with real parallelism/sharding,
(b) the pathological module(s) are profiled and fixed, or (c) the build is
decomposed into module groups whose MIR artifacts cache across retries.

## Next steps

1. Profile the candidate lowering `compiler.driver` (or whichever module the
   worker is stuck on) — the 32 GB RSS at the cap suggests an
   allocation-heavy path (candidate MIR retention/owner copying?).
2. Check whether `--threads` / MIR shard flags apply to the MIR phase of
   native-build (the hir shards exist; mir sharding may be behind an env or
   unimplemented).
3. Until then: stage3 evidence stays provisional; do not cite stage3 build
   times as qualification.

## Addendum: MIR sharding exists but is env-gated and unwired for ad-hoc lanes

`src/compiler/80.driver/driver_build/native_mir_shard.spl` implements full
MIR sharding (SIMPLE_MIR_SHARD=i/n, SIMPLE_MIR_SHARD_QUEUE, OWNER, LINK
ledger; largest-first LPT schedule; per-PASS sidecars feeding the link), and
`driver_aot_pipeline.spl` consumes it — but only when the environment schedule
is present. Nothing in the plain `native-build` CLI creates that schedule, so
an ad-hoc stage3 lane lowers MIR single-threaded. The wrapper's managed
stage3/stage4 lanes drive it; hand-driving it for the provisional lane
(coordinator + N shard workers + link worker) is the immediate lever for
~Nx throughput. The per-module pathological cost (32 GB RSS cap hit on the
first/largest driver modules) still needs a profile.

## Addendum 2026-10-22 (session 2): sharding wired for ad-hoc lanes; two more blockers found

1. `src/app/cli/native_build_main.spl` now defaults `SIMPLE_MIR_SHARDING=1` for
   ad-hoc lanes (opt out with `=0`; managed bootstrap lanes with
   `SIMPLE_BOOTSTRAP=1` unchanged). Shards engage without hand-driving the
   coordinator.
2. On macOS the fanout clamp degenerates to sequential: `shard_mem_available_kb`
   reads /proc/meminfo (Linux-only) → 0 → "unknown memory permits only the
   sequential path". Ad-hoc macOS lanes must declare
   `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` (e.g. 22000000 on a 24 GB host) to get
   parallel > 1. With 6 GB workers (`SIMPLE_MIR_SHARD_WORKER_KB=6000000`) the
   60%-usable rule yields parallel=2.
3. The shard eligibility guard (`native_mir_shard_eligible_v1` in
   `driver_aot_pipeline.spl`) refused the phase-3 lane with the opaque message
   "MIR sharding is unsupported for this build lane" and the coordinator fell
   back to in-process unsharded MIR (the ~100 h path). The guard now prints a
   per-condition refusal reason (`[mir-shard] eligibility refused ...`).
   Follow-up: whichever condition refuses the bootstrap_main dynload lane still
   needs a real fix (or an admitted narrower carve-out) — see the lane log for
   the recorded reason.
