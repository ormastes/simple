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
