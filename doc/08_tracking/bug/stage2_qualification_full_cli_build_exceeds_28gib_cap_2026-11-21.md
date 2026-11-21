# Stage 2 qualification: single-thread full-CLI build exceeds the 28 GiB phase cap on a 60 GiB host

**Date:** 2026-11-21 · **Branch:** release/1.0.0 @ `0d8a3269bec` · **Host:** Linux x86_64, 64 CPU, 63,449,060 KiB RAM
**Status:** open

## Symptom

`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --jobs=full`
admitted Stage 2 (sha256 `cf238aa4e9538baff9d9d8212f97b964c7108689668eea82ed8f7164c3959f6b`,
sanity + provenance receipts published), then aborted in the phase
verification matrix:

```
Stage 2 compiler tests failed (status=88)
VERDICT — ABORTED: stage=stage2-compiler-tests exit=1
```

`compiler_version` passed. `compiler_cli_build` (entry
`src/app/cli/_CliMain/main_and_help.spl`, 4415-module closure, build-threads=1)
was killed by the process-tree RSS watchdog. Its log ends with no compiler
error at:

```
[build] phase=mir state=running ... done=0 total=4415 ... elapsed_ms=7136916 current=mir_setup:struct_prescan
```

## Evidence (watchdog receipt, `verification/campaign.*/process.env`)

```
status=rss-cap-exceeded        exit_status=88
max_rss_kib=29360128           peak_rss_kib=29383332
compiler_jobs=1                budget_ceiling_kib=58720256
cap_source=phase-policy        cap_bound=worker-floor
```

Policy line (`logs/<triple>/stage2-compiler-tests.log:1`):

```
cap 29360128 KiB = base 4194304 KiB + worker floor 16777216 KiB x 150% x 1,
host budget 31724500 KiB (host RAM 63449060 KiB x 50%)
```

## Analysis

- The cap is a formula over host RAM, and the watchdog samples only the
  qualification's own process tree. A concurrent provisional Phase 3/4 lane
  on the same host was outside that tree and did not change the cap or the
  measurement. The build alone exceeds 28 GiB.
- The tree was at about 19.5 GiB mid-HIR and crossed 28 GiB entering MIR setup
  (`struct_prescan`), before a single MIR module completed. The true plateau
  was not measured here. The same closure plateaued at 51,551,038 KiB on the
  MSVC lane (`rss_static_ceiling_52gib_request_2026-11-14.md`).
- The watchdog ceiling for this host is 58,720,256 KiB, so an explicit
  `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` up to that value is admissible,
  but the 50 % host-budget rule never selects it on a 60 GiB host.

## Consequence

On any host with less than roughly 2x the full-CLI plateau of RAM, Stage 2
qualification fails deterministically at `compiler_cli_build`, about two hours
in, with no compiler diagnostic and an empty `compiler_cli_build.max-rss-kib`.

## Next steps

1. Rerun the qualification alone on the host with an explicit cap near the
   ceiling to measure the real plateau on Linux.
2. Then either price the whole-build phase from the measured plateau, or cut
   the single-process footprint of MIR setup over the 4415-module closure
   (the actual defect: 28+ GiB before MIR starts).
3. Write the peak into `compiler_cli_build.max-rss-kib` on a watchdog kill so
   the failure names its cause.
