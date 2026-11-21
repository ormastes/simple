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

## Where the memory is: MIR setup is not the retainer (2026-11-21, later)

No code change accompanies this section. `struct_prescan` is the last progress
line, not the cause: the process is already near the cap when HIR finishes.

### Measurements

Fixture (76-module closure, `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 SIMPLE_PHASE_RSS=1`,
admitted Stage 2 built from `0d8a3269bec`, 6 GiB cgroup, one run, x86_64 Linux):

| phase marker | rss_kib | delta per module |
|---|---|---|
| process start | 55,096 | |
| `phase2:parse:done` | 359,700 | 4.0 MB (AST) |
| `phase3:hir_typecheck:done` | 558,640 | 2.6 MB (HIR) |
| `mir_setup:struct_prescan:start` | 559,308 | |
| `struct_prescan visited=64` | 581,424 | transient peak inside the phase scope |
| `struct_prescan:done` | 571,680 | 0.16 MB retained |
| `composite_inventory:done` | 572,776 | |
| first 8 modules lowered (`staged_codegen:batch:start`) | 748,784 | 22 MB (MIR) |
| `staged_codegen:batch:done released=8` | 1,247,780 | +62 MB, not returned |

All of MIR setup (`warm_names` through `composite_inventory`) retained 14 MB
for 76 modules, about 0.2 MB per module.

Two-pass shard lane, 1601-module bootstrap CLI, two MIR workers, 44 GB cgroup
(the run that hit the cgroup limit on 2026-11-21; figures are one worker's own
`rss_mib`):

- both workers ran HIR over the whole closure (`phase=hir done=1601 total=1601`
  appears twice; no `hir-residency` line, so the interface-only load was off);
- `[mir] 50/1601 rss_mib=13715`: 13.4 GiB resident before MIR has done
  anything material, about 8.6 MiB per closure module;
- `[mir] 1601/1601 rss_mib=16915`: +3.1 GiB across MIR, about 4 MiB per owned
  module (800 of 1601);
- about 21.7 GB per worker was observed during codegen. The log carries no RSS
  for that step, so the last ~4.8 GB is not attributed.

Scaled to this bug's 4415-module closure, 6.6 to 8.6 MB per module gives 27 to
35 GiB at the end of HIR. The 19.5 GiB mid-HIR reading fits the same line. MIR
setup at 0.2 to 0.3 MB per module adds roughly 1 GiB, enough to cross a cap the
process was already under by less than that.

### Ranked suspects

1. **Whole-closure AST and HIR are immortal** (about 6.6 MB per module on the
   fixture, 8.6 MiB in the shard worker). The runtime has no collector, so
   `self.ctx.modules = {}` after HIR
   (`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1822`) rebinds and
   frees nothing, and each `HirModule` is deep-promoted out of its scope
   (`:631`). Same finding as `full_cli_native_build_peak_rss_2026-11-13.md`.
2. **Every MIR shard worker holds the whole closure, not its own half.**
   Two workers held 2 x 13.4 GiB of the 44 GB budget before lowering a module.
   The interface-only load that fixes this exists but is opt-in and off
   (`driver_mir_shard_hir_residency_v1.spl:55`, `SIMPLE_MIR_SHARD_INTERFACE_HIR=1`),
   and it is refused on the retained HIR route (`:87`; it needs
   `SIMPLE_STAGE3_STREAMING_SURFACES=1`).
3. **Growth after MIR, in codegen** (unattributed 4.8 GB per worker; on the
   fixture a staged batch of 8 grew RSS by 499 MB and `released=8` returned
   none of it). See `codegen_module_memory_not_freed_per_module_2026_11_02.md`.
4. **Promoted MIR per owned module** (4 MiB per module in the worker, 22 MB on
   the fixture's first batch).
5. **MIR setup itself** (0.2 MB per module retained, plus a transient peak of
   similar size because each phase is one transient scope:
   `driver_pipeline_lowering.spl:1329-1336`, `:1400-1406`, `:1421-1427`).
   Chunking the phase scope would trim only that transient and reintroduces the
   quadratic promote cost described at `:115`.

Not retainers: `ctx.mir_feed_modules` (`driver_pipeline_lowering.spl:744`) and
`enum_inventory_modules` (`:1397`) are shallow copies sharing the HIR handles.

### Why no fix landed here

Nothing in MIR setup holds enough to matter, and suspects 1 to 3 cannot be
fixed by dropping a reference: memory returns only when a transient scope ends
without promoting, or through an explicit free. Each needs an aliasing proof
and a measured Stage 2 rebuild. The cheapest next step is a measurement, not a
patch: rerun the shard lane with `SIMPLE_MIR_SHARD_INTERFACE_HIR=1` and
`SIMPLE_STAGE3_STREAMING_SURFACES=1` and compare `[mir] 50/N rss_mib`. Until
then, price a MIR shard worker at about 8.6 MiB x closure modules + 4 MiB x
owned modules + codegen, not from its own share of the closure.

Unmeasured: the single-process 4415-module plateau on Linux, the codegen step
in the shard worker, and any effect of the interface-only flag on this lane.
