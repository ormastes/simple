# Per-file worker lane: ~95% of every batch is setup, not compilation (2026-11-24)

- **Status:** OPEN. Budget measured from logs; no code change shipped with this
  record (every fix that moves the number needs a build to prove object
  identity, and no build could be run on the host when this was written).
- **Area:** pure-Simple `native-build`, per-file unit lane
  (`SIMPLE_FILE_WORKERS=1`, closure-walk route `SIMPLE_UNIT_TLDR_IMPORTS=0`).
- **Symptom:** compiler self-build (1,611 modules, batch 8, 4 workers) runs
  ~30 batches/hour and takes ~7 hours.

## Measured budget of one batch child

Source: `~/.simple/prov/p3r/build.log.2w` (release-head source, 2 workers),
unit `owner=0/2@0+fork-m27`, a mid-round batch: 8 targets, 462-module import
closure. Stamps are the child's own `[BOOTSTRAP-PHASE] +<ms>` values.

| step | stamps | time |
|---|---|---|
| process start -> `phase1:load_sources:preclosed:admitted` | +0 -> +11646 | 11.6 s |
| read 2,173 sources (`seeded` -> `bulk:done`) | +13481 -> +25018 | 11.5 s |
| `owner_copy:done` -> `fingerprint:start` (manifest policies) | +26471 -> +41218 | 14.7 s |
| `phase1:load_sources:done` | +44373 | **44 s total** |
| `phase2:surface:closure:start` -> `missing-direct-edge-summary` | +45872 -> +277897 | **232 s** |
| `phase3:hir_typecheck:start` -> `phase3:hir:loop:done modules=470` | +279794 -> +438235 | **158 s** |
| `phase3:hir:cold_receipts` | +438449 -> +444325 | 5.9 s |
| `aot:mir_shard:start` -> `aot:staged_codegen:schedule` (MIR setup) | +444342 -> +458558 | 14.2 s |
| MIR lowering of the 8 targets -> `aot:verify_lowered_mir:start` | +458558 -> +467097 | 8.5 s |
| codegen + cache save (`[codegen] 8/8 elapsed_s=10`) | +467327 -> +482982 | 15.7 s |
| **total** | | **483 s** |

Work that belongs to the 8 targets: 8.5 s lowering + ~15 s codegen = **~3 s per
module**. Everything before `aot:staged_codegen:schedule` is setup: **458 s of
483 s = 95%**. In that batch the HIR cache reported
`hits=470 misses=0 stores=0` and `[hir-shard] ... lowered=0`: not one module was
lowered to HIR, yet the HIR stage took 158 s.

Whole-run medians agree (`~/.simple/prov/p3h/build.log.0750`, 195 batches,
4 workers, older pinned source): load 44 s, surface 173 s, HIR 190 s, MIR 24 s,
codegen 14 s, about 446 s per batch. Setup is about 91% of worker time, i.e.
roughly 22 of 24 worker-hours.

### Cost model

Three batches with different closure sizes give the split. The first two are
from one run, the third from another run on a different source snapshot, so
the slope is an estimate, not a fit:

| batch | closure modules | phase 2 |
|---|---|---|
| `p3r2/build.log.r1` `0/2 fork-m0` | 8 | 65 s (+150121 -> +215339) |
| `p3r2/build.log.r1` `1/2 fork-m0` | 102 | 88 s (+152663 -> +240445) |
| `p3r/build.log.2w` `0/2 fork-m27` | 462 | 232 s |

- fixed per process: ~44 s load + ~62 s phase-2 floor + ~6 s receipts + ~14 s
  MIR setup = **~125 s**;
- per closure module: ~0.25-0.37 s surface restore + ~0.34 s HIR cache load =
  **~0.6-0.7 s**, so ~300 s at the median closure of 461;
- per target module: ~3 s.

The "85 s fixed cost per batch" figure from 2026-11-22 is stale: the cost is
not fixed, it scales with the import closure.

### Parses versus cache adoptions

`[frontend-cache] hits=540 misses=0 parses=120` for that batch. Totals over the
195-batch run: 98,109 hits, 3,093 misses, 27,414 parses; HIR cache 85,739 hits
against 1,652 lowerings.

The constant **120 parses per process** are the visibility manifest policies
(one per `__init__.spl` manifest directory). They are deliberately uncached:
`parse_visibility_manifest_policy_v1`
(`src/compiler/80.driver/driver_source_parse_selected.spl:358`) calls
`parse_full_frontend_in_borrowed_scope_selected_uncached_v1` with the comment
"Policy provider provenance is from a fresh actual parse", reached from
`driver_source_pipeline_loading.spl:1576`. The same 120 appear in parse shards
(`parses=716 claimed=596`). They sit inside the 14.7 s `owner_copy:done` ->
`fingerprint:start` gap (about 3% of a batch), which also holds the per-row
manifest observation loop and the native source-interface index build; the
share of the parses alone is not stamped. They are an admission input, so
they are needed as the code stands; removing them means a content-addressed
policy projection, which is a policy decision, not a cleanup.

## Root cause

1. **One exec per batch.** `NativeFileUnitProcessInvokerV1.run_unit`
   (`src/app/cli/native_build_main.spl:3343`, spawn at `:3358`) starts a fresh
   `native-build --hir-shard=...` process for every round of the loop in
   `src/compiler/80.driver/driver_build/native_file_unit_loop_v1.spl:32`. The
   `+fork-m<round>` suffix in the owner name is only a name: nothing is forked
   from a warm parent, so no parsed state is shared copy-on-write. Each child
   repeats phase 1 for all 2,173 sources. The trait comment at
   `native_file_worker_v1.spl:544-550` records why: an in-process unit waits on
   parser state becoming per-context. (`SIMPLE_FILE_WORKER_REUSE` is unrelated:
   it names the incremental planner's object-reuse file, not process reuse.)
2. **Full surfaces for the whole import closure.** On the closure-walk route
   the phase-2 loop (`driver_source_parse_streaming.spl:353-431`, call at
   `:394`) restores a complete module surface for every closure module
   (`worker_mode == 1`) and a placeholder for the other ~1,700 rows.
3. **Full HIR, bodies included, for the whole import closure.**
   `driver_hir_pipeline_lowering.spl:1508` calls `hir_cache_load_parsed_v1` for
   every closure row. In `fork-m27`, 155.2 s of the 158.4 s HIR stage is spent
   before each row's `phase3:hir:file:start`, i.e. in that load; time follows
   module size (`hir_codec.spl` 6.1 s, `mir_data.spl` 6.0 s; 91 of 461 rows over
   0.5 s account for 113 s). Only the 8 targets are lowered to MIR; the other
   rows are declaration-only providers.

## Why the existing opt-in does not fix it

`SIMPLE_FILE_WORKER_INTERFACE_HIR=1` (PRs #11008/#11056) is an RSS fix, not a
time fix: `hir_cache_load_in_owned_scope`
(`src/compiler/80.driver/driver_hir_cache.spl:599`) decodes the full module and
only then strips bodies (`:660-664`, `hir_module_interface_only_v1`). The 158 s
decode is still paid. It must also stay opt-in:
`doc/05_design/compiler/perf/mir_shard_hir_residency_v1.md` records "Object
identity NOT established" (77 of 332 objects differed with no A-vs-A baseline)
and its spec is unrun. It is absent from the `worker_hir_profile_v1.spl`
environment allowlist, so a profiled worker refuses it. If it is ever added
there it must stay inside the environment fingerprint
(`native_build_environment_identity.spl` drops only per-batch variables such as
`SIMPLE_FILE_WORKER_BATCH`), because the flag can change objects.

The launch script sets `SIMPLE_UNIT_TLDR_IMPORTS=0` and gives no reason. The
default PM3 route it turns off parses only the picked files and binds imports
to TLDR summary surfaces (`driver_source_parse_streaming.spl:319`), which
removes item 2. It does not remove item 3: for each summary-bound import row
it still loads the provider's HIR through the same decode-then-strip path
(`hir_unit_import_interface_load_v1`, `driver_hir_cache.spl:1848`, called from
`driver_hir_pipeline_lowering.spl:1354`). That set is the unit's summary-bound
imports rather than the full transitive closure, so it should be smaller, but
by how much is unmeasured. `=0` is the documented workaround in
`per_file_unit_closure_incomplete_2026-11-22.md` ("for a compiler built before
the fix"); the related PM3 records
`per_file_unit_imported_global_missing_provider_2026-11-21.md` and
`per_file_unit_imported_class_method_origin_2026-11-22.md` are also "fixed in
source, not proven on a rebuilt compiler". None of the logs under
`~/.simple/prov` contains a PM3-route run.

## Options, ranked by expected effect

1. **Prove the PM3 route on a release-head compiler and drop
   `SIMPLE_UNIT_TLDR_IMPORTS=0`.** Removes the closure surface restore (~170 s
   of the measured 232 s) and shrinks the HIR load to the summary-bound
   imports. The floor is ~125 s + 3 s per module; the real figure lies between
   that and today's ~480 s and is unmeasured. No code change if the PM3 bugs
   above are really fixed; needs one self-build to prove it.
2. **Interface-only HIR cache projection.** Store a bodies-free entry next to
   the full one at HIR store time and load that for non-target rows, so the
   decode is skipped rather than performed and discarded. Removes most of the
   158 s. Blocked on the same A-vs-A / A-vs-B object-identity run the residency
   design already asks for.
3. **Larger batches.** Setup is per batch, so by the model above batch 32 costs
   about 125 + 0.7 x closure + 96 s. Even with the closure at its maximum
   (1,574) that is ~1,320 s per 32 modules against ~1,930 s for four batches of
   8. `SIMPLE_FILE_WORKER_BATCH` is an existing knob and the adaptive default is
   already 16 for this build (`native_file_worker_adaptive_batch_v1`); the
   measured runs set it explicitly and picked 8. Limit: child RSS grows with the closure (6.6 GB at 462
   modules, ~10 GB on late `compiler.mir` units), so the worker price has to
   follow. Unmeasured.
4. **Warm parent, fork per round.** Run phase 1 once per worker and fork the
   unit child after `phase1:load_sources:done`, before the pick. Saves ~44 s per
   batch (~9%). Needs the child to re-read queue state after the fork and a
   proof that no pid- or time-derived state is captured in phase 1.
5. **Round-0 duplicate graph scan.** In round 0 every worker runs the same
   `phase2:surface:admitted-graph` scan (+42756 -> +148805, 106 s) before its
   first pick. One-time, ~106 s per extra worker.

## Not located

The ~62 s phase-2 floor (present with an 8-module closure) has no inner stamps:
`log_module_surface_stage` / `log_module_surface_released`
(`driver_log_helpers.spl:425-429`) print without `+ms`. It is split between the
2,173-row loop and the post-loop work at
`driver_source_parse_streaming.spl:456-722`; which one is unknown.

## Verification status

Everything above is read from existing build logs and source. Nothing was
built or run. The per-option predictions come from the two-point cost model and
are not measurements.
