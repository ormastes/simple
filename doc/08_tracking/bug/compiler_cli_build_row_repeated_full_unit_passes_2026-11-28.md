# compiler_cli_build matrix row: 263 full-frontend unit passes for one build, never fits any budget (2026-11-28)

- **Status:** root cause identified; mitigation shipped (adaptive unit batch cap
  16 -> 64); structural fix still open (shared/warm frontend across unit
  children — see "Options" below and
  `file_worker_batch_setup_dominates_self_build_2026-11-24.md`).
- **Area:** stage2/stage3 compiler-test matrix row `compiler_cli_build`;
  pure-Simple `native-build` per-file unit lane (`SIMPLE_FILE_WORKERS=1`,
  the default route).
- **Symptom:** the row has never completed within budget in any bootstrap
  lane: v6 ~18 h, v7c TIMEOUT at 6 h, v7i TIMEOUT at 12 h
  (`task=compiler_cli_build|result=TIMEOUT|status=124|elapsed_seconds=43205|max_rss_kib=2158716`;
  the low max_rss is the row wrapper — unit children do the work).

## Verdict up front

Not a cache-invalidation defect and not a retry loop. Every repeated
full-unit pass is one **per-file unit child process** doing its designed
job: the default per-file lane builds the full CLI as ~263 sequential
child processes, each of which re-runs the *entire* frontend over the
7,192-file / 4,207-module unit and then lowers **16 modules**. ~90-95% of
every child is setup. The HIR cache works (hits climb across children and
are never invalidated); the cost the cache cannot remove is the per-child
whole-inventory walk itself.

## Measured evidence

Logs: `build/bootstrap/pinned-src/pinned-<id>/.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log`
(one per lane, 82-100 MB each; counted with grep, never read whole).

Across all five preserved lanes (aarch64-unknown-linux-gnu):

| pinned src | unit children started | `[mir-shard] done` | modules lowered (sum claimed) | unit total | workers | batch |
|---|---|---|---|---|---|---|
| e803fa9762cd | 61 | 56 | 911 | 4,159 | 2 | 16 |
| 06ba866385d5 | 52 | 51 | 836 | 4,163 | 1 | 16 |
| 3dd00937c329 | 56 | 53 | 857 | 4,203 | 2 | 16 |
| 967f9178950e | 62 | 58 | 941 | 4,204 | 2 | 16 |
| f43f68c218ef (v7i, 12 h) | 63 | 61 | 989 | 4,207 | 2 | 16 |

Every lane dies at 20-24% of the modules. v7i rate: 61 finished children
in 43,205 s -> 4,207 modules / 16 per child = **263 children needed** ->
projection **~52 h** against a 12 h budget.

Per-child budget (v7i log, child elapsed_ms stamps; two workers interleave
one log, so stamps are per-process and were attributed per child):

- `phase=load_sources` re-reads **all 7,192 files, every child**:
  98-133 s (63/63 children, `cached=0` — source loading has no cache).
- `phase=hir` iterates **all 4,207 module rows, every child**
  (`unit_kind=modules total=4207`): 150-470+ s. HIR cache hits climb
  across children (cached=99 at child ~3 -> 1,400+ late in the lane) yet
  per-child HIR time does not drop — the walk, TLDR fallback parses and
  cache decode dominate, matching the cost model in
  `file_worker_batch_setup_dominates_self_build_2026-11-24.md`.
- TLDR fallbacks per child: ~180 modules re-parsed from source
  (lane totals: 11,388 `no-summary-surface`, 5,860 `multiline-string`,
  2,809 `no-sidecar`, 2,343 `class-without-interface-hir` fallback
  events). One recurring per-child summary-parse failure:
  `compiler/hir/hir_lowering/_Items/module_tldr_registration.spl line
  13:8: expected ), got Ident ...` in all 63 children (276 log lines) —
  cosmetic here (falls back to source load) but it is a TLDR-parser
  grammar gap worth its own look.
- Useful work per child: MIR lowering + codegen of 16 modules ≈ 30-60 s
  (`native_staged batch-1/batch-2`, `[codegen] 7/7 elapsed_s=13..19`).
- Child total: ~400-900 s (first child 801 s: 123 s load + 650 s
  parse/HIR + 28 s codegen). **~90-95% setup**, confirming the
  2026-11-24 doc's 95% figure at 2.6x the closure size.

## Mechanism (why the row does this)

1. The row runs `native-build --entry src/app/cli/_CliMain/main_and_help.spl
   --source src/{compiler,app,lib,os,plugins,compositions/...} --threads N`
   under `SIMPLE_BOOTSTRAP_STAGE3=1 SIMPLE_MIR_SHARDING=1`
   (`bootstrap-phase-verification.shs:1086-1132`). Route markers:
   `[stage3-route] per-file worker pool + per-module link`
   (`bootstrap_main.spl:690`).
2. The per-file pool is the **default build mode** (user build policy
   2026-11-04/05, `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "1"`,
   `native_file_worker_v1.spl:61`). Worker count is memory-clamped to 2
   here (`[file-worker] workers=2`; script requests
   `build_threads(4)/2` per tool row because compiler_cli_build and
   test_runner_build run concurrently,
   `bootstrap-phase-verification.shs:2692`).
3. Each worker loops `NativeFileUnitProcessInvokerV1.run_unit`
   (`native_build_main.spl:3668`): spawn ONE child per batch; the child
   picks its batch deps-first (`[file-worker] unit picked=16`,
   `driver_source_parse_streaming.spl:228`), builds HIR, lowers MIR,
   emits objects, seals the ledger, exits.
4. Batch size: `SIMPLE_FILE_WORKER_BATCH` is unset in the row, so the
   adaptive plan applies: `closure/(workers*4)` = 4207/8 = 525, **clamped
   to `NATIVE_FILE_WORKER_ADAPTIVE_BATCH_MAX_V1 = 16`**
   (`native_file_worker_v1.spl:272,283-290`). The "/4 rounds per worker"
   formula exists precisely to amortize per-child setup; the 16 clamp
   (written when per-child setup was believed cheap, "safely under
   3 GiB") destroys that amortization for any closure over 128 modules:
   263 children x ~450-550 s fixed setup each.
5. Nothing is shared between children: the `+fork-m<N>` owner suffix is
   only a name — no fork from a warm parent, so phase 1 (load_sources of
   7,192 files), the whole-inventory HIR walk, and the TLDR fallback
   parses repeat in full every time (root causes 1-3 in the 2026-11-24
   doc, unchanged).

So: by design, with a design parameter (16) that is pathological for the
largest unit in the repo. 63 children x ~485 s mean / 2 workers is
exactly the observed 12 h; 263 children is the projected ~52 h.

## Fix shipped with this record

`NATIVE_FILE_WORKER_ADAPTIVE_BATCH_MAX_V1`: 16 -> 64
(`src/compiler/80.driver/driver_build/native_file_worker_v1.spl`), spec
expectations updated
(`test/01_unit/app/cli/build_parallel_perf_mem_regression_spec.spl`).
The low-memory host cap (<= 24 GiB -> batch 4) is unchanged, as is the
explicit `SIMPLE_FILE_WORKER_BATCH` override.

Why 64 is defensible without a fresh measurement:

- Batch granularity is dropped from the native cache environment
  identity, so this changes scheduling only, not objects.
- Per-unit RSS is driven by the import-closure HIR decode, not the batch:
  the 2026-11-24 doc measured 6.6 GB at closure 462 and ~10 GB on late
  `compiler.mir` units at batch **8**; P4-v8 measured batch-32 units at
  7.8-9.6 GiB peak on a 24 GiB host (`p4_unit_whole_inventory_interface_
  index_2026-11-25.md`). The batch adds only the MIR/object residency of
  48 extra modules; sibling lanes already run 200
  (`NATIVE_MIR_FORK_BATCH_DEFAULT_V1`) to 263 (old shard claim cap
  ceil(4207/16)) modules per lowering process.
- The row's RSS watchdog stays authoritative and fails closed.

Expected effect (cost model, not measurement): 263 -> 66 children;
per child ~450-550 s fixed + ~64 x 2-3 s ≈ 620-750 s; 66 x ~685 s /
2 workers ≈ **6.3 h** — fits the 12 h row budget with margin, borderline
for a 6 h budget. Residual risk: unmeasured child RSS at batch 64 on the
aarch64 lane host; if the guard trips, set `SIMPLE_FILE_WORKER_BATCH=32`
for the tool rows (fits the P4-v8 measured envelope, ~10 h projected) —
that knob exists and needs no code change.

## Options still open (structural, ranked as in the 2026-11-24 doc)

1. Prove the PM3/TLDR route end-to-end and remove the remaining
   whole-closure HIR decode (options 1-2 there): attacks the ~450 s
   per-child fixed cost itself; needed to get the row comfortably under
   6 h and to stop paying 263x load_sources.
2. Warm parent, fork per round (option 4 there): phase 1 once per
   worker, ~44-133 s saved per child.
3. More workers for the tool rows: the host had 63 GiB free with a 39 GiB
   effective tree budget; `--threads` 2 per row is a script split, not a
   host limit.

## Verification status

- Log analysis only: counts and timings above are grep/awk measurements
  over the five preserved lane logs; no bootstrap lane was run for this
  record (a lane was live on the host).
- The constant change is covered by the updated unit spec; no full
  native-build was run (forbidden while the lane is active). The next
  bootstrap lane is the end-to-end check: success = `compiler_cli_build`
  PASS inside its timeout with ~66 unit children in the row log.
