# HIR phase RSS grows ~6 MiB per module at scale (compiler_cli_build exit 88)

- **Status:** open (large-scale driver unidentified; see "Findings after diagnosis")
- **Found:** 2026-11-19, phase 2 bootstrap at `2cf8e62e41f`
- **Severity:** P1. Blocks phase 2 admission (`stage2-compiler-tests` row `compiler_cli_build`)
- **Budget check (failing spec):** `test/05_perf/compiler/hir/hir_rss_slope_budget.shs`

## Symptom

`compiler_cli_build` ran HIR serially in one process: `compiler_jobs=1`, `cap_bound=small-host-one-worker-temp`,
and no `[capsule-shard]`/`[hir-shard]`/`[mir-shard]` lines. The watchdog killed it with `status=rss-cap-exceeded`
(exit 88) at `max_rss_kib=18445275`, after 1808 of 3998 HIR modules and 12161 s of wall time.
Log: `stage2-compiler-tests/.../verification/logs/compiler_cli_build.log`.

## Measurement

Setup:
- stage2 `compiler.snapshot` from that run, invoked with `native-build src/app/cli/bootstrap_main.spl --low-memory --entry-closure`
  (closure of 1713 modules).
- `SIMPLE_FILE_WORKERS=0`, a fresh cache dir, and `SIMPLE_MEM_SNAPSHOT_FILE`.
- Each probe ran under an 8 GB ulimit and stopped at 1700 s.

| run | HIR modules | RSS at HIR start | fitted slope (`hir-post-store` rss vs modules) |
|---|---|---|---|
| boot | 217 | 3.59 GB | 5610 KiB/module |
| trim (`MALLOC_TRIM_THRESHOLD_=0 MALLOC_ARENA_MAX=2`) | 281 | 3.59 GB | 6102 KiB/module |

- **Not malloc fragmentation.** The trim A/B left the slope unchanged.
- **Where RSS moves, per module.**
  - `hir-file-start -> hir-post-lowering`: +16.6 MiB per module.
  - Ending the transient scope at `post-diagnostics`: -7 MiB.
  - Plus `post-store -> next file-start`: -1.6 MiB. Net retained: ~7.9 MiB per module, endpoint average over the boot run. The least-squares fit is 5.5-6.0 MiB per module.
- **What the retained size tracks.** It correlates with source bytes (r=0.59, ~0.5 KiB RSS per source byte, about 26x the
  source size) more than with `use` count (r=0.42). Function bodies dominate.
  - Largest single costs: `hir_codec.spl` 330 MiB, `driver_aot_native_output.spl` 178 MiB.
  - `semantic_prerequisite_hir_observation_v1.spl` costs 157 MiB for a 2.4 KB file. That is a first-touch memo cost,
    see "Findings after diagnosis".
- **`heap_live_bytes` in the snapshot cannot be used here.** It counts heap-registry header bytes only
  (`interpreter_extern/memory.rs` bit0). It moved about 1 MB per module.
- **Model check.** HIR-start floor 7.5 GB + 6 MiB x 1808 = 18.1 GB, against 18.4 GB measured.
  The 7.5 GB floor is the 3998-module closure, inferred from this check. The 3.59 GB in the table is the 1713-module probe closure. **Projected for 3998 modules: ~31 GB (straight-line extrapolation, unvalidated; see "Findings after diagnosis").** Fitting 16 GiB needs a slope of 2.2 MiB per module or less.

## Root cause (hypothesis; see "Findings after diagnosis")

Not shown to drive the slope. The target row takes the retained-owner route
(`lower_retained_surface_module`), not `lower_streaming_surface_source`.

- Every lowered `HirModule` is promoted to the persistent heap, bodies included:
  - `lower_streaming_surface_source` and `lower_retained_surface_module` both call `rt_transient_heap_promote(hir_module)`.
  - The module is then stored in `phase_hir_modules`.
- There is no collector, so a promoted module is never freed.
- In the tool rows, MIR runs in spawned shard workers: `BOOTSTRAP_PHASE_C_TOOL_MIR_SHARD_COUNT=8`. Each worker re-runs the
  frontend and needs bodies only for the modules it claims.
- The existing interface-only residency (`driver_mir_shard_hir_residency_v1.spl`, `SIMPLE_MIR_SHARD_INTERFACE_HIR=1`)
  applies only on HIR cache **loads**. With a cold cache, the process that lowers HIR keeps every body.

## Fix direction (parked, unmeasured; does not reach the target row)

The target row runs with streaming surfaces 0 and residency refuses
`bootstrap-flat-rows`, so this does not apply there as written.

When residency is armed (or MIR runs in spawned workers), handle each non-entry module whose HIR cache store succeeds like this:
1. Encode the module and store it to the HIR cache inside the paused transient scope (`hir_module_encode_retained_v1`).
2. Promote only `hir_module_interface_only_v1(hir_module)`.

The bodies then die with the scope, and the claim loop reloads them from the cache as it already does.
The ordering matters: today the store happens after promotion, so projecting after the store frees nothing.

## Re-export chase warnings (not a memory driver)

- The real log shows `[hir-callable-dep-origin-unresolved]` lines, for example:
  - `lib.nogc_sync_mut.io.sqlite_embedded` lacks `PureDatabase`;
  - `lib.nogc_sync_mut.test_runner.test_db_compat` lacks `TrdRunRecord` and `TrdTimingSummary`;
  - the `simple_web_html_layout_renderer*` modules lack `HNode` and `HtmlChildIndex`.
- The memos behind the chase are bounded by distinct names, not by importers, and they live in heap containers that
  grew less than 1 MB per module in total:
  - the phase memos on the loop-owned lowerer;
  - `_hir_reexport_impl_probe_budget=40`.
- These are facade correctness gaps for the module owners.

## Also does not fit: time

At 6.7 s per module serial, HIR for 3998 modules takes ~7.4 h against the 8 h row timeout.

## Findings after diagnosis (2026-11-19)

Ground truth stays the failed run: 18.4 GB at 1808 modules, ~6 MiB/module.
Nothing below explains that slope, and the budget gate is NOT re-based.

- **Retained bodies alone do not account for it.** A store-then-project fix
  (promote only the interface projection after a cache store) was written but
  is parked unpushed: it lives in `lower_streaming_surface_source` (reached only
  when `SIMPLE_MIR_SHARD_INTERFACE_HIR=1` re-enables streaming surfaces), while the
  target row runs with `SIMPLE_STAGE3_STREAMING_SURFACES=0` (retained-owner
  route) and residency also refuses `bootstrap-flat-rows`. Its benefit is
  unmeasured.
- **Spike mass is first-touch.** In the 216-module probe the per-module
  `hir-post-store` delta has median 0.6 MiB and 10%-trimmed mean 2.7 MiB; 32
  spikes above 20 MiB carry 2148 MiB, more than the net 1666 MiB. Eight tiny
  modules each importing `compiler.hir.hir_definitions` cost ~1 MiB each,
  after `hir_types.spl` paid +17 MiB once. The 157 MiB
  `semantic_prerequisite_hir_observation_v1.spl` is such a first touch.
  The small-probe median does NOT predict the large run, so no projection is
  derived from it.
- **Shared imported-surface memo: premise disproved.** Importing HIR types is
  ~1 MiB per importer, not ~35 MiB; the per-importer copies in
  `register_imported_symbol_selected_v1` are importer-local symbol entries.
- **The per-module symbol table must stay.** `module_snapshot()`
  (`hir_types.spl:397`) moves the containers by reference (no duplicate);
  `promote_symbol_table_transient_owners` only makes it the sole owner, and
  in-process MIR reads `module.symbols` across `src/compiler/50.mir/`.
- **Open:** the true large-scale driver. Next probe: a run long enough
  (>1000 modules) to fit the slope after first-touch saturation, with
  per-phase owners (symbol table, phase memos, frontend registries) sized
  separately.
