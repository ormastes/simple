# Full-CLI native-build peak RSS (~24 GB HIR, ~20 GB MIR), 2026-11-13

- Status: OPEN. Diagnosed from source and logs only (no rebuild, no live run).
  One small fix landed with this record (see "Landed fix"). The main retainer
  needs an ownership change that is too large and risky for a minimal diff.
- Lane: pure-Simple Phase 2 compiler, `native-build` of `src/app/cli/main.spl`.
  Settings: `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`, `SIMPLE_NATIVE_BUILD_THREADS=2`,
  HIR shard pool off. 3110 modules.
- Evidence log: `C:/dev/wt-lane2/build/diag-phase4/e_cli/build.log` (13 MB).
  For comparison, the MCP entry builds with the same settings in
  `.../diag-phase4/{d,e,f}_mcp/build.log`.

## What the log actually shows

1. **Two processes, not one.** `[mir-shard] shards=2 parallel=2` (log line 114).
   Each MIR shard worker runs the full frontend and HIR for all 3110 modules:
   - `phase=hir done=3110` appears twice, at lines 26524 and 43582.
   - `[mir-shard] worker source entry` appears at lines 29194 and 46141.

   The `[mir] N/3110` lines interleave both workers. Their `elapsed_s` values
   jump backwards at N=350 and N=950. Each `rss_mib` value is one worker's own
   figure, so the process-tree figure is roughly the sum of the two.
   Where this comes from: `src/app/cli/native_build_main.spl:1405-1435`. Ad-hoc
   lanes (`SIMPLE_BOOTSTRAP` != 1) turn MIR sharding on by default, and every
   worker re-derives the whole-program HIR.
2. **The second worker gets no HIR reuse.** The worker-2 HIR summary reports
   `cached=258` of 3110, and the HIR cache store reports `stored=0 refused=2816`.
   The refusal reason is
   `codec detail=nil_in_non_optional_scalar:HirExpr.is_uninit_marker`.
   Commit `c3bad7cd3f8` (2026-11-07) added `is_uninit_marker: bool` to
   `HirExpr` with no default (`src/compiler/20.hir/hir_definitions.spl:602`).
   About 200 `HirExpr(...)` constructors omit the field, so native code leaves
   it nil. The generated codec then refuses the whole module at
   `src/compiler/20.hir/generated/hir_codec.spl:3355-3357`. As a result, every
   MIR shard worker re-lowers HIR from scratch.
3. **The "released late" RSS drop is not a free.** On Windows, `rss_mib` is
   `WorkingSetSize` (`src/runtime/runtime.c:2527`, printed by
   `src/compiler/80.driver/driver_log_helpers.spl:461`). The OS trims a working
   set under memory pressure, and here two roughly 20 GB workers were
   competing for memory. A drop from 21.6 GB to 12.8 GB therefore does not
   show that the compiler freed anything. Commit charge (`PrivateUsage`) is
   the right metric. No code path was found that frees the HIR set or the AST
   set during MIR.
4. **Memory grows linearly with module count.** MCP builds 282 modules at
   ~2.0 GB. CLI builds 3110 modules at ~24 GB. Both come to about 7.5 MB per
   module. That points to whole-closure retention, not one leaking step.

## Why "drop the reference after last use" does not help here

The native runtime has no GC and no refcount for ordinary values
(`src/runtime/runtime_native.c:9775`). An object is freed in only five ways:

- a transient scope ends without promoting it;
- `rt_string_free`;
- an rc root is released (`rt_rc_*`, `src/lib/nogc_sync_mut/sffi/rc_graph.spl`);
- the build session ends;
- the process exits.

These calls only reassign a binding, so they free nothing:

- `CompileContext.evict_ast` (`src/compiler/80.driver/driver_types.spl:1432`, `self.modules = {}`);
- `evict_hir` (`:1436`);
- `ast_reset` / `reset_all_pools` (`src/compiler/10.frontend/core/types.spl:1800`);
- `lexer_release_parse_source_globals` (`src/compiler/10.frontend/core/lexer.spl:375`).

The old objects stay owned by the session or the process.

## Retainers (resident from parse/HIR through MIR and codegen)

| Retainer | Where it becomes immortal | Later reader(s) | Est. share |
|---|---|---|---|
| All 3110 `ParserModule` ASTs (`ctx.modules`) | retained parse, promoted per file (`driver_source_parse_retained.spl`) | HIR loop `driver_hir_pipeline_lowering.spl:2067-2073`; export-facade checks `driver_aot_native_output.spl:2375,3859` (after MIR); `capture_vhdl_metadata` `driver_orchestration.spl:109` | ~7 GB (scaled from the Stage 3 curve: parse ~3.9 GB / 1626 modules) |
| All 3110 `HirModule`s (`ctx.hir_modules`) | `lower_retained_surface_module` deep-promotes each module out of its HIR scope (`driver_hir_pipeline_lowering.spl:579-645`, promote at `:595`) | whole-program MIR (`driver_pipeline_lowering.spl:723-905`, providers + prescans) | ~10 GB |
| Lowering memos/symbol tables promoted per module | `promote_diagnostics/phase_memo/symbol_table_transient_owners` (`:610-622`) | the shared `HirLowering` across modules | unmeasured |
| Module surfaces (`ctx.module_surfaces`) | retained parse surface phase | HIR loop; the retained path never clears it (the streaming path does at `:1659`) | ~1-2 GB |
| Source text | `ctx.sources[*].content` | the retained path never `rt_string_free`s it (the streaming path does at `:1652`) | <= 142 MiB (all `src/**/*.spl`); negligible |

These are NOT retainers. Each is a shallow struct copy that shares the same
handles:

- `ctx.mir_feed_modules` (`driver_pipeline_lowering.spl:734-736`);
- `ctx.validation_module_array` (`driver_hir_pipeline_lowering.spl:2381`).

`hir_cache_store` and `hir_module_encode_retained_v1` are already scoped
(`driver_hir_cache.spl:644-656`).

## Proposed fixes (in order of payoff)

1. **Done here:** default `HirExpr.is_uninit_marker` to `false`. This brings
   the HIR cache back, so MIR shard workers 2..N decode cached HIR instead of
   re-lowering it. It saves time (worker 2 spent about 1840 s re-lowering) and
   avoids that worker's lowering scratch. It does NOT shrink the
   whole-program resident set of any one worker.
2. **Tree RSS under MIR sharding:** with whole-program HIR, N MIR shard workers
   each hold the full AST and HIR set, so tree peak is about N x 20 GB.
   For a capped lane, either:
   - use `SIMPLE_MIR_SHARDING=0` (one ~24 GB process, not 2 x ~20 GB); or
   - use `SIMPLE_MIR_FORK_WORKERS` (copy-on-write children after HIR,
     `native_build_main.spl:1462-1470`).
3. **AST lifetime (main per-process win, ~7 GB):** `rt_rc_share` each
   `ParserModule` when parse commits it, and `rt_rc_release` it right after
   its HIR has been promoted. Needed first:
   - The aliasing proof: HIR built inside the HIR scope can point at
     AST-owned strings that are already process/session-owned, so promote
     skips them. Releasing the AST graph would then free strings that HIR
     still reads. The promote walker (`runtime_native.c`
     `rt_transient_heap_promote`, ~3407) would have to copy, not skip,
     rc-owned strings.
   - Moving the three post-HIR AST readers (the export-facade checks, VHDL
     metadata) to scalar facts captured during the HIR loop.

   This is too large for a minimal diff and needs a Phase 2 rebuild plus a
   capped measurement.
4. **Measure before changing ownership:** run once with
   `SIMPLE_MEM_SNAPSHOT_FILE` set. The retained HIR loop already writes
   `hir-file-start` / `hir-post-lowering` / `hir-post-diagnostics` /
   `hir-post-store` per module. Record commit charge as well as the working
   set.

## Landed fix

- `src/compiler/20.hir/hir_definitions.spl`: `is_uninit_marker: bool = false`.
  This does not change logic: a nil bool already read as false in
  `interp_is_uninit_marker_init`, and the codec now writes `0` where it wrote `N`.
- `test/01_unit/compiler/20.hir/uninit_marker_lowering_spec.spl`: two new cases.
  The source pin fails without the default. The seed interpreter fills an
  omitted bool with false, so a value check alone cannot tell the two apart.
- The fix takes effect only after a Phase 2 rebuild. The Rust seed does not
  reflect Phase 2 memory behavior.

## Recurrence 2026-11-14, aarch64 (DGX Spark), Stage 2 compiler-test matrix

`compiler_cli_build` aborted with `primary_status=rss-cap-exceeded`
(`primary_exit_status=88`; the matrix reports `status=89`) in two independent
`--full-bootstrap --stop-after-stage2 --backend=cranelift` runs:

| run | source | process-tree cap | last progress line |
|---|---|---|---|
| `bootstrap-fable-32` | `origin/release/1.0.0` `2864bc90f8c` | 24,146,760 KiB | MIR, struct re-registration warnings |
| `bootstrap-jitfree-s1` (PR #9147, under `SIMPLE_ARRAY_FREE_QUARANTINE=1`) | `33bc5c6d1d8` | 29,360,128 KiB | `[mir] 350/3146 rss_mib=26630` after about 100 min |

In both runs Stage 2 build, sanity and the compiler hash check passed, and
`compiler_version` passed. The full-CLI MIR phase now exceeds a 28 GiB cap
on this host, above the ~20 GB MIR figure recorded above.
