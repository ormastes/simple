# Stage 2 `compiler_cli_build` hits the tree RSS cap during MIR (2026-11-06)

Status: mitigated (shard-count pin in `scripts/bootstrap/phase-c-backend-commands.shs`).
Root retention in the MIR shard worker remains open; see "Not fixed" below.

## Symptom

Bootstrap run 10 (base `a720cb10557`, `build/bootstrap-opus-10`) aborted in
Stage 2 compiler tests. Row `compiler_cli_build` reached the 52 GiB
whole-tree cap at MIR schedule position 1088 of 3031. The tree held two
`compiler.snapshot` processes of ~25 GiB each.

## Not a regression

Run 4 (base `13a060d644e`, 2026-11-05, before #7177 `xray_mode` and #7184 HIR
arity) shows the same per-worker curve:

| MIR position | run 4 RSS (MiB) | run 10 RSS (MiB) |
|---|---|---|
| 50  | 19274 | 19337 |
| 300 | 20955 | 21037 |
| 550 | 20746 | 21052 |
| 1100 | — | 25231 |

Earlier runs failed before MIR, so this cost was never reached.

## Mechanism

- The row runs `[mir-shard] shards=2 parallel=2`. The coordinator's default
  shard count is the concurrent worker count
  (`native_build_mir_shard_count`, `src/app/cli/native_build_main.spl`), so
  each worker claims ~1516 of 3031 modules.
- Each MIR shard worker runs its own parse+HIR and starts MIR at ~19.3 GiB.
- A shard worker keeps every claimed module's MIR in `ctx.mir_modules` until
  the whole claim loop ends (`aot_compile_mir_shard_v1`,
  `src/compiler/80.driver/driver_aot_pipeline.spl`, `begin(0)` = staging
  off). Evicting would not help: the native runtime has no collector
  (`native_staged_codegen.spl` header, probe P0: 0 of 2001 allocations
  reclaimed); process exit is the only release.
- Measured growth: ~11 MiB RSS per claimed module (largest-first claim order).
  2 x (19.3 + 1516 x ~0.011) GiB does not fit 52 GiB at any point past ~1100.

## In-process measurement (probe build, 2026-11-06)

Probe binary = `a720cb10557` + a retained-root dump (local only, not landed),
`native-build src/app/cli/bootstrap_main.spl` (1571 modules), in process,
`SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=0`, `MemoryMax=32G`,
`SIMPLE_MIR_SECTION_PROFILE_FILE` rows per lowering section:

| modules lowered | runtime heap_live (MiB) | RSS (MiB) |
|---|---|---|
| 100 | 2617 | 11930 |
| 200 | 2761 | 13058 |
| 300 | 2903 | 13694 |

- heap_live grows 1.4 MiB per module; RSS grows ~8.8 MiB per module.
- Every `MirLowering` field root (`transient_owner.spl` inventory) is flat
  between position 50 and 100 (largest: `provider_enum_row_variants` 21 MiB,
  `rti.rows_by_key` 5.8 MiB, `callable_link_names` 5.5 MiB).
- Per-module retained heap (s5 minus p0) has a fixed floor of ~955 KiB even
  for one-line facade modules (`app/io/time_ops.spl`), plus a size term
  (`bootstrap_main.spl` 7 MiB, `driver_aot_native_output.spl` 7 MiB).
  A trivial module allocates ~12 MiB in the provider sections (p5a provider
  loop 6.4 MiB, p5 layouts 2.1 MiB, p6 1.4 MiB, p1 1.0 MiB) and the scope end
  frees ~11.1 MiB.

## Mitigation landed

`bootstrap_phase_c_run_tool_build` exports `SIMPLE_MIR_SHARD_COUNT=8` for the
full-tool rows (scoped to the call, like `SIMPLE_FILE_WORKERS=0`; an explicit
caller value wins). Each worker then claims at most ~380 modules: about
19.3 + 380 x 0.011 = 23.5 GiB, two concurrent workers about 47 GiB. Pinned by
`scripts/bootstrap/tests/phase-c-backend-commands-test.shs`. The coordinator
prints the effective value in the row log as `[mir-shard] shards=<n> parallel=<p>`.

Costs and margins (estimates from run 10, unverified until the next run):
- Memory: ~47 GiB of the 52 GiB cap, a ~5 GiB margin. Workers claim
  largest-first, so the first wave holds the heaviest modules; the 11 MiB
  slope was measured on that same order.
- Wall time: 4 waves of 2 workers instead of 1. Each worker repeats the
  frontend (~13 min with the HIR cache warm in run 10) and lowers ~380
  modules (~16 min at ~2.5 s each): ~2 h of MIR plus ~15 min of HIR shards,
  against the 14400 s row timeout (3600 s x4 scale). Each worker's own timeout
  starts at its spawn.
- The pin covers all four tool rows (cli, test runner, MCP, LSP). Smaller
  closures pay extra frontend passes; a closure-scaled count would avoid that.

## Not fixed

1. **Fixed per-module retained floor (~955 KiB): relocated provider type
   symbols.** `relocate_provider_type_symbol`
   (`src/compiler/50.mir/_MirLowering/provider_metadata.spl`, the
   `self.symbols.define_with_binding(allocation_name, ...)` call) copies every
   provider class/struct/enum/trait the consumer reaches into the consumer's
   own HIR `SymbolTable`, which is persistent HIR, so the copies survive the
   module's transient scope. Probe (`[symtab]` pre/post each
   `lower_module_transient_scoped`, 104 modules of the `bootstrap_main`
   closure): the consumer table grows by avg 833 symbols per module, min 725
   (one-line facades such as `bootstrap_k1_selected.spl`), max 870. Not
   rolled back here: lowered MIR keeps those ids (`MirType.Struct(symbol:
   SymbolId)` / `Enum(symbol:)`, `src/compiler/50.mir/mir_types.spl`) and
   the shard worker runs codegen after all lowering, so truncating the table
   at scope end would leave ids the later passes may resolve. A fix needs
   either a per-worker shared relocation table (one copy per provider type,
   not per consumer) or proof that no post-lowering reader in 60/70/80
   dereferences a relocated id.
2. **RSS grows faster than runtime heap_live, by a varying factor.** In
   process, `bootstrap_main` closure: heap_live +1.4 MiB/module throughout;
   RSS +1.7 MiB/module over modules 25-100 (probe2-a) but +8.8 MiB/module
   over modules 100-300 (probe-bm0). Whether the excess is untracked live
   bytes or freed-but-resident pages is not established: a glibc `mallinfo2`
   sampler (LD_PRELOAD) never reached the worker, because the native-build
   coordinator replaces the worker's environment.
2a. **~2.5 s per module even for facades** (run 10 `[mir-slow]` floor): a
   one-line module allocates ~12 MiB in the provider sections (p5a provider
   loop 6.4 MiB, p5 layouts 2.1 MiB, p6 trait impls 1.4 MiB, p1 native traits
   1.0 MiB), because they walk the whole provider closure per consumer.
3. The 19.3 GiB per-worker HIR floor: every MIR shard worker rebuilds the
   whole HIR before claiming a module.
4. A single cold MIR shard worker (`--threads 1`, no HIR shards) SIGSEGVs
   during in-process HIR at `compiler.common.error_codes` (2868/3060),
   `status=CRASH exit=-139`, on the run-10 Stage 2 binary `43f9a6fc68ac`.

## Run 11: row killed at the 52 GiB phase cap with 8 MIR shards; row cap 60 GiB

Run 11 (2026-11-06, base `e4c8830efc7`, Stage 2 binary sha256
`7daae12809221236454e78afb4d7a3cb4cf68e3394b188180bbbbcb840638702`,
121 GiB aarch64 host, `SIMPLE_MIR_SHARD_COUNT=8`) aborted `compiler_cli_build`
with `primary_status=rss-cap-exceeded`: `rss_limit_kib=54525952` (52 GiB,
`cap_source=phase-policy`, `cap_bound=worker-floor-elevated`: base 4194304 +
worker floor 16777216 x 150% x 2), `peak_rss_kib=54579388`. Two MIR shard
workers sampled at 24.0 and 25.2 GiB plus a ~1.1 GiB coordinator, in
`native_compile` of shard 1 (20/382). Host budget 63800400 KiB (50% of
127600812); host MemAvailable never fell below 35 GiB during the run.

How the cap reached the row: `bootstrap_tree_rss_whole_build_export` publishes
ONE pair (`SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` + elevated ceiling) that
both the campaign watchdog (`bootstrap-verification-campaign.shs`, wrapping
every row) and each row owner (`run-process-group-timeout.shs`) read. Stage 2
tool builds run serially (`BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1`), so
`compiler_cli_build` and `test_runner_build` never share the cap at the same
time; the kill came from the campaign receipt.

Owner decision: price the `compiler_cli_build` row at 60 GiB (62914560 KiB),
keep 8 MIR shards, keep every other row's cap. Implemented in the policy owner
(`scripts/bootstrap/lib/tree-rss-policy.shs`,
`BOOTSTRAP_TREE_RSS_PHASE_CLI_ROW_CAP_KIB`): the whole-build plan computes a
separate row cap (only with >= 2 workers, above the plan cap and within the
host budget; otherwise the plan cap), the export publishes it
(`SIMPLE_BOOTSTRAP_TREE_RSS_CLI_ROW_{CAP_KIB,CEILING_KIB,BOUND}`, enforce mode
only) and re-admits it before the phase starts; `bootstrap_tree_rss_row_cap_enter`
scopes it around that one row (receipt `cap_bound=cli-row-mir-shards`), and
`bootstrap_tree_rss_campaign_envelope` raises the campaign envelope to the
largest row cap. The phase cap itself stays 54525952 for every other row. A
higher worker FLOOR was not used because it would re-price every full-CLI row.

Risk: run 11's `[hir-shard]` line reports a cgroup `memory.max` of 67108864 KiB
(64 GiB); a 60 GiB tree leaves ~4 GiB before the kernel OOM-kills ahead of the
watchdog. The compiler's own effective shard budget (cgroup - headroom = 40 GiB)
is unchanged; only the watchdog kill line moved. This does not fix the
unbounded MIR share above; it buys ~8.5 GiB over the measured 51.5 GiB.
