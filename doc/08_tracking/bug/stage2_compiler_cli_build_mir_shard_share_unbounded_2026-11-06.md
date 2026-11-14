# Stage 2 `compiler_cli_build` hits the tree RSS cap during MIR (2026-11-06)

Status (2026-11-07): mitigated, verification pending. 8 MIR shards
(`scripts/bootstrap/phase-c-backend-commands.shs`, #7274; #7352's 12 reverted
by #7354) under the 60 GiB `compiler_cli_build` row cap (#7302). Run 13
finished MIR with no rss-cap kill; codegen headroom of the `compiler.*` /
`lib.*` / `os.*` shards is still unmeasured (see the 2026-11-07 section). Root
retention in the MIR shard worker remains open; see "Not fixed" below.
2026-11-14: "Not fixed" item 1 (relocated provider type copies) has an opt-in,
default-off scope-end retraction (`SIMPLE_MIR_RETRACT_PROVIDER_TYPES=1`),
byte-identical MIR by construction, awaiting a Stage 2 flip run -- see the
"Item 1" section at the end.

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

## Run 11: 8 shards were not enough (2026-11-06)

Run 11 (`build/bootstrap-opus-11`, carries #7274) logged
`[mir-shard] shards=8 parallel=2` and still aborted with
`rss-cap-exceeded`: tree peak 54,579,388 KiB (52.05 GiB) against the
54,525,952 KiB (52.0 GiB) cap, the same cap as run 10. Top process
26,437,356 KiB (25.2 GiB). Worker curve (MIR position: RSS MiB) 50: 19634,
300: 21498, 500: 20974, 750: 22290. Both first-wave workers finished lowering
their ~382 modules, ran `native_cache` 382/382 and were in `native_compile`
when the cap hit (in run 14 the same `done=13`/`done=19` counters were printed 2 ms
into the phase and counted modules settled before codegen, not objects
written -- run 14 wrote 669 objects before its kill; see
`stage2_cranelift_codegen_scope_default_off_2026-11-07.md`); RSS rose from ~22.4 to 25.2 GiB in those
last minutes. So the peak is end-of-shard codegen, ~16 MiB per claimed module
all-in (the 11 MiB run-10 slope was MIR only).

The `[mir]` lines walk alphabetically (app.* first), not largest-first:
wave 1 measured the lighter modules. The compiler.* / lib.* waves are not
measured, so the per-module figure may be higher for them.

### Pin raised to 12 (superseded: the pin is 8 again, #7354; see 2026-11-07 below)

ceil(3049/12) = 255 modules per worker: 19.6 + 255 x 16 MiB = ~23.6 GiB,
~48 GiB for two plus the coordinator, a 2-4 GiB margin on the light modules.

Wall time is the other side of the trade. Every shard worker repeats the
frontend: run 11 coordinator HIR ~1,411 s, worker frontend ~1,160 s, worker
MIR ~1,220 s for 382 modules. Six waves of 255 need about
1,411 + 6 x (1,160 + ~815) = ~13,300 s before codegen, against the 14,400 s
row timeout; codegen cost per wave is unknown (run 11 died 12-20 modules into
it). Each worker's own `--timeout` (7200 s) starts at its spawn
(`native_build_main.spl` shard pool), so it is not the binding limit; the row
timeout is. 8 shards is proven OOM; 16 would certainly time out. No shard
count meets both bounds while each worker rebuilds ~19.6 GiB of HIR: the
structural fix is item 3 below.

### Separate blocker in run 11 (not memory) - fixed

Fixed by #7301 (`64026e63fe6`, cranelift narrow-integer negate in the I64
lane) and #7308 (`fadd88059b3`, MIR f64 across text parse). Kept for history:

Run 11 recorded 5 cranelift AOT errors that failed the row independently of memory:
- `app.office.sheets.data_ops._compare_row_cells`: verifier error
  `isub.i32 v167, v166` where `v166` is i64.
- `app.office.sheets.spreadsheet._parse_f64`:
  `E-BACKEND-CRANELIFT-CALL-ABI` call to `rt_enum_id` with an f64 argument
  (callee declares i64).

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
   **2026-11-14: mechanism landed, opt-in, default off -- see "Item 1:
   scope-end retraction" below for the decision, the audit and the flip plan.**
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
host budget), the export publishes it
(`SIMPLE_BOOTSTRAP_TREE_RSS_CLI_ROW_{CAP_KIB,CEILING_KIB,BOUND}`, enforce mode
only) and re-admits it before the phase starts; `bootstrap_tree_rss_row_cap_enter`
scopes it around that one row (receipt `cap_bound=cli-row-mir-shards`), and
`bootstrap_tree_rss_campaign_envelope` raises the campaign envelope to the
largest row cap (its receipt keeps the phase bound). The phase cap itself stays
54525952 for every other row. A higher worker FLOOR was not used because it
would re-price every full-CLI row.

Fail-closed rules (review follow-up): a host budget that holds the 2-worker
plan but not 62914560 KiB is refused up front ("compiler_cli_build row needs
62914560 KiB ..."), never run at the 52 GiB cap run 11 died at; one build
thread (one MIR worker) and small hosts keep the plan cap. Because the
campaign envelope is the max row cap, not a sum, the row cap also requires
`BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1` (both Stage 2 entry points pin it);
anything else is refused at plan time and at row entry.

Known limit (not handled): the policy does not read cgroup `memory.max`. Run 11's `[hir-shard]` line reports a cgroup `memory.max` of 67108864 KiB
(64 GiB); a 60 GiB tree leaves ~4 GiB before the kernel OOM-kills ahead of the
watchdog. The compiler's own effective shard budget (cgroup - headroom = 40 GiB)
is unchanged; only the watchdog kill line moved. This does not fix the
unbounded MIR share above; it buys ~8.5 GiB over the measured 51.5 GiB.

## 2026-11-07: shard count back to 8 (reverts the #7352 raise to 12)

#7352 raised the full-tool MIR shard count from 8 to 12 based on run 11,
which ran under the old 52 GiB row cap. #7302 has since raised that cap to
60 GiB. Run 13 (`5fdf9fa4fc0`, Stage 2 binary sha256 `ef163123d471887e...`)
ran the row at 8 shards under the 60 GiB cap. All 8 shard workers finished
MIR. Every run-process receipt reports `primary_status=complete`, and there
was no rss-cap kill. The coordinator's tree RSS sample peaked at 57.06 GiB
(the external sampler's process sum was 56.96 GiB), and the largest single
process was 31.99 GiB. That peak came from the 2 `app.*` shards, which
reached end-of-shard codegen (at 361/383 and 364/383). They failed on
`export_list_static_visibility_not_lifted_2026-11-06`.
**The 6 `compiler.*`/`lib.*`/`os.*` shards stopped on 498 MIR lowering
errors before codegen** (`driver_aot_pipeline.spl` runs `compile_to_native`
only at 0 errors). Their codegen memory headroom is therefore UNMEASURED.

On wall time, the row took 10156 s against `task_timeout_seconds=14400`.
With parallel=2, 8 shards run as 4 waves of about 2540 s each, and each
wave repeats the ~19 min frontend. 12 shards run as 6 waves, projected at
12400 s (frontend fixed, MIR scaled) to 15200 s (whole wave fixed). That
reaches or passes the row timeout, and that is before the unmeasured codegen,
which adds wall time at any shard count. No memory measurement requires 12.
The pin goes back to 8. `phase-c-backend-commands-test.shs` now bounds it
on both sides: >= 8 for memory (run 10) and <= 8 for wall time (run 13).
This adds no new knob; `SIMPLE_MIR_SHARD_COUNT` from the caller still wins.

## Item 1: scope-end retraction of relocated provider type copies (2026-11-14)

Re-checked on `origin/release/1.0.0` = `3e473113105` (~2300 commits after the
record): **still live.** `relocate_provider_type_symbol`
(`provider_metadata.spl:386-430`) still `define_with_binding`s into
`self.symbols`, and `self.symbols = module.symbols` (`module_lowering.spl:2814`)
is the consumer HIR module's own persistent table. The trait-impl and layout
walks have gone demand-driven since 10-20 (`trait_demand`, `layout_demand`,
`module_lowering.spl:3009-3024`), but the p1 native-trait walk has not:
`register_native_trait_declarations/implementations` runs over EVERY provider
for EVERY consumer (`module_lowering.spl:2846-2858`; tables reset per module at
`:2830`) and relocates every type a provider trait signature or impl names.
Reproduced in the small (seed, spec below): a facade consumer with no imports
grows by exactly `Shape + Factor + Offset + Sq0..Sq5` = 9 symbols against 6
impl modules -- the floor scales with the closure's trait/impl population.

### Decision: (b) retract at scope end; (a) and (c) rejected

- `mir_json.spl:104-108` serializes `MirType.Struct/Enum(symbol)` as the raw
  id, so **byte-identical MIR <=> identical id allocation**. A per-worker
  shared relocation table (a) and demand-driven p1 (c) both renumber every
  later relocated id in every consumer that uses provider types.
- (c) is also not semantics-preserving: `native_trait_conversion.spl:405-430`
  builds a concrete type's runtime trait-cast dispatcher by enumerating ALL
  `native_trait_implementations` of that concrete owner, so the module that
  creates a trait object must know traits it never names (a dynamic cast in
  another module hits that dispatcher). Registration cannot be keyed on what
  the consumer names without a transitive closure that (c) did not have.
- (b) is byte-identical by construction: retraction runs after the MirModule
  is promoted and the transient scope has ended, so the MIR already carries
  the ids and nothing is renumbered.

### Mechanism (opt-in, default OFF)

- `SymbolTable.retract_symbol_rows_v1(ids)` (`20.hir/hir_symbol_table_methods.spl`):
  drops the `symbols` rows plus every `qualified_types` / `module_callables`
  row whose VALUE is one of them (the three maps `define_with_binding(
  bind_lexical: false, defining_module: Some)` writes). `next_symbol_id` is
  never rewound: a retracted id is never reissued, so a stale holder resolves
  to nil, never to another symbol. Maps are rebuilt without the keys -- the
  one `Dict` removal form both lanes agree on
  (`dict_remove_return_value_differs_native_vs_interpreter_2026-09-13.md`).
  No `SymbolTable` field was added: `generated/hir_codec.spl:65,10555`
  construct it literally, so a field means a codec regeneration.
- `MirLowering.provider_type_relocation_journal: [i64]` records every id
  `relocate_provider_type_symbol` defines (copy/push/store, Stage 4 field
  mutation rule); reset per `lower_module_transient_scoped`; the lifted-lambda
  nested lowerer inherits and hands it back (`switch_operators_calls.spl`
  8460/8772); promoted through the transient-owner inventory
  (`transient_owner.spl`) so it is readable after the scope ends.
- Knob: `MirLowering.retract_provider_type_relocations` or
  `SIMPLE_MIR_RETRACT_PROVIDER_TYPES=1` (read once per module). Applied on the
  success path of `lower_module_transient_scoped` only, after `s5_scope_end`;
  the unscoped fallback and every Err return keep the copies (a re-lower then
  reuses them exactly as before). Same opt-in class as
  `SIMPLE_MIR_SHARD_INTERFACE_HIR=1`.
- Only the four type kinds are retracted. `relocate_provider_callable` shares
  the writer but the interpreter lane reads function symbols from the module
  table after lowering (`interpreter_calls.spl:205`), so callables stay.

### Spec (seed, `/home/yoon/dev/seed-try-target/release/simple test`)

`test/01_unit/compiler/50.mir/mir_provider_symbol_relocation_retention_spec.spl`:
one `MirLowering`, fresh HIR per run, lowers `lib.impl0` (provider), a facade
and a consumer that dispatches through `Shape` -- knob off, off again
(control), on.

| module | off growth | on growth | next_symbol_id growth (both) | MIR rows equal |
|---|---|---|---|---|
| app.facade | 9 (all type kinds) | 0 | 9 | yes (384 B) |
| app.user | 6 (all type kinds) | 0 | 6 | yes (1691 B) |
| lib.impl0 | 3 (own `Method` rows) | 3 | 3 | yes (12593 B) |

Red before the change: 1/2 -- the facade example failed (growth 9), the
loose `user_growth < 12` bound of the first spec shape passed. Green:
3/3. MIR equality is over the serialized functions, statics, constants, type
ids/names and enum records. **Side finding:** `mir_module_canonical_fingerprint_v1`
is NOT run-to-run stable on the seed for a type-defining module --
`mir_fp_type_row` interpolates `{t.kind}` and the seed prints struct fields in
hash order (two knob-off runs of `lib.impl0` gave `c3812be7…` and
`0d9b36b6…`; the function rows were byte-identical). Recorded in
`mir_canonical_fingerprint_type_row_hash_order_seed_2026-11-14.md`.

Adjacent specs (seed, same runner), before -> after the change:
`mir_provider_trait_impl_once_per_closure` 3/3 -> 3/3,
`mir_provider_session_key_no_reencode` 2/2 -> 2/2, `provider_layout_demand`
4/4 -> 4/4 (one after-run hit the runner's `daemon-no-response` 900 s budget
under host load and passed 4/4 on re-run), `driver/mir_provider_aliases`
8/8 -> 8/8. `scripts/check/check-mir-transient-scope-boundary.shs` reports the
same `FAIL -- 18 invariant(s): owner-field-inventory-drift;
sffi-owner-release-forwarding-invalid` with the six source files reverted to
`3e473113105` and with the change applied: pre-existing red on the release
tip, not introduced here; the two new fields are in both the declaration and
the `transient_owner.spl` inventory.

### Post-lowering reader audit (static; why the knob stays off until a Stage 2 run)

- 60/70 import no `SymbolTable` except a fresh one in
  `result_abi_observation_capture.spl:90` and the interpret lane's function
  lookup above. Backend type mappers treat `Struct(_)` as an opaque pointer
  (`cranelift_type_mapper.spl:200,224`, `codegen.spl:619`).
- The AOT pipeline already evicts the whole HIR after lowering
  (`driver_aot_pipeline.spl:193-201`: "HIR is dead after MIR lowering for every
  AOT backend except vhdl and SIMPLE_BOOTSTRAP_DIRECT_IR"), so no MIR pass or
  codegen in that lane can read a consumer table. Those two exceptions, and the
  interpret lane, are the readers the knob must not be flipped under.
- 50.mir never writes relocated ids into provider-visible HIR: every
  `X.functions = ...` assignment in 50.mir targets a `MirModule`
  (`native_trait_thunks.spl:24`, `global_initializer_guard.spl:99`,
  `function_lowering.spl:1422`, `module_lowering.spl:3339/3620/3829/4135`), so a
  later consumer reading the retracted module as a provider only sees HIR-issued
  ids (below the watermark). The spec's provider-first ordering covers this.
- Cross-consumer lowering caches are reset per module (`native_trait_layouts`,
  `native_trait_implementations` at `module_lowering.spl:2830`); session rows
  are text-keyed.
- 80.driver readers of `module.symbols` are HIR-stage
  (`driver_warm_mir_logical_names_v1` at state 0, `collection_driver_binding_v1`
  via the planner, `driver_hir_pipeline_support.spl:415`,
  `run_representation_manifest_pass` from `driver_hir_pipeline_lowering.spl:2725`).
- NOT covered statically: `SIMPLE_BOOTSTRAP_DIRECT_IR=1`
  (`bootstrap_compile_to_native_local` re-reads `ctx.hir_modules`), the vhdl
  backend, and any reader reached through `ctx.hir_modules[...]` dynamically.
  A numeric dead-id guard in `get_symbol_raw` was considered and rejected:
  `relocate_provider_type_symbol` legitimately probes ids that belong to OTHER
  tables (`provider.symbols.has(id.id)`), and ids are small dense integers, so
  a miss in the retracted range is not evidence of a dead-id reader.

### Premises the flip run must prove (not provable on the seed)

- The spec asserts ROW COUNT, not bytes. Reclamation presumes the persistent
  heap frees the dropped `HirSymbol` copies, the retired text keys and the old
  map storage on last reference (the record's `heap_live` probe is a refcount
  metric, so this is expected). On a leak-only heap the three map rebuilds
  per module would be a net INCREASE; the knob then stays off. The flip
  run's heap_live/RSS curve against run 13 is the test.
- The journal's survival past `scope_end` is seed-verified (the retraction
  reads it after `s5_scope_end` and the spec is green); the boundary gate
  checks inventory parity only, so promotion on the native lane is proven by
  the Stage 2 run, not here.
- The lifted-lambda nested lowerer hands its journal back only on the
  `self.symbols = lw.symbols` adoption branch; otherwise its ids stay
  retained (safe side: never retract ids issued in a table that may not be
  the parent's).
### Flip plan (owner decision after evidence)

1. Stage 2 `compiler_cli_build` row, 8-shard pin, `SIMPLE_MIR_RETRACT_PROVIDER_TYPES=1`
   on the MIR shard workers only (not the interpret lane, not vhdl, not
   `SIMPLE_BOOTSTRAP_DIRECT_IR=1`). Compare per-module MIR against the knob-off
   run of the same inputs (serialized functions/statics/constants/type ids, not
   the canonical fingerprint until its type row is fixed) -- expect identical.
2. Record the `[symtab]` pre/post delta (expect ~0 type rows retained per
   module vs the 725-870 floor) and the worker RSS/heap_live curve against run
   13; `[mir-scope]` trace under `SIMPLE_MIR_SCOPE_TRACE_MODULE` prints the
   retracted count per module.
3. Any `SymbolId(id: -1)` / `HirTypeKind.Error` that appears only with the knob
   on is a dead-id reader: name it here and keep the knob off.
4. On green: default the knob on for the shard-worker lane in
   `phase-c-backend-commands.shs` (same place the shard pin lives), leaving the
   env override for A/B.
