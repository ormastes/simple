# native-build: every phase after parse is single-threaded (2026-08-22)

Lane: perf. Sibling of
`native_build_frontend_not_incremental_2026-08-21.md` (which made PARSE
parallel via shard processes). Status: **analysis complete; parse-shard tail
fixed (work queue); HIR/MIR/codegen parallelism filed, not shipped** — see
"What remains" for why and for the concrete next step.

## Symptom

`bin/simple native-build --source src/app --entry-closure --entry
src/app/cli/bootstrap_main.spl --threads 8` shards the parse across 8 worker
processes, then runs HIR, typecheck, mono, MIR, codegen and link **in the one
driver process**, one module at a time. 7 of 8 cores idle for the bulk of the
build. Measured on the stage-1 logs (`scratchpad/fp7/stage1_build.log`,
`fp5/`, both 2026-08-21, load 28-35):

| stamp | fp7 (+ms) | what it says |
|---|---|---|
| `parse 666/666 step 1/6` | 856 159 | parse phase end, 8 shards |
| `surface_freeze ... complete` | 917 024 | surface window 61 s |
| `hir 10/666 step 2/6` | 2 336 743 | **10 modules in 1 420 s = 142 s/module** |

666 modules at 142 s/module is ~26 h. **No run on record has ever reached
MIR, codegen or link on the bootstrap closure**, so there is no measured
MIR/codegen share for that closure; the 192-module lint_entry closure
(`phases36/run2.log`, `run3.log`) also died inside HIR (109/192 at +4 397 s;
138/192 at +3 829 s, 25-50 s/module). Every post-parse number below is from
the 3-module fixture instead (see "Measured").

Two things the logs say that are NOT this bug but gate any fix for it:

- A cache **hit** costs ~2 s under the interpreted driver: run3 real build,
  `hits=192 misses=0 parses=0`, parse phase +16 s → +400 s. Deserialising a
  flat pool is not free while the driver is tree-walked.
- The real build's parse in fp7 still took ~830 s with all 8 shards done.
  Same mechanism.

## Per-phase parallelizability (what a module needs from other modules)

Phase numbers are the `step k/6` in `[build]` stamps
(`src/compiler/80.driver/driver_log_helpers.spl:130`).

| step | phase | per-module loop | cross-module input needed | independent per module? | can cross a process boundary today? |
|---|---|---|---|---|---|
| 1 | parse | `driver_source_pipeline_parsing.spl` `for source in unique_entry_sources` | none (content only) | yes | **yes** — `ParserModule` ⇄ flat pool blob, `frontend_parse_cache.spl` (content-keyed, scope-checked) |
| 1 | surface build/alias/export_origins/freeze | same file, after parse | every `ParserModule` in the closure | no (whole-closure pass, ~61 s on 666) | not needed: each child rebuilds it from cache hits |
| 2 | HIR lowering | `driver_hir_pipeline_lowering.spl:117-270`, one `HirLowering` over frozen `surfaces` | **frozen module surfaces only** (`hirlowering_for_module("", surfaces)`; `lowered_by_surface` is consulted only for alias dedupe of the same physical file) | **yes** | **no** — `HirModule` (`20.hir/hir_types.spl:21`) carries a `SymbolTable` and `Dict<SymbolId, …>`; no serializer exists (`grep -rl serialize src/compiler/20.hir` → none). `SymbolId`s are process-local, so a codec also needs a cross-process id contract |
| 3 | HIR typecheck / analyze | `driver_orchestration.spl` phase 3 | all HIR modules | no (whole program) | n/a |
| 4 | monomorphize | `monomorphize_impl` | all HIR modules (instantiates across modules) | no (whole program) | n/a |
| 4 | MIR lowering | `driver_pipeline_lowering.spl:200-250`, one `MirLowering` | `prescan_module_struct_names` over **every** HIR module (field order of imported structs), then its own HIR | per-module after the prescan, but the prescan needs all HIR in-process | `50.mir/mir_serialization.spl` exists for `MirModule` (output side) — input side still needs all HIR |
| 5 | native_cache | `driver_aot_native_output.spl:768-815` | own source fingerprint only (`build_cache.get_cached_outputs`) | yes | yes (it is a file cache) |
| 5 | native_compile | `:822-900`, `ParallelBuilder.build()` over `FrozenNativeModuleCapsuleV1` | **own MIR capsule only** | **yes (embarrassingly)** | **partly** — `ParallelBuilder.build()` is in-process and sequential (`parallel.spl:395-470`: the "batch-concurrent" branch still calls `compile_fn` in a loop); `build_supervised()` (`:695`) is the real multi-process path and is unwired because no one-module compile CLI exists (`doc/03_plan/infra/unstable_mode_build_side.md`). Capsules could cross via `mir_serialization.spl` |
| 6 | link | `:1016-1060` | all objects | no | n/a |

Conclusion: the only phase that is both per-module independent AND has a
serialised form today is **parse**, which is why that one got sharded first.
Codegen is independent but its input (MIR) only exists after the whole-program
HIR → mono → MIR chain, so "codegen in N shard children" means "N children
each redo the 26-hour HIR" — strictly worse than sequential. **HIR is the
cost centre by two orders of magnitude and is the only phase whose
parallelisation would change the outcome; it is blocked on an `HirModule`
codec.**

## Design (minimal; same process model, same cache dir)

Reuse the parse-shard mechanism unchanged: N children, each a full
`native_build_worker` that loads the compiler closure, does phase X for the
modules it owns into `build/bootstrap/native_cache/<scope>/…`, exits; the real
build hits the cache. No new global state, no HIR/MIR shape change, no ABI
change; output byte-identical because a hit reproduces the same value the
sequential path would have computed.

1. **Work queue instead of a static split (shipped).** A static hash split
   has a tail: fp7's 8 shards finished between 73 and 94 modules each and the
   last one gated the phase. Each shard now walks the same source list and
   CLAIMS a module before parsing it; whoever claims first parses, the rest
   skip. Claim = marker file under `<frontend cache dir>/queue-<orchestrator
   pid>/`, created inside one flock'd critical section (`file_lock`, flock(2),
   present in both the seed and the C runtime). `rt_dir_create` returns true
   on EEXIST and `rename(2)` overwrites, and `rt_file_create_excl` exists only
   in the C runtime (an unbacked extern returns nil silently under the seed),
   so none of those is an atomic claim. Lock failure degrades to the static
   split for that module, not to "owns nothing". `SIMPLE_PARSE_SHARD_QUEUE=0`
   keeps the static split; the orchestrator receipt says which ran
   (`split=queue|static`), and each shard receipt now carries `claimed=K`.
   Files: `src/app/cli/native_build_main.spl` (`parse_shard_queue_dir`,
   `run_parse_shards`), `src/compiler/80.driver/driver_source_pipeline_parsing.spl`
   (`_driver_parse_shard_claim`, `_driver_parse_shard_owns`).
2. **HIR in dependency levels (designed, not shipped).** Children rebuild
   surfaces from cache hits (61 s on 666, acceptable), lower HIR for claimed
   modules, store `HirModule` content-keyed under `<scope>/hir/`. Needs (a) an
   `HirModule` codec — flat-pool style, over `hir_types.spl`, including a
   `SymbolTable` with process-independent ids; (b) the real build to load HIR
   for hits instead of lowering. Levels are NOT needed for lowering (it reads
   only frozen surfaces), only if typecheck is ever sharded. Estimated as a
   multi-day change; it is the one that matters.
3. **Codegen via `build_supervised` + `mir_serialization` (designed, not
   shipped).** Wire the existing supervised multi-process path with a
   one-module compile CLI that reads a serialised capsule. Gives per-unit
   isolation (the `unstable` mode the config already asks for) and N-way
   codegen. Worth doing only after (2), since codegen is a few percent of the
   post-parse wall on every measurement we have.

## Measured (3-module fixture `test/02_integration/compiler/driver/fixtures/native_build_cache`, seed `c2511ed73a36…`, load 28)

| run | wall | parse | hir | mir | native_compile | link | binary sha256 |
|---|---|---|---|---|---|---|---|
| threads 1, before | 58.2 s | 0.6 s | 0.6 s | 0.5 s | 3.5 s | 31.1 s | `9a40f3117b277548` |
| threads 2, queue | 108.1 s | 0.6 s (3 hits) | 0.6 s | 0.4 s | 3.6 s | 32.6 s | `9a40f3117b277548` |
| threads 1, after | 68.3 s | 0.6 s | 0.5 s | 0.5 s | 4.9 s | 35.0 s | `9a40f3117b277548` |
| threads 2, static split (`SIMPLE_PARSE_SHARD_QUEUE=0`) | 217.7 s (load spike; 3 hits) | | | | | | `9a40f3117b277548` |

Identical artefacts in every configuration. The wall DELTA on 3 modules is
two extra interpreted worker start-ups (~20 s each under this load) plus the
link, which dominates the fixture; the queue's benefit is the removed tail,
which only exists on closures large enough to have one. Shard receipts with
the queue: `shard=0/2 parses=1 claimed=1`, `shard=1/2 parses=2 claimed=2`,
real build `hits=3 misses=0 parses=0`.

## Regression spec

`test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl`
(mirrored in `test/integration/…`): per-worker receipts from both workers,
`claimed` and `parses` each sum to exactly N (a double claim overshoots, a lost
one undershoots), real build `hits=N`, queue dir removed, static split still
reachable behind `SIMPLE_PARSE_SHARD_QUEUE=0`, and the pre-existing
byte-identical-binary case.

## What remains

- `HirModule` codec + HIR cache load path (design item 2). This is the whole
  win; nothing else moves the 26-hour number.
- One-module compile CLI + `build_supervised` wiring for codegen (item 3).
- Cache-hit cost (~2 s/hit interpreted) and the real build's 830 s parse with
  a warm cache — separate perf item, not this record.
- The lint_entry/bootstrap `--threads 1` vs `2` wall comparison asked for in
  this lane was not run: neither closure completes HIR in under an hour on
  this host, so a 2 × multi-hour probe under load 28 with a bootstrap lane in
  flight was out of budget. The fixture numbers above are the evidence.
