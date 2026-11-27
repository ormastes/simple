# native-build SCV cold init crawls: coordinator module is JIT-demoted to pure interpretation (todo 478)

- **Date:** 2026-11-27
- **Status:** PARTIAL — the three source-fixable demotion causes are fixed (see "Fix log"); smoke result recorded below
- **Host:** Windows 11, seed `C:/dev/keep/seeds/simple-local-20261127h.exe`, worktree `C:/dev/lanes/c27-race` (release/1.0.0 tip 2cc4149be75)
- **Todo:** 478 (`dir_sync` native-link smoke)

## Symptom

`SIMPLE_SCV_INVENTORY_COLD_INIT=1 <seed> native-build <entry> -o <exe>` never reaches link.
It is NOT specific to the `dir_sync` entry: the trivial entry `fn main(): print("hi")`
stalls identically. The long silent period is not a hang and not a git/`workarounds:` scan.

## Where it stalls (measured)

1. Frontend load of the coordinator closure prints ~7,976 `[visibility-warning]` lines, then
   `workarounds: incomplete coverage; run simple check-dbs --fullscan bugs`
   (`src/app/cli/native_build_main.spl:2694`). This line is only a progress marker, it returns promptly.
2. With `SIMPLE_BUILD_TRACE=1` the next and LAST line ever printed is
   `[build-trace] +0ms coordinator:admission root=... source_roots=src/app,src/lib,src/compiler,...`
   (`native_build_main.spl`, just before `compiler_source_authority_acquire_v1`).
   So the stall is inside SCV admission: cold-init inventory
   (`compiler_inventory_refresh_*` in `src/app/compiler_entrypoint/inventory_events.spl`:
   `git ls-files -t ...` then one read + canonicalize + 5 digests per source file,
   47,230 `.spl`/`simple.sdn` files, 341 MB, under roots `src,test,examples/10_tooling`).
3. The process is one busy core (CPU-time +20 s per 20 s wall), no child processes, WS ~2.0-2.5 GB.
   After the reads finish the process keeps burning CPU with 0 read/write ops (post-listing phase).

## Root cause evidence: same code, at least 14x slower (42 s vs >10 min unfinished) once the coordinator closure is loaded

| run | engine | result |
|---|---|---|
| probe A: tiny script calling only `compiler_inventory_refresh_v1(cold_init=true)` | hybrid JIT (only demotion: `hybrid-interp-splice rt_time_monotonic_ns`) | **valid=true, 42,033 ms**, ~1,100 files/s |
| probe B: same call, but script first imports/uses `app.cli.native_build_main` | whole module demoted to the interpreter | still unfinished after >10 min; reads at ~30-90 files/s, then CPU-only tail |
| real `native-build` (3 runs) | same demotion | >8-34 min, never finishes |

Probe B and the real run log, before any inventory work:

```
[engine-demotion] reason=jit-compile-error detail=HIR lowering error: Unsupported feature:
  cannot infer field type while lowering Pointcut.matches_name: struct 'ANY' field 'kind'
  [in src/app/cli/native_build_main.spl]
```

`Pointcut` is defined four times (`pub trait Pointcut` at `src/compiler/00.common/cache_contract/aspect_plugin_model_v1.spl:10`, `src/compiler/10.frontend/core/aop.spl:77` struct,
`src/compiler/35.semantics/aspect_seal/facet_model.spl:93` class,
`src/lib/nogc_sync_mut/src/aop.spl:24` struct); the seed's HIR lowering resolves `self` of
`Pointcut.matches_name` to `ANY`, the JIT compile of the entry module fails, and the seed
demotes (announced by one `[engine-demotion]` stderr line) the entire module (including SCV inventory hashing of 47k files) to the
tree-walking interpreter. Renaming only core `Pointcut` -> `CorePointcut` (experiment, reverted)
removes that message but the next one appears immediately:
`CODEGEN-AMBIGUOUS-METHOD in 'simpleos_sdk_ledger_decode_v1': bare method 'as_str' has 4 candidates [MacroConstValu...`
-- i.e. a chain of independent JIT-compile failures, not one. Caveat: slowdown is attributed to
demotion by correlation (A vs B) and the engine-demotion log; no profiler is available here
to prove the per-phase split.

## Not the cause (ruled out)

- git subprocess / `workarounds:` / check-dbs scan: no children, returns before the trace line.
- Cold-init inventory itself: 42 s when JIT-hybrid (matches the 2026-11-07 round-15 80 s figure
  in `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13.md`).
- Why a `dir_sync` entry pulls in `src/compiler/80.driver`: SCV roots are
  `src/app,src/lib,src/compiler,src/os,src/plugins` for ANY entry, and the coordinator itself is
  Simple code importing `compiler.driver.*`; so every native-build loads the compiler closure.

## Next steps

1. Make the coordinator JIT-clean (fix the `Pointcut` ANY resolution AND the `as_str`
   ambiguity at `simpleos_sdk_ledger_decode_v1`; re-run until `[engine-demotion] reason=jit-compile-error`
   no longer appears for `native_build_main.spl`), or
2. Run SCV inventory in a separate lightweight process/script (probe A shape) instead of the demoted coordinator, or
3. Have the seed fail hard instead of demoting for the native-build coordinator.
Repro for the measurement: call `compiler_inventory_refresh_v1(root, root + "/build/scv", ["src","test","examples/10_tooling"], true)` from a script with and without importing `app.cli.native_build_main`.

## Related
- `doc/08_tracking/bug/hir_type_inference_any_field_2026-05-02.md` (same `struct 'ANY' field` lowering failure class).
- `doc/08_tracking/bug/browser_4k_whole_module_dejit_name_collisions_2026-10-04.md` (whole-module de-JIT caused by name collisions).

## Fix log (2026-11-27, branch work/native-build-jit-clean-20261127)

Fast reproducer: a script with `use app.cli.native_build_main.{main as nb_main}` plus its own `fn main()`,
`seed run`, grep stderr for `engine-demotion` (~70 s per iteration; without its own `fn main` the
as_str error is masked by `jit-bail:no-main-fn`). The entry-file check (item 3) only shows when
`native_build_main.spl` is itself the entry, i.e. under a real `native-build`.

| error | fix |
|---|---|
| `cannot infer field type while lowering Pointcut.matches_name: struct 'ANY' field 'kind'` | renamed core `Pointcut` (src/compiler/10.frontend/core/aop.spl) to `CorePointcut`; importers updated: `90.tools/aop.spl`, `90.tools/__init__.spl`, `core/__init__.spl` export, `plugins/aspects_builtin/{log,tracing}_aspect.spl`, `pipeline_integration_spec.spl` |
| `CODEGEN-AMBIGUOUS-METHOD ... 'as_str' has 4 candidates` in `simpleos_sdk_ledger_decode_v1` | explicit receiver type: `val entry: SdnValue = files[path]` before `entry.as_str()` |
| `module has 2 top-level statement(s) that the JIT entry path would silently skip` for `native_build_main.spl` | two bare `"""..."""` string statements above `pub fn` declarations (lines ~3460/3467) turned into `#` comments |

After these, no `reason=jit-compile-error` line remains. Still printed: `reason=hybrid-interp-splice`
for unresolved runtime externs (`rt_process_observation_v4_*`, `rt_host_*_headroom_bytes_v1`,
`rt_shared_parse_cell_read_v1`, `rt_simple_abi_version*`, `rt_text_is_ascii`, `rt_time_monotonic_ns`, ...):
these are per-function interpreter splices, not whole-module demotion (probe A in the table above had the same).
Their runtime backing in the seed is a separate gap.

### Smoke result after the fixes (`test/tmp_dir_sync_smoke`, `SIMPLE_SCV_INVENTORY_COLD_INIT=1 SIMPLE_BUILD_TRACE=1`)

SCV admission/cold-init inventory now FINISHES: `coordinator:worker:select` at +320 s (previously never
finished in >34 min), then `coordinator:shards parse=1 hir=3`, then `[build] phase=source_closure`
93/93 done (111 s). After that the run went silent for >15 min with no further `[build]` line
(killed by the operator, no exe produced, `true`/`false` output NOT reached). Next step: find what the
post-source_closure phase (task 2 of 6) is doing; not yet investigated.

## Seed defects behind the source workarounds (open, Fable review 2026-11-27)
The three source fixes above dodge seed bugs; they are not closed by this change.
1. Same-name type field inference: lowering `Pointcut.matches_name` inferred `self` as `ANY` while four `Pointcut` types coexisted (trait in `00.common/cache_contract/aspect_plugin_model_v1.spl:10`, class in `35.semantics/aspect_seal/facet_model.spl:93`, struct in `src/lib/nogc_sync_mut/src/aop.spl:24`, and the renamed core struct). Three remain after the rename. Same class as the OPEN `doc/08_tracking/bug/browser_4k_whole_module_dejit_name_collisions_2026-10-04.md` (rename-to-dodge); the RESOLVED `hir_type_inference_any_field_2026-05-02.md` does not cover this instance.
**Investigation 2026-11-27 (lane c28-a, seed simple-local-20261127m):** NOT reproduced with a minimal multi-module reproducer. Struct `Pointcut{kind,pattern}` with an implicit-self `matches_name` (as in the pre-rename `10.frontend/core/aop.spl`), plus a same-named trait+impl, class, and a second struct with different fields, spread over 4 modules and imported by glob, selective, and `as` alias, runs on `SIMPLE_EXECUTION_MODE=jit` with `demoted=no` (receipt `engine=cranelift-jit`). The owner-qualified scheme in `hir/lower/module_lowering/flatten_struct_owner.rs` already handles that shape. The remaining suspects, not yet proven: (a) `lower_function` (`module_lowering/function.rs` ~1286) resolves `current_class_type = types.lookup(owner_type)` BEFORE `enter_flatten_struct_scope()` (~1299), so the lookup runs under the caller's overlay, not the function owner's; (b) traits are not in the collision census (`struct_declaration` covers only struct/class/enum), so a trait sharing a name with a struct keeps the bare name; (c) the native-project lane has no owner attributes, so the census is a no-op there and the registry is keyed by bare name (last registration wins). Reproducing needs the real closure (revert `361c400c8c5` on `aop.spl` and `native-build`); my attempt to run a 4-file import of the real modules was demoted earlier by an unrelated `time_now_unix_micros` ambiguity. Regression tests for the same-unit trait/class/struct coexistence (no owner attributes, suspect c) are in `src/compiler_rust/compiler/src/hir/lower/tests/same_named_type_self_tests.rs`.
Review caveats (Fable): the new tests in `same_named_type_self_tests.rs` pin only "lowering succeeds" (the ANY-receiver fallback in `type_resolver.rs` ~804-824 can still find a uniquely named field), so a green run is not evidence against suspect (c). Suspect (a) may be benign: `module_with_owner_qualified_structs` has a `Node::Impl` arm (~344) that may already rewrite `owner_type` to the qualified name before the lookup. Suspect (b) is confirmed in code: `struct_declaration` matches only Struct/Class/Enum.
2. Bare-receiver method ambiguity: `files[path].as_str()` on a `Dict<text, SdnValue>` index gave `CODEGEN-AMBIGUOUS-METHOD` (4 candidates). Covered by the OPEN `doc/08_tracking/bug/codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`; this is a new site.
3. FIXED 2026-11-27 (seed simple-local-20261127m: bare string-literal statements are no longer counted; unit tests in exec_core.rs). Docstring counted as a skipped top-level statement: `jit_skipped_top_level_statements` in `src/compiler_rust/driver/src/exec_core.rs` (the `N::Expression(_)` arm, ~line 466) counts a bare string literal above a `pub fn` as a statement the JIT would skip and demotes the whole entry module. Other entry-capable files with the pattern: `src/app/ui/chrome_showcase/main.spl`, `startup_aspect_packs.spl:91`, `smf_elf_parser.spl:240`, `smf_writer.spl:184`. Fix in the seed: ignore bare string-literal expression statements (docstrings).

## Post-source_closure stall: measured (2026-11-27, seed simple-local-20261127h, worktree c27-census)

The silent period after `source_closure 93/93` is NOT a hang and NOT clang/lld/cargo (no such children ever
appear). Phase map for `native-build <entry>` on a 3-line entry:

1. Coordinator SCV admission/inventory: 331 s cold-init (`SIMPLE_SCV_INVENTORY_COLD_INIT=1`), **209 s** on the
   next run WITHOUT the env var, **21-24 s** from the run after that (journal/cursor now warm in `build/scv`).
   Iterate WITHOUT `SIMPLE_SCV_INVENTORY_COLD_INIT` once one cold-init has completed in the checkout.
2. Parse shard child (`run src/app/cli/parse_shard_main.spl --parse-fibers=0/1`, default `SIMPLE_PARSE_SHARDING`):
   source_closure 93 files in ~125-132 s, then the FileFiber parse loop
   (`_driver_run_parse_fibers`, `src/compiler/80.driver/driver_parse_shard_entry.spl`) is the silent part:
   one busy core, ~2 GB WS. New `[build-trace] parse-fibers:file:{start,parsed,tldr-done}` points (this change)
   show per-file cost: io_runtime.spl 2 KB 4.3 s parse + 0.3 s TLDR; external_text.spl 22 KB 55 s parse + 83 s TLDR;
   file_text_session.spl 17 KB 40 s parse + 40 s TLDR; i.e. ~2.5 ms/byte parse + ~2-4 ms/byte TLDR summary.
   7 files took 300 s; with 93 files this phase alone is well over 30 min. The shard is only a cache warmer
   (its output is parser/TLDR cache files), and HIR shards (hir=3) and the final worker repeat the same
   frontend work afterwards.
3. `SIMPLE_PARSE_SHARDING=0` skips parse AND HIR warm pools (admission 23 s) but then
   `mir_parallel=-1` ("memory budget cannot fit a MIR worker alongside the coordinator", coordinator RSS ~3.5 GB)
   fails with `error: MIR shard admission refused`; add `SIMPLE_MIR_SHARDING=0` to reach the single final worker.
4. Final worker (`run src/app/cli/native_build_worker.spl`): ~1 cpu-s per wall-s, silent (on Windows its stdout is captured by
   `process_run_timeout_live` until exit), >12 min and still running when last sampled.

Root cause of the slowness (from code reading, Fable review): the coordinator forces the interpreter on its children.
`native_build_main.spl:2793-2799` sets `SIMPLE_EXECUTION_MODE=interpret` when unset on a non-bootstrap route; `run_parse_shards` spawns `parse_shard_main.spl` (and later the final worker) with the inherited env, and the seed maps `interpret` to `ExecutionMode::Interpret` (`exec_core.rs:160`), so the JIT is never tried (no demotion line). Parse alone is ~400 B/s, parse + TLDR ~160-210 B/s. Forced interpretation was introduced after `native_build_direct_seed_jit_hang_2026-07-30.md`. Probe: export `SIMPLE_EXECUTION_MODE=jit` in the outer shell (the coordinator only overrides an empty mode). Fast iteration recipe: `SIMPLE_PARSE_SHARDING=0 SIMPLE_MIR_SHARDING=0 SIMPLE_BUILD_TRACE=1`
after one warm-up admission.

Run 4 result (`SIMPLE_PARSE_SHARDING=0 SIMPLE_MIR_SHARDING=0`): admission 21 s, then the single final worker ran
the full 2400 s `timeout` cap (coordinator saw rc=143 at +2337 s; worker CPU ~1 core, WS ~2 GB, no child
processes, no clang/lld ever spawned) and produced no exe, so the smoke output (`true` / `false`) is still NOT
reached and todo 478 / the plan-doc "STILL OWED native link smoke" stay open. The worker's `[build]` progress
lines are captured on Windows (`process_run_bounded` / `process_run_timeout_windows`; Unix relays live) and not echoed until exit, so its internal phase at the kill is
unknown; next step is to make the worker's stdout live (or `SIMPLE_NATIVE_BUILD_WORKER_SPAWN_TRACE`) and re-run
with a >2400 s cap, or run the children on JIT (see root cause above).

## JIT children probe (2026-11-27, seed simple-local-20261127l, worktree c27-census)

`SIMPLE_EXECUTION_MODE=jit SIMPLE_BUILD_TRACE=1 ... native-build smoke.spl` (children inherit `jit`):

| phase | interpreted (before) | JIT children (measured) |
|---|---|---|
| parse shard `source_closure` 93 files | 125-132 s | 1.8-2.0 s |
| parse shard FileFiber loop | 7 files = 300 s (io_runtime.spl 4.3 s parse) | whole shard ~5-7 s; io_runtime.spl 2.3 KB parse 0.4 s (+0.0 s TLDR); 6 shards x 11-22 files done in the ~57 s between `coordinator:shards parse=6` and `mir_parallel` |
| coordinator admission (warm) | 21-24 s | 17 s to worker:select |
| MIR shard admission (default) | refused (`mir_parallel=-1`) | still refused: needs `SIMPLE_MIR_SHARDING=0` (coordinator RSS ~3.5 GB) |

No `[engine-demotion] reason=jit-compile-error` and no JIT hang (no flat-CPU stall) in coordinator or parse children; only the known
`hybrid-interp-splice` extern lines. Memory: coordinator WS ~3.4 GB, each parse child ~0.8 GB, final worker ~2.0-2.1 GB, flat.

The 2026-07-30 doc's own final section already re-scoped that "JIT hang" as `process_run_timeout` buffering stdout until exit
(not a hang), so the forced `interpret` default had no standing reason. Change: `run_native_build_worker` now sets
`SIMPLE_EXECUTION_MODE=jit` (was `interpret`) when unset on the non-bootstrap route (`native_build_main.spl`); the
`== "interpret"` clamps (parse cap 1, `--low-memory`) now apply only when the operator opts into interpret.

STILL OPEN: with `SIMPLE_MIR_SHARDING=0 SIMPLE_EXECUTION_MODE=jit` the single final worker (`native_build_worker.spl`) ran to the
2400 s cap (rc=143, ~2200 cpu-s, WS flat ~2.1 GB, no clang/lld children) and produced no exe, so the smoke (`true`/`false`) is still
NOT reached; todo 478 and the plan-doc owed item stay open. JIT therefore fixes the parse-warm phase (>30 min -> <10 s) but not the
final worker; its internal phase is invisible on Windows because its stdout (74 KB) and stderr (1.3 MB) are only returned at exit and
are discarded on timeout kill. Next: make the worker's output live (or flush captured stdout on timeout) to see which phase
(HIR serial lowering after "HIR warm-up pool refused: no closure request published", MIR, LLVM) consumes the time.

Follow-up: verify that JIT-run parse shards write front-end cache entries identical to interpreted ones (the lint entry has a known
JIT wrong-answer precedent, `src/compiler_rust/driver/src/exec_core.rs:1971-1987`); a faster but divergent cache warm would be silent.

## Live worker log + phase breakdown (2026-11-27, seed simple-local-20261127m, worktree c27-variant)

Visibility fix: `SIMPLE_BUILD_TRACE_FILE=<path>` (with `SIMPLE_BUILD_TRACE=1`) makes `log_build_trace` append every
`[build-trace]` line to that file per line, in the coordinator, parse shards and the final worker alike (env is inherited).
`SIMPLE_BUILD_PROGRESS_EVENTS=<path>` already did the same for `[build]` progress events. Both work on Windows while the
worker is still running and survive the cap kill. New trace points: `driver:stage_parse:start`,
`driver:stage_lower_hir:start/done`.

Second defect found by this run (fixed): with `SIMPLE_SCV_INVENTORY_COLD_INIT=1` on the JIT coordinator the cold-init scan died with
`match statement exhausted without matching any pattern` at `inventory_events.spl:474` for the skipped non-source path
`examples/10_tooling/README.md` (`Ok(None)` of `Result<CompileSourceEventV1?, text>` matched neither the `Ok(Some(ev))` nor the
`Ok(None)` arm) -> `git-event-refresh-failed`. The match now uses `case Ok(item): if item.is_some(): events.push(item!)`.

Phase breakdown of the smoke (`SIMPLE_MIR_SHARDING=0`, JIT children), wall seconds from coordinator start:

| phase | time |
|---|---|
| SCV cold-init scan + decode (102761 git rows, 47274 inventory rows) | 0 -> 720 s (dominant; one-time per worktree) |
| parse shards (5, warm) + hir=2 shard decision | 720 -> 794 s |
| final worker start -> `driver:compile:start` | 126 s |
| `driver:load_sources` (192 sources, 2.1 MB) | 90 s (done at worker +217 s) |
| after `load_sources:done` (stage_parse / stage_lower_hir of the 192-source closure) | silent for >600 s when I stopped it (worker +217 s .. +830 s); no further trace line, so the time is inside stage_parse or serial HIR lowering; the new trace points will say which |

Smoke NOT completed (stopped at ~14 min of worker time to honour the time box); todo 478 and the plan-doc "STILL OWED" stay open.
Next: rerun with the new `stage_parse/stage_lower_hir` trace points (cold init is now cached, so ~80 s to worker start).

Review follow-ups: the trace sink is now one file per process, `<SIMPLE_BUILD_TRACE_FILE>.<pid>` (`file_append` is size +
positioned write, not O_APPEND, so shards sharing one path could overwrite each other). Note a set
`SIMPLE_BUILD_TRACE_FILE` value folds into the `native_noop_request_v1` identity: reuse the same path across reruns or expect a
no-op cache miss. The same `Ok(None)`/`Ok(Some(ev))` pattern in `compiler_inventory_event_push_cost_v1` got the same rewrite.
Miscompile record: `native_build_jit_nested_option_result_match_exhausted_2026-11-27.md`.
## Item 2 resolved in the seed (2026-11-27)

The `files[path].as_str()` ambiguity was a seed HIR typing bug (nested tail
`match` statement typed NIL/ANY), not Dict indexing; fixed in
`hir/lower/expr/control.rs::lower_do_block`. The explicit
`val entry: SdnValue = files[path]` workaround in `simpleos_sysroot_receipt.spl`
is no longer required once a seed with this fix is deployed. See
`codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`.

## Final worker phase breakdown: stage_parse runs at ~500 chars/s (2026-11-27, seed simple-local-20261127r, worktree c27-variant)

Run: `SIMPLE_COMPILER_PHASE_PROFILE=1 SIMPLE_MIR_SHARDING=0 SIMPLE_BUILD_TRACE=1 SIMPLE_BUILD_TRACE_FILE=...` (`log_phase`
lines now also tee to the trace file, so the worker's `[BOOTSTRAP-PHASE]` stream is live on Windows). Worker timeline
(wall ms from `worker:start`):

| phase | time |
|---|---|
| worker start -> `compile:start` | 161 s |
| `phase1:load_sources` bulk closure (192 sources, 2.1 MB; each `closure:already-loaded` step ~2 s) | 161 s -> 394 s (233 s) |
| owner copy | 394 -> 411 s |
| `phase2:parse` (stage_parse) start | 476 s |
| stage_parse per file (serial, in the worker) | see below |

Per-file serial parse in the worker (`phase2:parse:file:start/done`, chars -> wall):

| file | chars | wall |
|---|---|---|
| test/.../smoke.spl | 134 | 0.9 s |
| sosix/fs_v1.spl | 2354 | 2.8 s |
| io/dir_ops.spl | 5029 | 9.5 s |
| io/file_ops.spl | 30294 | 54.7 s |
| io_runtime.spl | 43584 | 101.8 s |

That is ~0.4-2 ms per char (roughly 500 chars/s, mildly superlinear), i.e. interpreter speed. The same files parse in
0.2-0.4 s inside the JIT parse shards. Extrapolated to 2.1 MB, the final worker's serial re-parse of the 192-source closure is
on the order of 1 hour, which is the "silent >600 s after load_sources:done" and the 2400 s cap hit. So the culprit is
`stage_parse` (`parse_all_committing_impl`) re-parsing every source inside the single final worker at interpreted speed even
though the shards already parsed and cached them; HIR was never reached. Stopped at ~11 min of parse (6 of 192 files done).

Open: either (a) confirm the worker really runs the parse functions on JIT (the shards do; the worker shows interpreter-class
speed) -- check `SIMPLE_EXECUTION_MODE` as seen by the worker and any `engine-demotion` line, or (b) have stage_parse consume the
shards' parse/front-end cache instead of re-parsing. Also: load_sources closure scan costs 233 s and worker start 161 s.

Side effect measured: any edit under `src/**` invalidates the SCV cold-init cache (the cold-init scan took 1027 s on the rerun
instead of ~270 s), so each trace-point edit costs ~17 min before the worker starts.

Trace additions (kept): `log_phase` tee to `SIMPLE_BUILD_TRACE_FILE`; `driver:hir:streaming:prelude_done`,
`driver:hir:streaming:visit_order n=`, and per-module `driver:hir:module:start pos= path=` in the streaming HIR loop
(untested: HIR was not reached).

## d29-f: the worker entry itself demotes to the interpreter (2026-11-27)

Seed `simple-local-20261127r.exe`, `SIMPLE_EXECUTION_MODE=jit run src/app/cli/native_build_worker.spl --help`
(the entry prints "internal entrypoint" and exits 1, so this isolates module load + JIT compile):

- DEMOTED. `[engine-demotion] reason=jit-compile-error detail=HIR lowering error: ambiguous call to
  llvm_int8_type_in_context: 2 co-compiled definitions (src/lib/nogc_async_mut/sffi/llvm_types.spl,
  src/lib/nogc_sync_mut/sffi/llvm_types.spl) ... [compiler_cross_module_private_symbol_collision]`.
  Raised for src/plugins/backend_llvm_lib/llvm_lib_type_mapper.spl, then llvm_lib_translate_expr.spl.
  Cause: `use std.sffi.llvm.*` (also in llvm_lib_backend.spl, llvm_lib_translate.spl) resolves to both
  lane copies, so every `llvm_*` call is ambiguous. Whole worker closure falls back to the interpreter
  (2m04s to demote, then interpreted).
- Fix: those four files now import `std.nogc_sync_mut.sffi.llvm.*` explicitly. After it,
  the llvm ambiguity is gone, but a second jit-compile-error remained (see addendum below); after the addendum only `reason=hybrid-interp-splice` for `rt_*` externs
  (cache_host/heap/sysctl/etc., expected on this seed) plus 7 CODEGEN-AMBIGUOUS-METHOD lines
  (`CudaTypeMapper.map_tuple` bare `map`, 4 candidates) - not fixed here, separate shape.
- Timings (--help, wall): JIT before fix 2m04 (demote + interp); JIT after fix 3m29 (full JIT compile of
  the closure); forced interpret 1m22. So for this entry the interpreter is faster to first output;
  JIT is not a win on cold start, and the >600 s silence after load_sources is not explained by this
  demotion alone (the c27 stage trace owns that). Logs: scratchpad d29f/{jit,jit2,jit3,interp}.log.

Worker mode (answer to the trace lane): native_build_main.spl:2794-2803 sets `SIMPLE_EXECUTION_MODE=jit`
in the coordinator env when it is unset and the route is not a compiled bootstrap capsule, and the worker
inherits it, so the worker REQUESTS jit. Before the fix above its closure then hit the
`jit-compile-error` demotion and ran fully interpreted, which matches stage_parse at ~500 chars/s
(interpreter speed) while the separately spawned parse shards (a different, smaller closure) stay on JIT
at 0.2-0.4 s per file. Re-measure stage_parse in the real worker with this fix before concluding; the
shards' front-end cache reuse by stage_parse was not investigated (time box).

### d29-f addendum: second demotion, zero jit-compile-error after fix (2026-11-27)

Correction: after the llvm import fix the worker STILL demoted (`CODEGEN-AMBIGUOUS-METHOD` in
`CudaTypeMapper.map_tuple`, bare `map` on an untyped `elements.enumerate()` receiver, 4 candidates, then
`jit-compile-error detail=src/app/cli/native_build_worker.spl` + "JIT compilation failed, falling back
to interpreter"). Fixed by replacing that `.enumerate().map(...)` with an explicit typed loop in
src/plugins/backend_cuda/cuda_type_mapper.spl. Demotion count (jit-compile-error / JIT compilation
failed / CODEGEN-AMBIGUOUS): before any fix 1 / 1 / 0 (jit.log), after llvm fix only 1 / 1 / 7 (jit3.log),
after cuda fix 0 / 0 / 0 (jit4.log). Remaining: `hybrid-interp-splice` for rt_* externs only (not an error).
`--help` JIT wall 2m50. Spec stage3_explicit_owner_types_spec.spl 2/2 on seed r.
The `[engine-demotion]` lines are printed by the Rust seed (src/compiler_rust/common/src/engine_receipt.rs
and the driver), so teeing them into SIMPLE_BUILD_TRACE_FILE from Simple source is not possible; skipped.

### d29-f correction (2026-11-27): "0/0/0" was vacuous

The earlier "after cuda fix 0 / 0 / 0" run hard-failed before main with 140 `semantic: private fn ... is not
visible` errors (the demotion counters were zero only because it never got that far). Fixed by making the
cross-module-used fns `pub`: all `fn llvm_*` in src/lib/nogc_sync_mut/sffi/{llvm_types,llvm_codegen,
llvm_target,llvm_loader}.spl, plus 16 compiler fns (auto_vectorize_codegen/analysis, module_lowering
hir_module_surface_index, mir_lowering_stmts, mir_instruction_support, feature_caps_types). Genuine result
(jit6.log): `SIMPLE_EXECUTION_MODE=jit run native_build_worker.spl --help` -> rc=1, last line
`error: native_build_worker.spl is an internal entrypoint`, 0 "is not visible", 0 jit-compile-error /
JIT compilation failed / CODEGEN-AMBIGUOUS; only `hybrid-interp-splice` (rt_* externs) remains.
## llvm_lib import fix (3ae9ee35013) does not un-demote the final worker (2026-11-27, seed r)

Rerun with the `std.nogc_sync_mut.sffi.llvm.*` import fix cherry-picked: the worker is still interpreter-speed. stage_parse per file,
before -> after: smoke.spl (134 chars) 0.9 -> 1.5 s, fs_v1.spl (2354) 2.8 -> 5.1 s, dir_ops.spl (5029) 9.5 -> 15.1 s (box was
loaded, so slower, not faster); load_sources bulk closure 233 s -> 181 s of worker time but the worker start rose to 334 s. Stopped
at the third file. Per the coordinator, a further demotion (`CudaTypeMapper.map_tuple` CODEGEN-AMBIGUOUS-METHOD) still drops the whole
worker closure to the interpreter; that fix is pending in lane d29-f. The worker's `[engine-demotion]` lines are invisible on
Windows (stdout returned at exit only); consider teeing `[engine-demotion]` to the trace file too. No exe; todo 478 stays open.

## Run with d29-f fixes (140bcf8350a) fails at the semantic check (2026-11-27, seed r)

Cherry-picked the d29-f src fixes (llvm pin, CudaTypeMapper.map_tuple, dangling export) on this worktree's base (b46b620940e,
39 commits behind origin) and reran the smoke. Cold init 1368 s, then `coordinator:shards parse=0 hir=1 mir_parallel=0` (the shards
no longer run: the worker was handed everything) and the final worker returned rc=1 after 171 s:
`error: semantic: private fn create_alias_guard_block of module ...\mir_opt\auto_vectorize_codegen.spl ... mark it pub or export it`,
imported by `src/compiler/60.mir_opt/mir_opt/_AutoVectorize/rewrite.spl:50`. Every fn in `auto_vectorize_codegen.spl` is non-pub and
origin/release/1.0.0 is identical there, so this is a tree defect that the now-compiling worker surfaces (previously the demoted
interpreter did not enforce it). stage_parse was therefore NOT reached and no per-file parse timing was measured. Next: make the
imported fns of auto_vectorize_codegen.spl `pub` (or fix the import), then rerun; expect ~25 min per attempt (cold init).

## Run with d29-f 0e506dcf40e: worker is JIT, frontend+HIR+MIR in 79 s; new blocker at backend session open (2026-11-27, seed r)

Base cc85cd23dda + d29-f commits (llvm pin, map_tuple, pub visibility). Final worker timeline (ms from worker start):

| phase | before (interpreted) | now (JIT) |
|---|---|---|
| worker start -> compile:start | 161-334 s | 22.9 s |
| load_sources bulk closure (192 sources) | 181-233 s | 1.9 s |
| stage_parse (93 modules) | est. ~1 h (io_runtime.spl 101.8 s) | 25.5 s (io_runtime.spl 0.47 s, process_ops.spl 195 KB 2.1 s) |
| HIR (phase3) | never reached | 51.4 -> 70.4 s (19 s) |
| MIR + mir_verify (8 modules, 227 fns) | never reached | to 78.6 s |
| aot:native_session_open | - | rc=70 `Runtime error: unresolved symbol -- ... code-generation dispatch gap`, at 78.9 s |

So the stage_parse blocker is fixed (interpreter demotion was the cause; ~200x faster). The worker now dies in
`BackendSessionOwnedLeaseV2.open(request)` (`driver_aot_native_output.spl:2498`) with an unresolved symbol (name not printed by the
seed's `error_handling.rs` message; the worker's own stderr tail ends right after `mir_verify` idx=8). No exe; todo 478 and the plan
STILL OWED stay open. Next: find the unresolved callee in the backend-session open path (run the worker under SIMPLE_EXECUTION_MODE=jit
with a seed that names the symbol, or bisect `BackendSessionOwnedLeaseV2.open`), then rerun; coordinator part (cold init) took 1435 s.

## RESOLVED: backend session open dispatch gap, exe produced (2026-11-28, seed r, lane c27-variant)

The unresolved symbol was `CraneliftCodegenState.supports_target` (the seed prints it on the line BEFORE the generic
"unresolved symbol" text: `Runtime error: Function '<name>' not found`; the earlier tail missed it). Cause: `src/compiler/70.backend/codegen.spl`
declared `type Codegen = CraneliftCodegenState`, re-exported from `src/compiler/70.backend/__init__.spl`, which collides by simple name
with the `Codegen` trait in `codegen_types.spl`. Under JIT, trait-object calls such as `codegen.supports_target(target)` in
`builtin_adapter.spl:204` (receiver from `CodegenFactory.create`) resolved to the alias's struct, which has no such method. Fix: delete the
unused alias and its re-export (no importer of `Codegen` from `compiler.backend` / `compiler.backend.codegen` exists).

Fast harness (about 1 min, no cold init): a .spl that installs the K1 backend table (as `native_build_worker.spl` does) and calls
`BackendSessionOwnedLeaseV2.open(driver_aot_backend_plugin_request_v1("llvm", ...))`, run with `SIMPLE_EXECUTION_MODE=jit SIMPLE_MIR_SHARDING=0`.
Before: `Function 'CraneliftCodegenState.supports_target' not found`, rc 70. After: `open ok`.

Full smoke (with the d29-f commits applied; seed r; `SIMPLE_MIR_SHARDING=0`): `native-build smoke.spl -o smoke.exe` rc=0, 209920-byte exe, running it
prints `true` then `false`. Timeline: shards done at 659 s, worker returned at 892 s (cold init included). Entry was a 3-line print stand-in, not
`dir_sync` itself. Todo 478 closed. Depends on the d29-f lane (work/native-build-worker-engine-mode-20261127) landing.
