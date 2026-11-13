# Phase 3 compile-error reporting catalog (2026-11-13)

- **Status:** OPEN (catalog; fix groups (b) `f85e72b895c` and (c) `ea3369d688d` committed on the lane; rest filed below)
- **Lane:** `work/compile-error-reporting-20261113`
- **Question asked:** does every compile failure seen in the Phase 3 build print
  a proper, actionable message (phase, module, file:line:col, error code, cause;
  for crashes: module + signal + last breadcrumb)?

## Evidence sources and producer identity

| tag | what | producer (the binary that PRINTS the message) |
|-----|------|-----|
| **C** | `/home/yoon/dev/simple-census-20261113/build/p3-census.log` (28,166 lines) | run-19 `stage2-admitted/simple`, pinned src `3197fdaa5ed6` |
| **P** | single-module probes `build/errprobe/src/p*.spl` via `env_p3.sh`, 6G cap | run-21 `stage2-admitted/simple`, pinned src `554460a6b85a` |
| **M** | manual Phase 3 shard agents `simple-mp3-*-20261113/build/mp3-*` (read-only) | run-21 S2 over release `f790f7f266e` / `4028c047eea` |

A message printed by Stage 2 comes from Stage 2's OWN (older) driver code; a
source fix here reaches the Phase 3 build only after the next producer rebuild.
`da13010c811` (the #8831 unproven-call-origin gate) is **not** an ancestor of
run-21's `554460a6b85a`, so the mp3 agents still hit the bare panic (case 11).

Probe recipe (one at a time, `free -g` available >= 25):
`/tmp/claude-1000/-home-yoon-dev-simple/1c5553d5-2b52-4fb8-a27f-eb455a008041/scratchpad/errprobe/probe.sh <name> [--emit-object] -o <out>`
(in-process positional `native-build`, `--backend cranelift --runtime-bundle core-c-bootstrap --threads 1`).

## Catalog

"Missing" uses the goal's fields: phase / module / file:line:col / code / cause /
(crash) signal + crashed module + breadcrumb. **Code** is missing from every
driver message (case 28) and is not repeated per row.

| # | class (src) | current output (verbatim, trimmed) | missing | emitting site | after / spec |
|---|---|---|---|---|---|
| 1 | parse error (P p1) | `error: in-process native-build: parse error in build/errprobe/src/p1_parse.spl: 4:1:expected ), got Dedent ''` | space after `4:1:`; path and position are separate tokens (`path: L:C:` not `path:L:C`) | `80.driver/driver_parse_diagnostic.spl:16` | adequate; cosmetic, not fixed |
| 2 | HIR unresolved name (P p3) | `HIR lowering error in .../p3_unresolved_fn.spl: unresolved name: nope_fn at .../p3_unresolved_fn.spl:2:5` | — | HIR lowering error list | adequate |
| 3 | MIR unresolved method (P p4, C 26036/26502) | `[first-compile-error] MIR lowering error: unresolved method call: nope_method route=runtime-fallback key=::nope_method ... at .../p4_unresolved_method.spl:3:5` | — (module named in the preceding `[mir-module-failure]`) | `50.mir/_MirLoweringExpr/method_calls_literals.spl:2519` | adequate |
| 4 | unresolved import (P p6) | `unresolved import 'std.nonexistent_mod' (used in .../p6_missing_import.spl): no source file found ...` | line:col of the `use` | `80.driver/driver_source_pipeline_loading.spl:1181` | adequate; position not fixed |
| 5 | link: entry has no `main` (P p5, M A/B) | `Hosted native linking failed: ... mold: error: undefined symbol: __simple_main >>> referenced by simple_entry.c` | plain-language cause ("entry module defines no main; pass --emit-object") | `80.driver/driver_aot_native_output.spl:1980` (`driver_native_link_failure_result`) | adequate (linker text is exact); hint not added |
| 6 | **type mismatch accepted silently** (P p2 `val x: i64 = "s"`, p7 `val t: text = 5`) | *(nothing)* — `rc=0`, object emitted | the whole error: LOST | native-build pipeline runs no type check that rejects these | **not a reporting defect** — a checking gap; filed for the type-system owner, out of this lane |
| 7 | MIR enum payload mismatch (C 26182, 26465) | `[go-to-end] failed stage=mir module=compiler.hir.hir_lowering.statements: MIR lowering error: enum construction '...HirStmtKind.Let': payload type mismatch at 1; function=lower_hir_stmt module=... payload_at=<path>:L:C` | — | `50.mir/_MirLoweringExpr/enum_constructor_payload.spl:476`, `80.driver/driver_build/go_to_end.spl:89` | adequate |
| 8 | MIR `MirConstValue.Str` payload (C 26263) | same shape as 7, `function=make_register_static_driver_call` | — | same | adequate |
| 9 | borrow: short borrow escapes (C 26468, 26475) | `[go-to-end] failed stage=borrow module=compiler.backend.linker.lld_sffi: 43:1: short borrow escapes: ... [fn ...lld_elf_link, mir point 5][mir-slow] ...` | source FILE (only module + L:C); line glued to next record (case 20) | `55.borrow/borrow_check/borrow_graph.spl:816`, `go_to_end.spl:89` | module+L:C is resolvable; file not added |
| 10 | MIR struct re-registered (C 25940-25946) | `[mir-lower] WARNING: struct/class name 'JoinPoint' re-registered with a DIFFERENT field list (existing=[...] vs new=[...]; keeping EXISTING)` | which two modules collide | `50.mir/_MirLowering/module_lowering.spl:1939` | warning, not a failure; not fixed |
| 11 | **unproven call origin — backend panic** (C 26519, 26521; live on run-21) | `MIR call target lacks proven source/runtime/foreign origin: callee=env_get` then SIGABRT | module, function, call site; kills the worker | `50.mir/mir_instruction_support.spl:301` (`mir_call_origin_uses_local_symbols_named`) | backstop only once the gate (12) runs first; panic text unchanged (names callee). Producer rebuild needed |
| 12 | unproven call origin — module gate (#8831, source only) | `unproven-call-origin: MIR call target lacks proven source/runtime/foreign origin: callee=env_get fn=read_home` | module, call site L:C | `50.mir/mir_instruction_graph.spl:601` | **FIXED (b)** `f85e72b895c`: `... callee=env_get fn=read_home module=<m> at=<file>:L:C`; spec `test/01_unit/compiler/mir/unproven_call_origin_module_census_spec.spl` |
| 13 | **shard worker CRASH row** (C 26522) | `[mir-shard] owner=1/2@0 status=CRASH exit=-134 claimed=809 sealed=809 finished=false` | signal NAME, crashed module, phase, breadcrumb | `src/app/cli/native_build_main.spl:1354` | **FIXED (c)** `ea3369d688d`: `... finished=false signal=SIGABRT(6)` + `[mir-shard] owner=1/2@0 ICE[codegen] module <m> (attributed): worker died inside this module (worker exit status -134 signal=SIGABRT(6)); source <path>` + merged ICE summary; specs `test/01_unit/app/cli/native_build_exit_status_spec.spl`, `test/01_unit/compiler/driver/ice_dead_pid_attribution_spec.spl` |
| 14 | 1619 `failed module: CRASH <m>` rows (C) | `[mir-shard] failed module: CRASH app.bug.workaround_index` x1619 | which ONE module was in flight; the rest only "not finished" | `native_build_main.spl:1424` (`hir_shard_recovery_failed_rows_v1`) | rows kept (they are the ledger truth); the in-flight module is now printed by the 13 line BEFORE them |
| 15 | pool outcome (C 28143) | `[mir-shard] outcome=fail exit=1 failed_modules=1619 ... blocked=error: MIR shard aggregate failure; link and artifact publication blocked` | pointer to the cause; glued (case 20) | `native_build_main.spl:1535`, `bootstrap_main.spl:236` | cause now carried by 13; not changed |
| 16 | no `[first-compile-error]` for a worker crash (C) | *(absent)* | first-error line for the crash | `native_file_worker_first_error_line_v1` only reads a published reason | the 13 attribution line is the first error; not separately changed |
| 17 | HIR cache store refused (C 19465) | `[hir-cache-store] refused reason=decode detail=reader kind=malformed detail=enum wire enum allocation failed line=5368/20870 ... module=<path>; entry not stored ...` | — (cache warning, compile continues) | `80.driver/driver_hir_cache.spl:1037` | adequate |
| 18 | HIR re-export chase unresolved (C x26, M D.log) | `[hir-reexport-chase-unresolved] facade=... item=... local=... importer=<path>: the facade neither declares ...` | line:col of the import | `20.hir/hir_lowering/_Items/module_import_registration.spl:1181` | warning; not fixed |
| 19 | HIR callable-dep origin unresolved (C x7) | `[hir-callable-dep-origin-unresolved] owner=compiler.common.runtime_value_v1 dependency=Value: no declaration ...` | file:line | `20.hir/hir_lowering/_Items/module_reexport_materialization.spl:1056` | warning; not fixed |
| 20 | **eprint lines glued (no trailing newline)** (C 26468/26475/26522/28143, P every run: `build-session: end disabled (opt-in)rc=0`) | hexdump: `finished=false[mir-shard] owner=` (no `\n`) | the record separator | `lib/nogc_sync_mut/io/process_ops.spl:3182` `rt_stderr_write("{msg}\n")` as compiled INTO Stage 2 | **producer-build defect, not current source**: p8 (`eprint` call form + `rt_stderr_write("{m}\n")`) compiled BY run-21 S2 prints `A1\nB2\nx=C3\nC3\nD4\n` correctly. Fixed by the next producer generation; no source change |
| 21 | `[bootstrap-error-count]` / `[collect-all]` glued (P p2-p7) | `[bootstrap-error-count] source_idx=0 point=entry count=0[build] phase=hir ...` | separator | `80.driver/driver_hir_pipeline_lowering.spl:2028` | same as 20 |
| 22 | error-list print SEGV (guide item 6: int-boxed `RtCoreString` handle) | not reproduced: run-21 S2 printed the `error: in-process native-build: {err}` list for parse (p1), HIR (p3), MIR (p4), link (p5), import (p6) | — | `src/app/cli/bootstrap_main.spl:771` | **not reproduced on run-21**; observed on run-27e (`p2shard-17`). Keep the gdb recipe; no source change without a repro |
| 23 | SIGSEGV after `rebuilt 1`, no message (M mp3-0 `A.log`, `workaround_index` without `--emit-object`) | `Cache: reused 0 modules; rebuilt 1.` / `Command terminated by signal 11` | everything | link-error print path (where 5 prints) | not reproduced: same S2 + same module (`pA_real`) prints case 5. A differs only by source tree; needs the mp3-0 agent's core/gdb trace |
| 24 | `to_text()` destroys error text (`<invalid-heap:0x..>` / empty; stage2_aot_error_message_lost_invalid_heap_2026-09-06) | not reproduced (no backend `Err` probe on run-21) | — | `80.driver/driver_aot_native_output.spl:4590` | current source renders inside the binding arm and copies via `compileerror_owned_text`; a seed spec of the pure formatter would prove nothing about native rendering. Verify with the first real backend `Err` |
| 25 | single-worker crash tail (guide item 4) | `error: native-build worker terminated with signal 6 before producing a binary; NOT a compile failure.` | signal NAME | `native_build_main.spl:2486` | **FIXED (c)** `ea3369d688d`: `... terminated with signal 6 (SIGABRT) before producing a binary ...` |
| 26 | shard exit hint is Windows-only | POSIX `-134` gets no hint | — | `src/app/cli/shard_mem_clamp.spl:449` | superseded by the 13 signal field |
| 27 | duplicate `unresolved method call 'is_none'` warning (C 26033-26034) | identical line twice | — | two call sites at `persisted_graph.spl:96` | not a defect (two calls) |
| 28 | **no error code anywhere in the driver pipeline** | — | code | `Diagnostic.code` exists (`00.common/diagnostics/diagnostic.spl:12`), `error_codes.spl` has 179 codes, but `CompileResult` carries `[text]` and every driver/HIR/MIR emitter formats text | infra gap, filed: carry `Diagnostic` (or `code` + text) through `CompileResult`; do not invent per-emitter codes |
| 29 | output-mode bind refusal (M `a.log`) | `Error: could not bind native-build output mode 'entry'` | why it failed / what to pass | `src/app/cli/bootstrap_main.spl:716` | CLI usage error; not fixed |
| 30 | `no verified object ... (rc=0)` (M `c1.err`) | `error: no verified object for <src> in <cache>/build_cache.sdn (rc=0)` | — | lane script `compile_one.sh`, not the compiler | out of scope |

## Fix groups in this change

- **(b) unproven-call-origin gate names module + call site.** Each site line now
  ends `module=<module.name> at=<line>:<col>` (`at=?` when the instruction has no
  span). The driver already prefixes the failing unit and records it as a caught
  ICE. The backend panic (case 11) stays the backstop and keeps its text.
- **(c) shard worker crashes name the signal and the module.** The ledger pool
  (`run_ledger_shards`) now claims the ICE run directory when nobody else did, so
  its workers write per-pid breadcrumbs (the bootstrap `native-build` route
  never claimed one: the census pool ran with no breadcrumbs at all). On a
  failed reap it prints `signal=<NAME>(<n>)` on the status row and attributes
  the dead worker's open breadcrumbs (that pid only, not other live workers)
  through `ice_boundary_attribute_dead_pid_v1`, which records them in the ICE
  receipt. The single-worker tail line names the signal too.
  Side effect, stated: on the bootstrap route the shard workers now run with
  the ICE boundary on (mode `on` = record and continue,
  `driver_pipeline_lowering.spl:365`), exactly as they already did under the
  worker-launch route; `SIMPLE_ICE_BOUNDARY=off` restores the old behaviour.

## Not fixed here (owners)

- 6 (silent type mismatch) — type-system owner; a lost error, the most serious
  open row.
- 20/21 (glued lines) — closes with the next producer rebuild; re-check the
  first Phase 3 log for `[a-z]\][[]` junctions.
- 22/23/24 — need a reproduction on the current producer; recipes above.
- 28 (error codes) — diagnostics-infra owner.
