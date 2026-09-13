# Stage 3 self-host fails: E-MIR-TYPE-ZeroKind on `compile_specialized_template_release` scope-tail (macOS arm64)

**Date:** 2026-09-05
**Status:** OPEN — blocks the adhoc full-CLI lane at `5418d2075bb` on this host
**Area:** compiler / 50.mir lowering (stage2 pure-Simple compiler compiling itself)
**Related:** `zerokind_is_a_corrupt_aggregate_2026-09-03.md` (OPEN, root cause characterised, fix not identified),
`zerokind_roams_between_victims_avoidance_edits_are_not_fixes_2026-09-02.md`,
`a387009e6c7` (fix for the previous 6 Stage-3 ZeroKind victims, #274).

## Symptom

Adhoc chain run in a frozen detached worktree at `5418d2075bb` (contains the
`2da5aa6e` rt_* dual-lane commit):

1. `--strategy=adhoc --full-bootstrap --stop-after-stage2 --mode=dynload` — **Stage 2 admitted** (Rust seed compiling `bootstrap_main.spl`; sanity + receiver proofs pass; the stage2 binary compiles and runs a hello world).
2. `produce-bootstrap-planner-admission-v2.shs --target=//bootstrap:stage4 --reason=self-host-convergence-check --parent-compiler=<stage2>` — receipt produced and `--validate-bootstrap-receipt` passes.
3. `--strategy=adhoc --full-cli --bootstrap-receipt=<receipt>` — Stage 2 rebuilt and admitted, then **Stage 3 (stage2 -> bootstrap_main.spl, self-host) fails, exit 1**:

```
error: bootstrap MIR lowering: E-MIR-TYPE-ZeroKind: lower_type received a
well-formed HirType whose `kind` field is raw 0 (never written) while lowering
'scope-tail:compiler.driver.pipeline_fn.compile_specialized_template_release'
-- fix the PRODUCER that left kind unset, not lower_type
error: native-build worker exited with code 1.
  interpreter: .../build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/simple (exit code 1)
```

Driver then reports `Stage 3 unavailable — no provenance-verified compiler for
Stage 4` and `error: full CLI build requires a verified pure-Simple
stage2/stage3 compiler; refusing seed fallback` (exit 2). No
`build/bootstrap/full/` artifact is produced, so nothing can be deployed.

- Log: `build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log`
  (16,299 lines; the ZeroKind error appears exactly twice, both for the same
  victim, at lines 15915 and 16122).
- Emitter: `src/compiler/50.mir/_MirLowering/function_lowering.spl:1290`.
- Victim: `src/compiler/80.driver/pipeline_fn.spl:123-144` —
  `compile_specialized_template_release(...) -> text`, whose whole body is a
  single tail call `compile_specialized_template(..., OptimizationConfig.speed())`.
- Stage 2 (the same source compiled by the Rust seed) emits **zero** ZeroKind
  errors, so the SOURCE being compiled is not at fault; the emitter is the
  stage2 pure-Simple compiler. The 09-03 record characterises the class as a
  corrupt aggregate (memory-level, `disc=-1 kindzero=true`), P0, "sole
  remaining blocker for Stage-3 self-host on aarch64-apple-darwin" — so this
  is consistent with that pre-existing class. It is **not proven independent
  of `2da5aa6e`** (rt_* dual-lane C/Rust edits): the stage2 binary links the
  modified `runtime.c` / `value_ops.rs`, and a memory-level corruption could
  be influenced by runtime changes. Ruling that out requires a Stage-3 run at
  `2da5aa6e^` (hours). The fixes `a387009e6c7` / `a35cddc2271` are present at
  `5418d2075bb`; this victim name appears in none of the three prior records.

## Why it is a new victim, not the 09-02 one

`a387009e6c7` fixed six Stage-3 victims in `pipeline_fn.spl`
(`CompiledUnit.entry_point`); this scope-tail victim is in the same file but a
different function shape (a trailing-call scope tail returning `text`), which
matches the "roams between victims" pattern in the 09-02 record: avoidance
edits move the corrupt aggregate rather than remove it.

## Environment

macOS 25.5.0 arm64, LLVM 18 (`/opt/homebrew/opt/llvm@18`), platform triple
`aarch64-apple-darwin`, 5 native-build jobs, dynload mode. Rust seed rebuilt in
the same run (`rust-seed-build.log` green).

## Next step

Root-cause in the HIR producer per the 09-03 record; re-run the chain from the
Stage 2 trust root (the runtime snapshot digest pins every non-vendor file
under `src/runtime`, so any compiler/runtime edit invalidates the receipt).

---

## Addendum 2026-09-06 — victim relocated, mechanism class narrowed, no repro obtained

Static + log investigation on the frozen worktree of the 09-05 run (the worktree
and its admitted stage2 binary were lost mid-session when the host process died;
nothing below was verified by a fresh run — see "Not verified").

### 1. The victim is the ENTRY module, not `pipeline_fn.spl`

`stage3-native-build.log` (first block, all lines are stderr `eprint`s, so their
order is real):

```
15980  [bootstrap-flat-entry] index=0 modules=771 functions=34
       ... 140 x [mir-prescan] HirStmtKind.Expr ...
16122  error: bootstrap MIR lowering: E-MIR-TYPE-ZeroKind ... 'scope-tail:...compile_specialized_template_release'
```

`[bootstrap-flat-entry]` is emitted by
`bootstrap_lower_flat_hir_modules_to_mir_for_target` (`bootstrap_globals.spl:508`)
immediately before `bootstrap_lower_flat_hir_module_to_mir(entry_index, ..., true)`;
the prescan lines are that call's `prescan_block_for_struct_types` walk
(`module_lowering.spl:2053`), and `bootstrap_reject_fatal_mir_errors` is checked
after EVERY `lower_function` (`bootstrap_globals.spl:~445`) and `exit(1)`s on the
first hit. So:

- the fatal fires while lowering **`app.cli.bootstrap_main` (flat row 0, 34
  functions)** — the first module MIR-lowered. Caveat: with `mir_trace_enabled()`
  off there is no per-module stderr marker, so the 140 prescan lines alone could
  in principle span modules; the stdout evidence below closes that gap;
- **there was ONE raise, not two.** This record's header says the error "appears
  exactly twice" (lines 15915 and 16122); line 15915 is inside the
  `PRESERVED DIAGNOSTICS` extract of the same stream whose raw tail follows, and
  16122 is the same `eprint` in that tail. Every fatal in the stream would be in
  the preserved extract; only one is;
- **probable victim: `bootstrap_native_build_ffi_progress`
  (`src/app/cli/bootstrap_main.spl:202-207`)**, or
  `lower_runtime_module_initializers_named`, which is checked at the same point.
  The nested `native-build-stderr-33044.log` (481,337 bytes, timestamps identical
  to block 1 to the millisecond, so a second capture of the same process, whose
  parent reported a clean `exited with code 1`) ends with
  `real-lower:done bootstrap_native_build_ffi_progress` — the exact point where
  `bootstrap_reject_fatal_mir_errors` runs after `lower_function` returns. It is
  the first entry function lowered (`lower_function:start` right after
  `aot:lower_to_mir:start`). Confirm with a run that captures stdout and stderr
  to separate files. That 6-line function's `lower_type` inputs are a small set:
  `state: text`, `-> unit`, the `path` Let type, the `if` condition, and the
  return types of the two cross-module calls `env_get`/`file_append` — the last
  two are the only inputs whose HirType originates in ANOTHER module's HIR
  (`bootstrap_fn_ret_hir_type_lookup`, `switch_operators_calls.spl:1378/1421`,
  fed by `_bootstrap_fn_ret_hir_types` registered in `bootstrap_globals.spl:383`
  from every module's `func.return_type`);
- the per-call `[mir-lower-type-probe]` (`function_lowering.spl:954`, gate
  `SIMPLE_MIRB_TRACE`, present at `5418d2075bb`) binds `fn=` to the SAME
  constant scope tail, so it cannot name the function either; it does give the
  failing call's `seq=` index within the run;
- the `scope-tail:` label is the LAST element of `_bootstrap_function_value_names`,
  a program-wide list assigned whole (`bootstrap_globals.spl:402`); it names the
  last function of the last module (`pipeline_fn`) for every raise in every
  module. The "victim function" in this record's title and in the 09-02 table
  (`compile_specialized_template{,_default,_release}` moving between runs) is that
  constant changing as pipeline_fn.spl was edited — it never localised anything.
  `pipeline_fn.spl:123-144` is NOT the victim; do not edit it.
- `[mir-lower] lower_function:start <name>` is `print` (stdout, buffered) while
  the fatal is `eprint`; the merged log therefore cannot name the function. A
  run with stdout and stderr captured to SEPARATE files (or with
  `bootstrap_reject_fatal_mir_errors` also printing `hir_fn.name`) names it.

### 2. "The object is NOT malformed" (09-03) is vacuous

`rt_heap_ref_wellformed` is a tag-and-address check only
(`src/runtime/runtime_native.c:8100-8103`: heap tag set and address >= 4096).
It says nothing about liveness. `kind == 0` with a span that is non-nil,
non-zero and undereferenceable is exactly what a freed `rt_alloc` block that has
since been REUSED for a different struct looks like (word 0 = that struct's
first field, word 1 = its second). Reads corrupt only in function bodies, counts
varying with heap state, and every reader-side fix inert are all consistent
with a use-after-free, and the 08-31 record's two-sided probe already showed
the graph intact when lowering begins.

### 3. What can free an HirType in the stage2 binary

Freeing paths in this binary: the per-file transient heap scope, `rt_free`
(explicit; only `lld_sffi.spl` calls it), sampled mem-guard slots, and
`rt_realloc`. A grep of the Rust seed for the `"rt_free"` string finds only
declaration/alias sites (`runtime_sffi.rs`, `calls.rs`, `elf_utils.rs`); its
drop/release emission logic was NOT audited. With that caveat, the transient
scope is the most plausible freer of HIR nodes:

- `driver_hir_pipeline_lowering.spl:65-99`: per source file,
  `rt_transient_array_scope_begin` -> parse + `lower_parser_module_unstub` ->
  `pause` -> `rt_transient_heap_promote(hir_module)`, diagnostics,
  `bootstrap_hir_modules_promote_last` (flat row arrays, lowering_helpers.spl:197-223),
  `driver_promote_frontend_registry_owners` (aspect/effect/rt_criticality/layer_eq)
  -> `rt_transient_array_scope_end` -> `rt_core_reclaim_transient_immortal` +
  `rt_core_reclaim_transient_raw` (`runtime_native.c:1384-1393, 1561-1580`) free
  every in-scope object the promote walk did not reach.
- Walker (`runtime_native.c:2057-2180`): descends arrays (except BYTES/U64_PACKED),
  dicts, enum payloads, closure captures, and RAW blocks by conservative 8-byte
  word scan — but ONLY raw blocks present in the raw table, which
  `rt_core_transient_raw_clear()` wipes at every scope end. Consequence: **every
  struct allocated before the current scope is a leaf**; a transient object
  reachable only through such a struct is freed. `HirModule.symbols` is the
  shared, run-lifetime `SymbolTable` (`module_build.spl:573,723`), so nothing
  under `hir_module.symbols` is promoted via the module root — its `HirSymbol`s
  survive only because the flat row array holds the same objects.
- `begin_module` (`context_helpers.spl:44-99`) runs BEFORE the scope opens and
  resets every HirType-holding `HirLowering` dict (`struct_field_types_by_name`,
  `local_tuple_types`, `fn_tuple_returns`, ...), so cross-module staleness via
  the dicts listed there is ruled out. Audit completed 2026-09-06 11:35:
  `SymbolTable.reset_module` (`hir_types.spl:311-333`) re-creates all 14 fields
  of the class (`hir_types.spl:254-282`), and every `HirLowering` field past
  `types.spl:160` holds only ints/text/bools. No retained `HirLowering` /
  `SymbolTable` field carries an HirType across modules. The escape is
  therefore an in-scope node referenced from a promoted node THROUGH a pre-scope
  struct (walker leaf), or an unpromoted parallel owner outside `HirLowering`.
  `module_surface_promote` promotes surface fields by name
  (`module_surface_registry.spl:305-333`); unlisted `ModuleSurface` fields
  (`friends`, `internal_exports`, `import_target_*`, `import_resolution_traces`,
  `export_route_*`, `composite_index`, the `Dict<text,...>` mirrors,
  `export_origins`, `declaration_authority_index`) are freed at parse-scope end
  unless promoted elsewhere — unexamined, listed for the next reader.

The specific escaping object was NOT identified.

### 4. `2da5aa6e` (rt_* dual-lane) — cheap evidence it is unrelated

`git show --stat 2da5aa6e`: 62 insertions across `value_ops.rs`, `runtime.c`,
`runtime.h`, `runtime_native.c`; its diff contains zero occurrences of
`transient|promote|reclaim|rt_alloc|rt_struct_alloc|immortal`. It cannot have
changed any allocation or reclaim path above. Not a proof of independence
(that still needs a Stage-3 run at `2da5aa6e^`), but the bug predates it
(09-03) and it touches none of the mechanism.

### 5. Reproduction attempts

- The receiver-gate arm-2 fixture
  (`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl`,
  2 modules) reproduced this class with an older stage2 (08-31 record:
  4/8/20 `disc=-1` per run; `module_build.spl:~95` comment). At 09-05 admission
  it PASSED once (`stage2-receiver.env status=pass`). A frozen-stage2 N=3 rerun
  with `SIMPLE_MIR_TAG_PROBE=1` was started on 09-06; the process ran ~12 min
  under heavy contention without emitting output and was lost with the
  worktree. **No verdict** — not a negative.
- No smaller entry than `bootstrap_main.spl` was found that provably reaches
  the fatal; the corruption is heap-state dependent, so a fixture must be
  judged over N>=10 runs with non-vacuity (`lines`, `hir n/n`) checked.

### 6. Next instrumented run

Prerequisite: the admitted stage2 binary was lost with the frozen worktree; a
`--stop-after-stage2` rebuild (~1 h) is needed first.

1. No source edit: that stage2, Stage-3 argv, `--threads 1`,
   `SIMPLE_COMPILER_TRACE=1`, `SIMPLE_MIRB_TRACE=1` (per-call probe),
   `SIMPLE_MIR_TAG_PROBE=1`, cache-dir outside the tree, **stdout and stderr to
   separate files**. The last `lower_function:start` in stdout names the entry
   function and the probe's `seq=` names the failing `lower_type` call; ~70 min
   to phase 5, exits at the fatal before writing objects.
2. Then (needs a stage2 rebuild): under an env flag make
   `rt_core_reclaim_transient_raw` POISON owned blocks (fill, do not free) so a
   dangling read yields a recognisable pattern instead of a reused block, and
   record `(ptr, scope_id)` of every poisoned block; a ZeroKind raise then
   reports which file's scope freed the object. That is the measurement that
   names the producer.

### Not verified

Everything in sections 1-3 is read from the 09-05 logs and source at
`5418d2075bb`; no run was completed on 09-06. No fix was attempted.

### 7. 2026-09-06 stage2 rebuild attempt — blocked on disk, not started

`git worktree add --detach <scratch>/zk-wt 5418d2075bb` then
`bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2
--mode=dynload` in it, with a 30 s watchdog set to abort below 4 GiB. The script
refused before doing any work: `insufficient disk space to start a bootstrap:
9 GB free` — its floor is `SIMPLE_BOOTSTRAP_MIN_FREE_GB` (default 10,
`bootstrap-from-scratch.sh:674`). Free space fell 16 -> 6 GiB during the
attempt from concurrent peer activity (the checkout itself is 2.7 GiB); the
worktree was removed again. No bootstrap ran; nothing was built. The Stage-3
diagnostic run (§6) therefore has not happened.

Second attempt, 11:28 local: 37 GiB free, no peer bootstrap; worktree
`<scratch>/zk-wt` at `5418d2075bb` recreated, watchdog re-armed, the same
`--stop-after-stage2` command started (log: `<scratch>/zk-stage2-build.log`).
Outcome recorded below when known.
