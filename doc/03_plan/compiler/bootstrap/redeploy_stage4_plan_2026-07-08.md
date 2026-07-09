# Stage4 Self-Host Redeploy (#79) — Detailed Plan (2026-07-08)

Status: **blocked, precisely root-caused.** Deployed `bin/simple` (Jul 3) still
works as a tool; producing a *new* self-hosted stage4 binary from current source
does not yet succeed. This plan records the two emit paths, the exact current
wall, and the concrete next steps with file:line anchors.

## Goal

`bin/simple build bootstrap` (or the equivalent stage2 self-compile) produces a
working self-hosted `simple` binary from current `src/`, gateable and
redeployable to `bin/release/<triple>/simple`.

## The two emit paths

1. **cranelift/llc `SIMPLE_BOOTSTRAP=1` (the bootstrap path).** Driver:
   `src/compiler/80.driver/driver_bootstrap.spl`
   (`bootstrap_emit_real_llvm_object`, :226). Uses the pure-Simple `MirToLlvm`
   text backend + `llc`. This is the realistic route to a redeployable stage4.
2. **llvm-lib AOT (reference-correct sibling).** `src/compiler/70.backend/
   backend/llvm_lib_*`. Now compiles *trivial* programs to running binaries
   (commits `7984ab3`, `4866213`) but is long-horizon for #79 — and the deployed
   `bin/simple` has **no LLVM linked**, so it can't even run this backend.

## CURRENT WALL (path 1, cranelift/llc `SIMPLE_BOOTSTRAP` string-literal drop) — STALE, see path-2 update below

**This section describes path 1** (`SIMPLE_BOOTSTRAP=1` stage2 self-compile via the pure-Simple
`MirToLlvm` text backend + `llc`, `driver_bootstrap.spl`). **`bin/simple build bootstrap`'s actual
Stage 1 currently runs path 2** (the `llvm-lib` AOT / LLVM-C-API path below — confirmed by the
`[llvm-lib]`-prefixed errors and `LLVMBuildICmp`/`LLVMSetDataLayout` FFI crash backtraces in
`bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`). Path-1's string-drop investigation
below is preserved for whoever resumes that path, but it is **not** the wall blocking
`bin/simple build bootstrap` today — see "CURRENT WALL (path 2)" below for that.

**Evidence.** The `SIMPLE_BOOTSTRAP=1` stage2 self-compile of
`src/app/cli/bootstrap_main.spl` returns rc=0 and emits a **21KB inert stub**:
run it and `--version`/no-arg print nothing. Dumped IR (`/tmp/simple_llvm_*.ll`)
shows:
- `fn bootstrap_version()->text: "1.0.0-beta"` → `ret ptr null` (string→null on
  the return path).
- `__simple_main` has a real body, but every `rt_println` arg is a `[1 x i8]`
  (empty `""`) global; short *compared* literals (`--version` `[10 x i8]`,
  `--help` `[7 x i8]`) survive with content.
- `fn native_build_help()->i64: 0` → `ret i64 0` is **correct** (not a bug).

**The codegen emitter is innocent.** Path: `driver_bootstrap.spl:232` creates a
`MirToLlvm` translator → Str emit at
`70.backend/backend/_MirToLlvm/core_codegen.spl:553` → `add_string_global`
(`asm_constraints_helpers.spl:151`), whose array size is
`escaped_string_byte_len(v)+1 = value.len()+1`
(`mir_to_llvm_helpers.spl:135`). `[1 x i8]` ⟹ `value.len()==0` **at emission**,
so the `Const(Str)` is **already empty** when it arrives.

**So the drop is upstream.** The MIR functions are pre-built and stored in
`_bootstrap_mir_functions` (`50.mir/_MirLowering/bootstrap_globals.spl:41`,
added at `:145`) from the standard HIR→MIR lowering. String literals become
`MirConstValue.Str(value)` at `50.mir/mir_data.spl:486` (`emit_const_str`,
:482). Either HIR→MIR builds an empty `Const(Str)`, or the **seed interpreter
zeroes string literals** while running the (interpreted) compiler during the
self-compile — the #66 "string drops to empty in run path" class, residual on
the `SIMPLE_BOOTSTRAP` compile path (#66 was closed for the concat case).

## CURRENT WALL (path 2, llvm-lib AOT / LLVM-C-API) — this is what `bin/simple build bootstrap` hits today

Path 2 (`src/compiler/70.backend/backend/llvm_lib_*`, native-build LLVM-IR generation run
**interpreted** by the deployed `bin/simple`) has been the actual Stage-1 wall all session
(2026-07-09). It advanced twice (139→134→139 across #130/#133, real exit-code/backtrace changes),
then **stalled at exit 139** for the rest of this session (steps 3-5 below) — a real, separate bug was
fixed in step 4, but it did not move the fatal 139:
1. **Pre-#130:** ICmp SIGSEGV (139) — bad `llvm::Value*` operand from wiped call/method args.
2. **#130** `bfd98b03 fix(hir): stop wiping call/method args under SIMPLE_BOOTSTRAP` — fixed that,
   moved the wall to a DataLayout abort (134, corrupted `text.ptr()` param to `LLVMSetDataLayout`).
3. **#133** `d16a8883 fix(bootstrap): lower function params under SIMPLE_BOOTSTRAP` — fixed the
   DataLayout wall. On the resulting tree, Stage 1 still fails at exit 139 (SIGSEGV), and the log
   *also* shows a separate, non-fatal event: an **unresolved-function-call** eprint from
   `translate_call` (`llvm_lib_translate_expr.spl:478-480`) for callee `Const(Str("rt_cli_get_args"))`
   → `func_ref == 0` (not in `func_map`, not pre-declared in the LLVM module) → that one call is
   dropped, producing broken IR **for that call site only**.
4. **2026-07-09 fix (this session, uncommitted, left for review):** `rt_cli_get_args` is a real
   runtime extern (`src/runtime/runtime_native.c:1198`, used by `src/app/sj/main.spl` /
   `sj_daemon/main.spl`) that `declare_runtime_functions()` in `llvm_lib_translate.spl` never
   pre-declared (only sibling `rt_get_args` was). Added one line mirroring the existing declaration:
   `declare_fn(mod_, "rt_cli_get_args", llvm_function_type(ptr_ty, [], false))` right after
   `rt_get_args` (`llvm_lib_translate.spl:237`). Verified: re-run shows **zero**
   `[llvm-lib] ERROR: unresolved function call` occurrences (was 1) — that specific broken-IR drop is
   genuinely fixed. **This is a real, worthwhile, standalone fix — keep/land it — but see (5): it does
   NOT unblock Stage 1.**
5. **CORRECTED — the fatal wall did NOT move; it was mis-attributed to (3)'s dropped call.**
   Comparing macOS crash reports from the pre-fix run
   (`~/Library/Logs/DiagnosticReports/simple-2026-07-09-134458.ips`) and the post-fix run
   (`...-134732.ips`) shows **byte-identical** crashing-thread top-8 frames and identical
   `EXC_BAD_ACCESS`/`KERN_INVALID_ADDRESS at 0x0` in both — `llvm::ConstantFolder::FoldCmp` /
   `LLVMBuildICmp`, reached via `call_extern_function_with_values`. The SIGSEGV was **already** the
   fatal Stage-1 crash before step (4)'s fix; the `rt_cli_get_args` unresolved-callee eprint and the
   SIGSEGV are two independent, co-occurring events in the same Stage-1 compile, not cause→effect.
   **True current state: exit 139, `LLVMBuildICmp`/`ConstantFolder::FoldCmp` SIGSEGV, unchanged
   before and after this session's fix — this is the same crash class #130 (step 2) was believed to
   have fixed**, either a different uncovered `ICmp` call site, or an incomplete/order-sensitive fix.
   See `doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`'s "State
   after this run" section for the full comparison and backtrace. **This is the next thing to
   instrument/diagnose** (repeat this doc's Step-1 diagnostic-eprint method, but on the
   `LLVMBuildICmp` extern binding / `call_extern_function_with_values` opaque-`llvm::Value*`
   marshalling, per that bug doc's original "Fix direction" section).

**A second, separate, NOT-yet-hit latent bug found by code-reading while diagnosing (4):**
`translate_call`'s inline `Copy(local)`/`Move(local)` match arms (used to resolve an *indirect*-call
callee) pass the raw `LocalId` struct to `get_value(value_map, local)` instead of unwrapping `local.id`
first — the exact bug class `7984ab3ad7` (2026-07-08) fixed in the sibling `translate_operand`
function and the `SetField` inline match in the *same file*, but missed this occurrence. Any indirect
call (callee = `Copy`/`Move` operand, not a `Const(Str(name))`) will always resolve `func_ref == 0` and
get silently dropped. One-line-per-arm fix, matching the established `7984ab3ad7` pattern exactly:
`get_value(value_map, local.id)`. Not applied (not the wall actually hit; flagged as active #79/#133
territory per this plan's own "do not solo-patch structural value_map threading" guidance) — next
person touching `translate_call` should land it alongside whatever they're already doing there.

## Why it's been hard (structural, not just difficulty)

- **Duplicate module files**: numbered (`50.mir`, `70.backend`) vs non-numbered
  (`mir`, `backend`) directories both exist. The seed resolves an import to one
  copy; instrumentation on the other copy silently never fires (both `ADDSTR`
  in `add_string_global` and `EMITSTR` in `emit_const_str` missed). Same #41
  duplicate-definition class that the llvm-lib FFI fixes had to patch ×4.
- **~400s per probe** (the stage2 self-compile builds a large closure).
- **Parallel-sync clobber**: a concurrent full-WC sync reverts edits within
  seconds, so instrument via **atomic cp-into-main-repo + immediate run** (the
  seed reads stdlib from the main repo relative to the seed binary, NOT CWD —
  a detached worktree is NOT read by native-build).
- **Session kill-monitor** SIGKILLs `simple run`/exec-mode processes (rc=9);
  reproduce via `native-build`, not `run`.

## Next steps (in order)

**Path 2 (the live wall — do this first, it's what `bin/simple build bootstrap` actually runs):**
1. **Land the uncommitted `rt_cli_get_args` declare_fn fix** (this session,
   `llvm_lib_translate.spl:238`, additive one-liner) — review + commit. Real, verified fix for a
   broken-IR drop, but note: it does NOT by itself unblock Stage 1 (see (2)).
2. **UPDATED 2026-07-09 (post-9d11e852 diagnosis pass): the wall is nondeterministic, not a stable
   exit-139.** A fresh `bin/simple build bootstrap` against `9d11e852` (instrumenting `translate_binop`
   to log the source MIR operand of any NULL ICmp lhs/rhs) did **not** reproduce exit 139 — it aborted
   at exit **134** again (`LLVMSetDataLayout`/`DataLayout::DataLayout` → "ABI alignment must be a 16-bit
   integer"), before `translate_binop` was ever reached (0 diagnostic hits). Cross-referencing all of
   today's crash reports (10:35 SIGABRT/134, 13:36/13:44/13:47 SIGSEGV/139, 14:08 SIGABRT/134) shows the
   crash **site** flips between the `LLVMSetDataLayout` text-arg wall and the `LLVMBuildICmp`
   `Value*`-operand wall across runs of an otherwise-unchanged tree — inconsistent with a fixed missing
   `value_map` key (which would fail identically every run) and consistent with a heap/timing-dependent
   corruption inside the interpreter's shared `call_extern_function_with_values` FFI-marshalling path
   (present in every one of these backtraces, regardless of which downstream LLVM C API is hit). Full
   evidence + verdict: `bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`'s
   "post-9d11e852 diagnosis session" update.
   **Revised next step:** do NOT keep repeating the positional Simple-side `eprint`-guard method — it
   only fires if that exact call site is reached before the nondeterministic corruption happens to
   manifest elsewhere first (as this run demonstrates). Instead diagnose
   `call_extern_function_with_values` itself (`simple_compiler::interpreter::interpreter_extern`, Rust)
   for a dangling/reused `text.ptr()` buffer or a stale/uninitialized extern-argument marshalling slot —
   see that bug-doc section's "Concrete next fix direction" for the specific experiment (compare the
   argument address/bytes on the interpreter side immediately before an extern call vs. what the native
   callee receives).
3. **UPDATED 2026-07-10 (Codex/Spark bootstrap-first pass): one run did reach `translate_binop` and
   proved a genuine missing `value_map` operand for that run.** The temporary probe logged:
   `dest=4 lhs=<nonzero> rhs=0 left=Copy#2 present=true right=Copy#3 present=false`, then Stage 1
   failed at exit 139. Artifact:
   `/private/tmp/claude-501/-Users-ormastes-simple/7597a415-f0b0-4c3f-822d-107292b34bec/scratchpad/codex_null_binop_bootstrap.log`.
   This does not invalidate the nondeterministic FFI concern in (2); it means the current action needs
   two coordinated checks:
   - add a MIR/value-map validator before LLVM translation that reports function name, block, instruction
     index, and any `Copy`/`Move` local with no prior def or `Arg` local; this should identify whether
     `Copy#3` came from the `function_lowering.spl:124` phantom-parameter fallback or from an
     initializer-less local path such as `mir_lowering_stmts.spl:154-159`;
   - continue tracing `call_extern_function_with_values` argument bytes/addresses because unchanged-tree
     runs still flip between `LLVMBuildICmp` and `LLVMSetDataLayout`.
   The temporary compiler diagnostic was reverted; only docs remain dirty.
4. **UPDATED 2026-07-10 (Codex bootstrap continuation): applied three targeted fixes and stopped at the
   session verify/fix cap.**
   - `translate_call`'s latent `Copy`/`Move` `.id` unwrap fix is now applied.
   - `llvm_set_data_layout` now NUL-terminates the layout string in all three active LLVM FFI wrappers;
     the next bootstrap moved past the prior `LLVMSetDataLayout` abort.
   - A targeted probe then identified the next ICmp wall as
     `bootstrap_output_from_args block=0 inst=0`, missing `Copy#3` for the `i >= args.len()` comparison.
     `bootstrap_builtin_signature` was updated so argument-taking bootstrap helpers no longer receive a
     zero-parameter HIR function type (`bootstrap_output_from_args([text], i64)`, `run_native_build_bootstrap([text])`,
     `eprint(text)`).
   The temporary diagnostic was removed. Backend focused checks pass; `expressions.spl` still fails the
   current file-level checker on pre-existing enum-payload parser errors away from the edited signature
   block. Do the next bootstrap in a fresh scoped session because this lane already consumed three
   bootstrap verify/fix cycles.
5. If the next Stage 1 run still fails, start from the latest wall, not from DataLayout: inspect the
   emitted HIR/MIR for `bootstrap_output_from_args` and confirm params/arg locals are present before
   llvm-lib translation.
6. Once Stage 1 (path 2) passes, re-gate the full `bin/simple build bootstrap` 3-stage before any
   redeploy to `bin/release`.

**Path 1 (cranelift/llc `SIMPLE_BOOTSTRAP` string-literal drop — stale/deprioritized, not today's
wall, preserved for whoever resumes it):**
1. **[#128] Pin the drop point.** Instrument the string-literal lowering in
   **both** copies simultaneously — `50.mir/mir_data.spl:486` `emit_const_str`
   AND `mir/mir_data.spl` (+ the HIR→MIR literal path) — with an `eprint` of
   `value`/`value.len()`, via atomic cp + one `SIMPLE_BOOTSTRAP=1 native-build`
   run. Grep the output for `1.0.0-beta`:
   - arrives as `""` → HIR/MIR-gen or seed string-literal handling bug.
   - arrives intact → the drop is between MIR store and emit (re-check the
     `_bootstrap_mir_functions` round-trip / seed value handling).
2. **Fix the single site** found in (1). If MIR-gen/pure-Simple → fix in `.spl`
   and re-run the stage2 probe; strings should carry content and the driver
   should print its version/help.
3. **Re-gate**: once the stage2 driver is non-inert, run the full
   `bin/simple build bootstrap` 3-stage and the extended smoke matrix before any
   redeploy to `bin/release`.

## Landed this session (verified, on origin/main)

- `7984ab3` — llvm-lib value_map return-threading + operand `LocalId.id` key →
  emitted IR passes LLVM verification (was invalid).
- `4866213` — llvm-lib trivial-binary milestone: create_target_machine
  Triple/CPU/Features NUL-terminate + cpu `x86-64-v1`→`x86-64` + name
  NUL-terminate (all 4 FFI copies). `42` and `40+2` → running ELF64 returning 42.
- `bfd98b03` (#130) — stop wiping call/method args under SIMPLE_BOOTSTRAP; not blocking now. It moved
  the visible symptom from one ICmp crash instance to the DataLayout abort, but later evidence shows
  the broader Stage-1 wall was not fully resolved.
- `d16a8883` (#133) — lower function params under SIMPLE_BOOTSTRAP; not blocking now. It moved the
  visible symptom back from DataLayout abort to exit 139, but later evidence still shows both the
  DataLayout and ICmp walls can appear across reruns.

## Uncommitted this session (2026-07-09, left for review — see bug doc for full detail)

- **Applied:** `llvm_lib_translate.spl:238` — `declare_fn(mod_, "rt_cli_get_args", ...)`, additive.
  Verified fix: cleared the `translate_call` unresolved-callee eprint for the `Const(Str("rt_cli_get_args"))`
  case (1 → 0 occurrences). **Does not affect the exit-139 SIGSEGV** — crash-report comparison
  (pre-fix `simple-2026-07-09-134458.ips` vs post-fix `...-134732.ips`) shows byte-identical crash
  signatures, proving these were always two independent issues.
- **Not applied (reported for #79):** `translate_call`'s `Copy`/`Move` match arms need
  `local` → `local.id` (same class as `7984ab3ad7`, latent, not yet hit by a real run).
- **Not diagnosed (the actual fatal wall, present throughout this session, before and after the fix
  above):** `LLVMBuildICmp`/`ConstantFolder::FoldCmp` SIGSEGV (exit 139), crash reports
  `simple-2026-07-09-134458.ips` (pre-fix) and `simple-2026-07-09-134732.ips` (post-fix).

## Out of scope for #79 (recorded, not on the critical path)

- llvm-lib runtime-builtin decls (`#129`) — **UPDATE 2026-07-09: no longer purely out-of-scope.**
  `bin/simple build bootstrap`'s Stage 1 now runs the llvm-lib path (path 2) as its live wall, and
  `#129`'s exact class of gap (a `declare_runtime_functions()` hardcoded list missing a real extern,
  here `rt_cli_get_args`) was this session's actual blocker. The broader `#129` question — should
  `declare_runtime_functions()` stay a hand-maintained list, or should it derive declarations from the
  `extern fn` decls actually present in the MIR module (avoiding future one-off gaps) — is still a
  reasonable structural item to scope separately; the immediate instance was fixed additively.
- Interpreter completeness (`#99`) and class-in-array mutation (`#112`) —
  interpreter-lane items; `#112` repro blocked by the exec-mode kill-monitor.
