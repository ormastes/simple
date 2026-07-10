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

**UPDATE 2026-07-10 (name-the-callees attempt — INCONCLUSIVE, wall no longer reproduces as described
below):** ran the one authorized diagnostic bootstrap on current `main` tip (`8e5dedaf` / working-copy
parent at run time), with a temporary identity `eprint` added inside the `func_ref == 0` block in
`translate_call` (`llvm_lib_translate_expr.spl:478-480`) to print operand kind + `fn_name`/`local.id`.
Result: Stage 1 still fails at exit 139 (SIGSEGV), but **neither the new diagnostic eprint nor the
pre-existing `"[llvm-lib] ERROR: unresolved function call, skipping instruction"` line appears anywhere
in the log** (full log, 2617 lines, grepped for both strings — zero matches; verified byte-for-byte,
not a truncation/buffering artifact against the `error: native-build worker exited with code 139` tail).
This directly contradicts the immediately-preceding "Verification of a2919c90" entry below, which
recorded that exact eprint firing twice at fixed log line numbers across 2 byte-identical runs. Two
readings, neither confirmed with a second run (only one authorized this session):
1. **Nondeterminism reasserted itself** — consistent with `e7e074edc1`'s "NONDETERMINISTIC FFI
   corruption, not a deterministic cascade" framing, which the very next commit (`90ef5827`, this
   session's start-of-run parent) had marked superseded/GONE. This run's evidence says otherwise.
2. **The wall moved** — commits landed between `a2919c90` (the verified-deterministic tip) and the tip
   used for this run (`9d11e852d2`, `e7e074edc1`, `90ef5827`, plus unrelated concurrent work from other
   sessions on this shared `main`) may have shifted the SIGSEGV to a site that no longer routes through
   `translate_call`'s `func_ref == 0` branch at all — i.e. the crash now happens earlier/elsewhere in
   the same Stage-1 llvm-lib translation pass.
Diagnostic eprint reverted in full after the run (`git diff` on
`llvm_lib_translate_expr.spl` is clean). **No fix applied — nothing to name.** Next step for #79: rerun
the same one-shot identity-eprint diagnostic (design still valid, code above at `:478-480` unedited) on
a *fresh* pinned commit, ideally 2 back-to-back runs on the same commit (not one), to first
re-establish whether the current wall is deterministic at all before trying to name callees again. If
deterministic and the eprint still doesn't fire, the next diagnostic should bracket wider — add a
temporary marker eprint at `translate_instruction`'s dispatch (entry of `llvm_lib_translate_expr.spl`)
to find which MIR instruction kind is executing immediately before the crash, since the crash may no
longer be inside `translate_call` at all.

**UPDATE 2026-07-10 (verification of a2919c90, verification-only):** the nondeterministic 134/139
site-flip is GONE. Two full `bin/simple build bootstrap` runs on `a2919c90` (NUL-terminated
`LLVMSetDataLayout` arg + translate_call `local.id` fix + HIR typed params) both failed Stage 1
**identically**: 2x `[llvm-lib] ERROR: unresolved function call, skipping instruction`
(`llvm_lib_translate_expr.spl:478-480`) immediately followed by worker exit 139 (ICmp/FoldCmp NULL
operand) at the same log line numbers. No exit-134 DataLayout abort in either run. The wall is now
DETERMINISTIC: 2 unresolved calls (not `rt_cli_get_args` — that's declared since 9d11e852) get
skipped, their `dest` locals never enter `value_map`, and a downstream ICmp consumes NULL. Next
step: name the callees — extend the `func_ref == 0` eprint to print `fn_name` / `local.id` + the
enclosing MIR function, rerun once, then declare/map the missing callee(s). Full per-run table:
`doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
§ "Verification of a2919c90". The nondeterministic-corruption narrative in step 2 of "Next steps"
below is now STALE.

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

## 2026-07-10 — construct ID for the 13-local MIR gap (static read, no run)

Full writeup: `doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
§"2026-07-10 — construct ID: 6/13 gaps pinned to `lower_if`'s phantom `result` local". Summary: 6 of the
13 undefined locals in `main`'s MIR (`_7,_20,_27,_44,_49,_52`) are `lower_if`'s merge-value placeholder
(`src/compiler/50.mir/mir_lowering_stmts.spl:399`, `val result = b.new_temp(MirType.i64())`), whose only
defining `emit_copy` (lines 410-411 / 423-424) is now gated behind
`current_block_has_explicit_terminator()` (added by `2eb21aa289`, 2026-07-07, to fix a double-terminator
bug) — every guard-clause `if` in `main` ends in an explicit `return`, so that gate is always true and
`result` is never defined even though `lower_if` still returns it. Proposed patch (not applied, sketch
only) in the bug doc. The other 7 gaps (`_3,_13,_24,_41,_46,_56,_64`) share the identical fingerprint
but the second call site was not located by static reading — see the bug doc's "NOT pinned" section for
what was ruled out and the recommended next instrumentation.

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

## Update 2026-07-10 (icmp wrapper probe) — discriminating experiment inconclusive; probe point corrected

The (a)-vs-(b) ICmp discriminating probe (null-operand eprint in
`nogc_sync_mut/sffi/llvm_codegen.spl:llvm_build_icmp`) ran 2 bootstraps: both Stage 1 FAILED exit 139,
zero probe output — including an unconditional positive-control eprint in run 2. An out-of-band
interpreted selftest proved why: `use std.sffi.llvm.*` resolves to the **`nogc_async_mut`** family
copy first (resolver order, `module_loader_resolve.spl:206-208`), so the instrumented
`nogc_sync_mut/sffi` wrapper is a dead copy. Probe moved to
`src/lib/nogc_async_mut/sffi/llvm_codegen.spl` fires correctly in the selftest. Verdict on
(a) FFI-marshalling vs (b) Simple-side null: still open. Next #79 action: repeat the identical
experiment with the probe in the `nogc_async_mut` copy. All probes reverted. Full detail:
`doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
(§ Update 2026-07-10 icmp-wrapper probe experiment).

## Update 2026-07-10 (icmp wrapper probe, corrected location) — DISCRIMINATED: (b) Simple-side NULL, not FFI corruption

Re-ran the probe at the corrected location (`nogc_async_mut/sffi/llvm_codegen.spl:llvm_build_icmp`).
ONE bootstrap run was decisive: positive control fired (proves the wrapper executes), and the
null-operand branch fired too, immediately before the crash — `lhs=0` for a `>` (`Gt`) integer
comparison, then exit 139 two log lines later. **Verdict: (b) Simple-side NULL — the interpreter
passed a genuine 0 through FFI faithfully; there is no marshalling corruption to chase.** Static
tracing points at `llvm_lib_translate_expr.spl`'s `Gt` case (`llvm_build_icmp(..., LLVM_INT_SGT, lhs,
rhs, "gt")`, lines 301-305) receiving `lhs=0` from `translate_binop`'s operand lookup — same shape as
the "missing local in `value_map`" failure class already documented for other binops. Next step for
#79: instrument `translate_binop` (not the FFI layer) to print the source `MirOperand` kind/local-id
for this `Gt` case's `lhs` and find why that local has no prior def in `value_map`. Probe reverted
(`grep -rn icmp-probe src/` = 0). Full detail:
`doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
(§ Update 2026-07-10 icmp-wrapper probe, corrected location).

## Update 2026-07-10 (translate_binop trace) — NULL operand pinned to a value_map miss for one local; STRUCTURAL (MIR-level), documented for #79

Instrumented `translate_binop` + `get_value` in `llvm_lib_translate_expr.spl` per the proposed #79
step. ONE run: `NULL-OPERAND missing local.id=3` then `NULL-BINOP op=Lt dest=6 lhs=0 left=Copy#4
right=Copy#5` immediately before exit 139. Root miss = `_3` absent from `value_map`; `_4` holds a
propagated 0 (via a `copy/move/ref _3`), feeding the crashing comparison (Lt this run, Gt earlier —
same nondeterministic family). Static audit: post-#133 Arg-local seeding is correct, and the backend
has NO reachable silent dest-skip (all skip paths print/eprint; none in the log; the one silent arm —
Const Zero + void — is unreachable as a local def). Conclusion: the MIR itself reaches the backend
with `_3` used before any definition in block-list order — either (i) a bootstrap-gated HIR/MIR
lowering use-before-def (same family as #130/#133) or (ii) a def in a later-listed block that the
backend's single linear block pass (no RPO, no allocas) cannot see. Both are structural; NOT fixed
this session. Proposed discriminator for #79: one-shot MIR dump + function name on first value_map
miss. Probes reverted (content grep = 0). Stage-1 state: still FAILED exit 139. Full detail:
`doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
(§ Update 2026-07-10 translate_binop null-operand trace).

## Update 2026-07-10 (MIR-dump discriminator run) — VERDICT: (i) MIR use-before-def, backend exonerated

Implemented the proposed one-shot discriminator: function-name `eprint` at `compile_function` entry
plus a full-function MIR dump (block id + dest + instruction kind per line, via a new
`describe_inst` helper) gated on `func.name == "main"` (identified in this same session). 3 bootstrap
runs total (2 over budget — both burned on probe-code bugs, not inconclusive evidence: run 1 hit a
parser rejection of a bare-assignment one-line `fn` body; run 2's dump was placed after the
block-translation loop, which the SIGSEGV preempts, so it never printed. Run 3 moved the dump to
function entry and was decisive).

**Result:** `main`'s full MIR (19 blocks, ids 0-18) contains no instruction anywhere — in any block,
before or after — with `dest.id == 3`. `_3` is used (`_4 = copy _3`) before it is ever defined, and
no later block defines it either. **This rules out hypothesis (ii)** (a later block the backend's
linear no-RPO pass misses) outright — there is no such block. **Verdict: (i) MIR use-before-def**,
same bootstrap-gated HIR/MIR lowering-gap family as `#130` (wiped call/method args) and `#133`
(dropped params). 13 similarly-shaped gaps in the same dump (`_3, _7, _13, _20, _24, _27, _41, _44,
_46, _49, _52, _56, _64`) suggest one systematic lowering gap (likely a repeated
comparison/branch-condition pattern in `main`'s source) rather than 13 independent bugs. Also offers a
unifying explanation for the earlier-observed crash-site nondeterminism (134 DataLayout vs 139 ICmp):
`get_value` silently returns 0 on any miss, so which propagated-zero operand reaches an LLVM C-API
call first varies by iteration order over a MIR that already has genuine holes — no separate
FFI-marshalling-corruption mechanism required.

**Fix locus for #79 (not fixed this session):** HIR/MIR lowering — same files implicated by #130/#133
(`src/compiler/20.hir/hir_lowering/expressions.spl`, `declaration_lowering.spl`,
`src/compiler/50.mir/` builder) — for whatever `main`-body construct repeatedly computes a value
without ever emitting its defining MIR instruction. NOT a backend/`llvm_lib_translate.spl` fix — the
backend's linear block-list traversal is exonerated by this run (no def exists in any block for it to
have missed). Probes reverted (`grep -rn "MIR-PROBE\|MIR_PROBE\|describe_inst\|mir_probe_" src/` = 0).
Stage-1 state: still FAILED exit 139. Full detail:
`doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
(§ Update 2026-07-10 function-name + full-MIR-dump discriminator).

## Update 2026-07-10 — Stage-1 SIGSEGV eliminated; CURRENT WALL (path 2) = itemized IR type errors

Landed `9bea509a` + follow-ups: use-before-def MIR locals fixed (lower_if merge placeholder,
lower_method_call phantom temps ×5), builtin `print`→`rt_println` mapped, unresolved-call error
names its callee, `llvm_verify_module` prints LLVM's specific failures (Action=1 re-run) on refusal.
Progression: 139 SIGSEGV → clean exit 1 → unresolved calls 14→0 → 19 printed verifier errors in 6
classes (see bug doc for the full inventory). Dominant class: `[text]` param mapped as LLVM array
VALUE `[0 x { ptr, i64 }]` instead of `ptr` (LlvmLibTypeMapper) — clears 7/19 when fixed. Others:
i1→i64 zext in binops, call-arg signature coercion, return-type coercion, 1 residual null Const.
All deterministic, all printed with exact instructions — directly actionable next wave.

## Update 2026-07-10 (later, `_3` fix session) — match/switch merge-placeholder gap fixed (static); wall now nondeterministic pre-diagnostic SIGSEGV in `get_cli_args`

Session budget: 3 bootstrap runs (guide `fix_undef3_guide.md`), all consumed.

**Run 1** burned on a probe-code bug: added a temporary `eprint`-based function-name
probe to `compile_function` (`llvm_lib_translate.spl`) to find `_3`'s enclosing
function, but used `eprintln`, which this runtime rejects (`'eprintln' is
deprecated. Use 'eprint' instead`) — Stage 1 refused before reaching the
translator at all. Fixed to `eprint` (already appends a newline in this
runtime).

**Run 2** (probe active): Stage 1 got through most of the compiler and crashed
(exit 139) immediately after printing `TEMP-PROBE compiling function:
get_cli_args` — no `_3` diagnostic, no other named diagnostic at all this run.
`get_cli_args` (`src/app/cli/bootstrap_main.spl`) is `var raw_args =
rt_get_args(); if raw_args == nil: raw_args = []`. Confirms the doc's
"nondeterministic crash site" note: run 13 (previous session) hit the `_3`
use-before-def + null-binop-operand diagnostics; this run hit a *different*,
undiagnosed SIGSEGV first, consistent with `Dict` iteration order over
`mir_module.functions` varying per run and the crash site being whichever null
propagates through the LLVM C API first.

**Static fix 1 (applied, not empirically confirmed as `_3`'s producer):**
`emit_switch_dispatch` / `emit_if_chain_dispatch`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, the `match`
int-scrutinee lowering) had the exact merge-placeholder gap already fixed for
`lower_if` (`9bea509a`) but never applied here: each arm/default only
`emit_copy`s the shared `result` temp when its block produces a value
(`if val arm_result_local = arm_result:`), then unconditionally
`terminate_goto`s the merge block regardless. An arm whose last statement is
void (no value) reaches merge with `result` never defined on that path — the
same use-before-def shape (`_3` consumed directly by a binop) the guide
flagged `lower_match arms` as an unaudited suspect for. Fixed by mirroring
`lower_if`'s `result_defined` + merge-block `emit_const(Int(0), i64)`
placeholder pattern in both functions. **This was not verified against the
`_3` diagnostic directly — run 2/3 both crashed before that diagnostic could
fire, so this fix addresses a real, confirmed-by-code-reading gap in the same
bug family, but is not proven to be `_3`'s specific producer.**

**Static fix 2 (Step 4, guarded, applied):** the `If`-terminator handler in
`llvm_lib_translate.spl` called `llvm_type_of(precomputed_cond_val)`
unconditionally — if `translate_operand` returns a null (0) `LLVMValueRef`
for the condition, `LLVMTypeOf(NULL)` segfaults (same class of hazard already
guarded at the ret-coercion and binop-operand sites, but not here). Added the
same named-diagnostic-then-placeholder guard: `precomputed_cond_val == 0` now
`eprint`s `[llvm-lib] ERROR: If-terminator cond translated to null (...)` and
substitutes a constant `false` instead of crashing.

**Static fix 3 (Step 4, guarded, applied):** `translate_call_indirect` and
`translate_intrinsic` (`llvm_lib_translate_expr.spl`) built their arg lists
with a raw, unguarded `translate_operand` push — the same null-argument
LLVMBuildCall2 hazard `translate_call` was already guarded against. Added the
matching named-diagnostic + i64-0-placeholder guard to both arg loops (and a
null-target guard on `translate_call_indirect`'s `fn_ptr`).

**Run 3** (all 3 fixes applied): Stage 1 still exit 139, crash again
immediately after (and only after) `TEMP-PROBE compiling function:
get_cli_args` — my new If-terminator guard did NOT fire, meaning the crash is
NOT at the If-terminator this time (or precomputed_cond_val was non-null but
something else in that path crashed), and no other new guard fired either.
Only one `TEMP-PROBE` line printed in the entire run (vs 3 in run 2),
consistent with the doc's non-deterministic-iteration-order theory — a
different/earlier function-processing order this run. The crash is somewhere
inside `compile_function` for `get_cli_args` (or later, before the next
`TEMP-PROBE` would have printed) that is **not yet instrumented** — none of
the existing named guards (translate_call args/callee, translate_binop
operands, ret coercion, If-cond, call_indirect/intrinsic args) fired. Probe
reverted (`compile_function` no longer prints).

**Honest state at end of session:** `_3` use-before-def and the residual
post-diagnostic crash from run 13 were NOT reproduced this session (different
nondeterministic crash site both runs). Two real, code-reading-confirmed
lowering/backend gaps were fixed (match/switch merge placeholder;
If-terminator null-cond guard) plus 2 more null-arg guards, but Stage 1 is
still SIGSEGV with zero diagnostics printed before the crash in both runs 2
and 3 — meaning there is at least one more unguarded/unlowered path reachable
from very early in `get_cli_args` (or a sibling small function iterated
first) that no current instrumentation covers. Next session: re-add the
function-name probe (temporarily) plus instrument `compile_function`'s
block/value-map setup phase itself (block creation, param mapping,
`local_types` construction) — the crash may be there rather than in any
`translate_*` call, since none of those are printing a diagnostic before
the SIGSEGV.
