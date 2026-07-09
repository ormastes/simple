# Bug: bootstrap Stage 1 SIGSEGV in LLVM `ConstantFolder::FoldCmp` via interpreted `LLVMBuildICmp` extern ([LIM-010] objcopy hint is a red herring)

- **ID:** bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09
- **Severity:** P1 (blocks `bin/simple build bootstrap` — the 3-stage self-compilation verification —
  at Stage 1 on macOS aarch64). The deployed self-hosted binary works for day-to-day tooling; only
  the bootstrap native-build path crashes.
- **Backend:** native-build LLVM IR generation, run **interpreted** by the deployed self-hosted
  `bin/simple` (`aarch64-apple-darwin-macho`, built 2026-07-05). Reproduced 2026-07-09.
- **Status:** OPEN — root-caused via crash report `~/Library/Logs/DiagnosticReports/simple-2026-07-09-084618.ips`.

## Symptom

`bin/simple build bootstrap` → `Stage 1 FAILED`:
```
error: native-build worker exited with code 139.
  interpreter: /Users/ormastes/simple/bin/simple (exit code 139)
[LIM-010] SEGFAULT (exit 139) — likely LLVM constructor conflict
[LIM-010] Ensure objcopy is available and strip_llvm_constructors() succeeded
```

## The [LIM-010] objcopy hint is a RED HERRING

`[LIM-010]` (`driver/src/cli/commands/misc_commands.rs:558`) prints an "objcopy / LLVM constructor"
guess on **any** worker exit-139. It is wrong here:
- `llvm-objcopy` **is** installed — `/opt/homebrew/opt/llvm@18/bin/llvm-objcopy` (→ Cellar/llvm@18/18.1.8)
  and llvm/llvm@22 — at paths `find_objcopy_tool()` (`compiler/src/pipeline/native_project/tools.rs:415`)
  checks directly.
- Re-running the bootstrap with `/opt/homebrew/opt/llvm@18/bin` prepended to `PATH` produces the
  **identical** SIGSEGV. So `strip_llvm_constructors()` is not the failure.

Recommend making `[LIM-010]` not assert an objcopy cause unconditionally on 139 (it cost real
debugging time chasing objcopy).

## Real root cause (from the crash backtrace)

`EXC_BAD_ACCESS (SIGSEGV) / KERN_INVALID_ADDRESS`, crashing thread `simple-main`, PC in:
```
llvm::ConstantFolder::FoldCmp(llvm::CmpInst::Predicate, llvm::Value*, llvm::Value*) const   ← crash frame
llvm::IRBuilderBase::CreateICmp(...)
LLVMBuildICmp
core::ops::function::FnOnce::call_once                     (extern binding thunk)
simple_compiler::interpreter::interpreter_extern::call_extern_function_with_values
simple_compiler::interpreter::interpreter_call::evaluate_call
... (deep interpreter recursion — 184 frames, depth-16 recursion of handle_method_call_with_self_update)
simple_compiler::interpreter::interpreter_eval::evaluate_module_impl
simple_driver::exec_core::ExecCore::run_file_interpreted_with_args
simple_driver::cli::commands::misc_commands::handle_run
```

So: the native-build worker runs the LLVM-IR-generation Simple code **interpreted**
(`run_file_interpreted_with_args`); a Simple `LLVMBuildICmp(builder, pred, lhs, rhs, name)` extern call
reaches LLVM with a **bad `llvm::Value*` operand** (lhs or rhs), and `ConstantFolder::FoldCmp`
dereferences invalid memory → SIGSEGV. `far=0` / `KERN_INVALID_ADDRESS` is consistent with a
null/garbage `Value*`.

Most likely one of:
1. **Interpreter FFI marshalling of opaque `llvm::Value*` handles** — `call_extern_function_with_values`
   corrupts/zeroes a pointer-typed argument passed to `LLVMBuildICmp` (same family as the other
   interpreter pointer/marshalling bugs, e.g. `bug_u8_cast_push_marshalling`).
2. **Simple-side codegen** passing a null/undef value operand to `LLVMBuildICmp` (a missing/ordering
   bug in the Simple LLVM IR builder that only shows up on this input).

## Update 2026-07-09 — it's a CASCADE, common cause = interpreter FFI pointer marshalling in native-build

A diagnostic experiment (temporary null-operand guard in `sffi/llvm_codegen.spl:llvm_build_icmp`,
now reverted) invalidated the native cache and forced a fuller recompile, which surfaced a **second,
distinct** native-build crash that aborts even earlier:
```
LLVM ERROR: ABI alignment must be a 16-bit integer          (exit 134, SIGABRT)
llvm::report_fatal_error(...)
llvm::DataLayout::DataLayout(llvm::StringRef)
llvm::Module::setDataLayout(llvm::StringRef)
simple_compiler::interpreter::interpreter_extern::call_extern_function_with_values   ← same FFI path
```
The aarch64-darwin datalayout literal in `llvm_target.spl:datalayout()` (`"e-m:o-i64:64-i128:128-
n32:64-S128-Fn32"`, line 147) is **valid** (max alignment 128) — LLVM is not rejecting that string.
So LLVM received a **corrupted** datalayout `StringRef` (garbage bytes parsed as an out-of-range
alignment). That, plus the ICmp crash receiving a bad `llvm::Value*`, means **both** failures are
LLVM C-API calls reached through `call_extern_function_with_values` with a **bad pointer/`StringRef`
argument** — i.e. the strongest single hypothesis is now **interpreter FFI marshalling of
pointer/opaque/`text` arguments in the native-build path**, not two independent codegen bugs.

Caveat: the deployed binary's native-build produced this very binary earlier, so the marshalling
defect is either recent (a peer interpreter/FFI change) or triggered only by a specific arg
shape/order that the current bootstrap sources hit. The guard experiment also proved the ICmp site is
reachable and the build *would* advance past it if the operand were valid — consistent with
"transient bad pointer" rather than "always-null operand".

## Update 2026-07-09 (later) — #130 VALIDATED this diagnosis + fixed the ICmp wall

Peer commit `bfd98b03 fix(hir): stop wiping call/method args under SIMPLE_BOOTSTRAP (#130)`
(Simple-source, `src/compiler/20.hir/hir_lowering/expressions.spl`) landed. Re-running the bootstrap
on that tree: the failure moved from the **ICmp SIGSEGV (139)** to the **DataLayout abort (134)** —
i.e. #130 fixed the bad-`llvm::Value*`-operand crash exactly as this bug predicted (it WAS
call/method args being wiped under `SIMPLE_BOOTSTRAP`), and the build now advances to the second wall
this doc already documented.

**The current front wall — same FFI-arg-corruption class, likely a case #130 missed:**
`llvm_set_data_layout(mod_, layout)` → `_lc2("LLVMSetDataLayout", mod_, layout.ptr())`
(`sffi/llvm_types.spl:79-80`). `layout` is a valid literal from `datalayout()`
(`llvm_target.spl:147`), but LLVM receives a corrupted string → "ABI alignment must be a 16-bit
integer". So the **`layout.ptr()` text-pointer argument** reaches LLVM corrupted — the same class of
bug as the ICmp operand #130 just fixed. Suggests #130's "stop wiping call/method args" fix does not
cover the `text.ptr()`-argument path (or `_lc2`/`text.ptr()` under SIMPLE_BOOTSTRAP has its own
wiping). This is the concrete next step for #79.

## Context — this is a wall of the ACTIVE #79 llvm-lib effort, not an independent regression

The LLVM-lib native-build path is under active peer development (`#79 stage4 self-host redeploy`),
with 8 `llvm-lib`/`llvm-ffi` commits in the last 3 days, several fixing this exact crash class:
`7984ab3ad7 fix(llvm-lib): thread value_map through translators + key operands by LocalId.id`
(operand-value mapping — directly the bad-`llvm::Value*`-ICmp-operand here),
`50427136eb fix(llvm-lib): refuse to emit an IR-verification-failed module (was segfault)`,
`747448c900`/`ff36210a60` (per-arch target-init). So these crashes are the **current walls** of that
in-flight effort — coordinate with #79 rather than patching independently (a solo guard/fix would
collide with the operand-mapping work already underway). This doc contributes the DataLayout wall +
the FFI-marshalling common-cause hypothesis + the [LIM-010] debunk to that thread.

## Fix direction

Instrument the `LLVMBuildICmp` extern binding (or `call_extern_function_with_values` for opaque
pointer args) to log/validate the two `llvm::Value*` operands before the call; compare the pointer
values seen by the interpreter vs. what LLVM receives, to decide between (1) marshalling corruption
and (2) a genuine null operand from Simple codegen. If (1), fix the interpreter's opaque-pointer
extern marshalling; if (2), fix the Simple LLVM IR builder call site. Per `.claude/rules/bootstrap.md`,
the fix belongs in pure-Simple (the IR builder) or the interpreter FFI path, and the deployed binary
re-built — not a fall-back to the seed.

## Update 2026-07-09 (later still) — #133 cleared the DataLayout wall; new wall = unresolved-callee in `translate_call`; FIXED (isolated)

Peer commit `d16a8883 fix(bootstrap): lower function params under SIMPLE_BOOTSTRAP (#133)`
(`declaration_lowering.spl` + `mir_data.spl`) landed on `origin/main` and **cleared the DataLayout
abort (134)** documented above. Re-running `bin/simple build bootstrap` on that tree, Stage 1 now
fails at exit **139** (SIGSEGV, same `[LIM-010]` red-herring hint), preceded by:
```
[llvm-lib] ERROR: unresolved function call, skipping instruction — generated code will be broken
```
emitted from `translate_call` at `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:478-480`
(callee resolution: `Const(Str(name))` → `fn_name` → `llvm_get_named_function`/`func_map` fallback;
`Copy(local)`/`Move(local)` → `get_value(value_map, local)` indirect call; `func_ref == 0` ⇒ the call
instruction is dropped, leaving broken IR that later SIGSEGVs).

**Diagnosis.** Added a temporary diagnostic `eprint` in the `func_ref == 0` branch of `translate_call`
printing the callee kind/name/local-id/func_map-membership, ran ONE `bin/simple build bootstrap`, and
captured exactly one hit (module compiled far enough this time to hit this instruction exactly once
before the compile aborted):
```
[llvm-lib] UNRESOLVED callee kind=Const name='rt_cli_get_args' local=-1 func_map_has_name=false
```

**Root cause.** `rt_cli_get_args` is a real, linkable runtime extern — implemented in
`src/runtime/runtime_native.c:1198` (`SplArray* rt_cli_get_args(void)`, declared in `runtime.h:495`,
weak fallback in `runtime.c:1538`) and called directly via `extern fn rt_cli_get_args() -> [text]` from
`src/app/sj/main.spl:10`/`src/app/sj_daemon/main.spl:10`. But `declare_runtime_functions()`
(`llvm_lib_translate.spl:156+`) — the hardcoded list of `rt_*` runtime functions pre-declared into every
LLVM module before translation — never declared `rt_cli_get_args` (only its sibling `rt_get_args` is
declared, at line 237). Since `rt_cli_get_args` is an `extern fn` (no body), it's also absent from
`func_map` (built from `mir_module.functions`, i.e. functions with bodies). So both callee-resolution
paths in `translate_call`'s `Const(Str(name))` branch missed → `func_ref == 0` → the call is dropped →
broken IR for that one call site. This is the exact "runtime/extern function called by name but never
forward-declared" candidate this doc's Step-2 guidance predicted, and it's the concrete gap `#129`
("llvm-lib runtime-builtin decls") was tracking (see plan doc's "Out of scope" section, now partially
in-scope). **Important correction (see "State after this run" below): this drop is a real, independent
bug worth fixing, but it is NOT what causes the Stage-1 SIGSEGV (139)** — crash-report comparison
proves the fatal crash is unchanged whether or not this specific call resolves.

**Fix applied (isolated, low-risk, additive-only).** Added one line to `declare_runtime_functions()`
in `src/compiler/70.backend/backend/llvm_lib_translate.spl`, mirroring the existing `rt_get_args`
declaration exactly (same ABI — no args, pointer return):
```
declare_fn(mod_, "rt_cli_get_args", llvm_function_type(ptr_ty, [], false))
```
The temporary diagnostic `eprint` in `translate_call` was fully reverted afterward (`jj diff` on
`llvm_lib_translate_expr.spl` shows no changes) — only the additive declaration in
`llvm_lib_translate.spl` remains, left **uncommitted** for review.

**A second, separate bug found by code-reading (NOT applied — reporting for #79, do not solo-patch).**
While reading `translate_call` to diagnose the above, found that its inline `Copy(local)`/`Move(local)`
match arms (lines ~476-483) call `func_ref = get_value(value_map, local)` — passing the raw `LocalId`
struct instead of its inner `.id: i64` field, so `value_map.contains(local_id)` in `get_value` can never
match (keys are pure `i64`) and any **indirect call whose callee is a `Copy`/`Move` operand** would
always resolve `func_ref == 0` (dropped call) — same defect class, and almost the same line numbers, as
`7984ab3ad7 fix(llvm-lib): thread value_map through translators + key operands by LocalId.id` (2026-07-08),
which fixed this *exact* pattern in the sibling `translate_operand` function (`llvm_lib_translate_expr.spl`
lines 597-600: `get_value(value_map, local.id)`) and in the `SetField` inline match, but did **not** touch
`translate_call`'s own inline match. Proposed fix (one-line-per-arm, matching the established pattern
`7984ab3ad7` already used elsewhere in this file):
```
case Copy(local): func_ref = get_value(value_map, local.id)
case Move(local): func_ref = get_value(value_map, local.id)
```
Not applied here per this doc's "Step 3" guidance — the guide explicitly calls this class ("indirect-call
callee not in value_map", downstream of #133 param-lowering) active `#79` territory landing multiple
commits/day; a solo patch risks colliding with in-flight `#79` work. Reporting precisely so `#79` can
pick it up (it was not the wall actually hit on this run — the wall hit was the `Const` path
`rt_cli_get_args` gap above — but it is real, latent, and one line away from a fix).

**State after this run — CORRECTED: the fix does NOT advance Stage 1; the fatal wall is unchanged.**
Initial framing of this run (now corrected below) claimed the fix "advanced the wall" because the
`[llvm-lib] ERROR: unresolved function call` line went from 1 occurrence (pre-fix) to 0 (post-fix).
That part is true and verified. But **the fatal event — exit 139 — is unchanged**, and a direct
crash-report comparison disproves the "advanced" narrative:

- Pre-fix run (`rt_cli_get_args` unresolved, then SIGSEGV): crash report
  `~/Library/Logs/DiagnosticReports/simple-2026-07-09-134458.ips`.
- Post-fix run (`rt_cli_get_args` resolves cleanly, still SIGSEGV): crash report
  `~/Library/Logs/DiagnosticReports/simple-2026-07-09-134732.ips`.

Parsed both `.ips` files: **identical** `EXC_BAD_ACCESS` / `SIGSEGV` / `KERN_INVALID_ADDRESS at 0x0`,
and **byte-identical** top-8 crashing-thread frames in both:
```
llvm::ConstantFolder::FoldCmp(llvm::CmpInst::Predicate, llvm::Value*, llvm::Value*) const
llvm::IRBuilderBase::CreateICmp(llvm::CmpInst::Predicate, llvm::Value*, llvm::Value*, llvm::Twine const&)
LLVMBuildICmp
core::ops::function::FnOnce::call_once
simple_compiler::interpreter::interpreter_extern::call_extern_function_with_values
simple_compiler::interpreter::interpreter_call::evaluate_call
simple_compiler::interpreter::expr::calls::eval_call_expr
simple_compiler::interpreter::expr::evaluate_expr
```
This proves the `LLVMBuildICmp`/`ConstantFolder::FoldCmp` SIGSEGV was **already** the fatal Stage-1
crash *before* this session's fix — the `rt_cli_get_args` unresolved-callee message and the SIGSEGV
are two separate, co-occurring events during the same Stage-1 compile, not cause-and-effect. The
`translate_call` "call is dropped → broken IR → downstream SIGSEGV" causal story (written earlier in
this doc, describing the `rt_cli_get_args` case specifically) is **wrong for this crash** — the crash
site/order is identical whether or not that particular call resolves.

**Honest summary:** this session's fix is a real, verified, worthwhile bug fix (a genuinely dropped
runtime call, now resolved, additive and safe — keep it) but it does **not** move Stage 1 forward.
The actual front wall — present both before and after this fix, i.e. it is the same wall #130
(`bfd98b03`) was supposed to have fixed — is the `LLVMBuildICmp` SIGSEGV. Either (a) #130's
"stop wiping call/method args" fix only covers some call/method-arg sites and this crash is a
different, uncovered site, or (b) the fix is incomplete/order-sensitive for whatever construct
precedes this particular `ICmp`. **Not diagnosed further in this session** — the guide's Step 1
diagnostic-eprint method should be repeated on the `LLVMBuildICmp` extern binding / the interpreter's
`call_extern_function_with_values` opaque-`llvm::Value*` marshalling (this doc's original "Fix
direction" section, written before #130/#133 landed, already outlines this — it remains the correct
next step, now confirmed still-applicable rather than superseded). This is genuinely `#79`/#130
territory: a recurring/unfixed instance of an already-diagnosed crash class, not a new bug shape.
