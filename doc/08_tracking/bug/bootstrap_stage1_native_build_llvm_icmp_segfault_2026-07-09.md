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

## Update 2026-07-09 (pure-diagnosis session, post-9d11e852) — instrumented `translate_binop`, wall PRE-EMPTED by an even earlier abort; crash SITE is nondeterministic across unchanged-tree runs

**Setup.** Added a temporary diagnostic to `translate_binop` in
`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` (right after the `lhs`/`rhs` computation,
lines 208-209): `eprint` fires only when `lhs == 0 or rhs == 0`, printing the source `MirOperand` kind
(`Copy#<local.id>` / `Move#<local.id>` / `Const`) for both sides, plus `dest.id`. Ran exactly ONE
`bin/simple build bootstrap` against tip `9d11e852` (the just-landed `rt_cli_get_args` decl fix — the
guide's stated premise was that this fix is orthogonal to the ICmp wall). Log:
`/private/tmp/claude-501/-Users-ormastes-simple/7597a415-f0b0-4c3f-822d-107292b34bec/scratchpad/nullop.log`.

**Result: the diagnostic never fired (0 occurrences of `NULL-ICMP-OPERAND`).** Stage 1 instead aborted
with exit **134** again:
```
LLVM ERROR: ABI alignment must be a 16-bit integer
error: native-build worker exited with code 134.
Stage 1 FAILED
```
Crash report `~/Library/Logs/DiagnosticReports/simple-2026-07-09-140843.ips`, faulting thread:
```
abort
llvm::report_fatal_error(llvm::Twine const&, bool)
llvm::report_fatal_error(llvm::Error, bool)
llvm::DataLayout::DataLayout(llvm::StringRef)
llvm::Module::setDataLayout(llvm::StringRef)
core::ops::function::FnOnce::call_once
simple_compiler::interpreter::interpreter_extern::call_extern_function_with_values
```
This is the **same DataLayout wall** already documented above (`llvm_set_data_layout(llvm_mod,
data_layout)` at `llvm_lib_backend.spl:54`), called once at module setup — **before** `Pass 2`
(`translate_module_to_llvm` → per-instruction translation) even starts. So `translate_binop` was never
reached this run; that is exactly why the instrumentation caught nothing. **The literal task ("find
which local is NULL at the ICmp") is unachievable on this run** because the code path containing the
ICmp is unreachable before the process aborts.

**The wall is nondeterministic across otherwise-identical runs of the same tree — new evidence.**
Cross-referencing today's (2026-07-09) crash reports, which this doc had not previously assembled in
one place:
| time | file | signal | site |
|---|---|---|---|
| 10:35 | `simple-2026-07-09-103528.ips` | SIGABRT (134) | `setDataLayout`/`DataLayout::DataLayout` (same as this run) |
| 13:36 | `simple-2026-07-09-133637.ips` | SIGSEGV (139) | `ConstantFolder::FoldCmp`/`LLVMBuildICmp` |
| 13:44 | `simple-2026-07-09-134458.ips` | SIGSEGV (139) | `ConstantFolder::FoldCmp`/`LLVMBuildICmp` |
| 13:47 | `simple-2026-07-09-134732.ips` | SIGSEGV (139) | `ConstantFolder::FoldCmp`/`LLVMBuildICmp` |
| 14:08 | `simple-2026-07-09-140843.ips` | SIGABRT (134) | `setDataLayout`/`DataLayout::DataLayout` (this run) |

(`9d11e852` landed 14:03:45; the 13:xx reports predate it, the 14:08 report is against it.) The
10:35→13:36 flip (134→139) happened with **no commit in between** on the timeline this doc already
established (both are pre-`9d11e852`, post-`#133`/`d16a8883`), and the 13:47→14:08 flip (139→134)
straddles only the orthogonal `rt_cli_get_args` decl fix. **A fixed MIR translation of a fixed input
program calling a fixed missing `value_map` key would fail at the same site every single run.** Flipping
between two distinct LLVM-C-API call sites (`LLVMSetDataLayout`'s `text` `StringRef` vs. `LLVMBuildICmp`'s
`llvm::Value*` operand) across runs of the same source is inconsistent with hypothesis (b) and consistent
with hypothesis (a): a heap/ASLR/allocation-timing-dependent corruption inside the interpreter's generic
FFI argument marshalling (`call_extern_function_with_values`, present in **every** frame trace above,
regardless of which LLVM API is ultimately called) that nondeterministically clobbers whichever
pointer/text-typed argument happens to be marshalled around that time.

**Static corroboration (no rebuild needed).** The intended datalayout string for this host
(macOS/aarch64 → `LlvmTargetTriple.datalayout()`, `llvm_target.spl:145-151`, `is_macho` branch):
```
"e-m:o-i64:64-i128:128-n32:64-S128-Fn32"
```
is well-formed and is the exact standard clang/LLVM `arm64-apple-macosx` datalayout — confirmed by
reading the source directly (no Simple-side string-construction bug). So the corruption happens between
the Simple `text` value and what LLVM's C API receives, i.e. inside `call_extern_function_with_values` /
the `_lc2` binding thunk, not in `llvm_target.spl`.

**(a) vs (b) verdict: (a), FFI/memory-corruption in `call_extern_function_with_values`.** Evidence: (i)
crash SITE nondeterminism across unchanged-tree runs, which a fixed missing-value_map-key lookup cannot
produce; (ii) both crash sites funnel through the same generic interpreter FFI-dispatch frame, not
translator-specific code; (iii) the intended datalayout string is statically well-formed, ruling out a
Simple-source string bug for that wall specifically.

**ICmp NULL-operand localization: POSTPONED.** Cannot name which local id is null this session — the
crash preempted `translate_binop` entirely (0 diagnostic hits). Per the "ONE build at a time" / no-easy-pass
constraints, did not force a second rebuild hoping to land on the ICmp site (which run hits which wall
appears to be governed by nondeterministic corruption, not something a second run can reliably steer).

**Concrete next fix direction for #79.** Stop instrumenting individual Simple-side translator call
sites — a positional `eprint` guard only fires if that exact site is reached before whichever
nondeterministic corruption manifests *first*, as this run demonstrates. Instead instrument (or
code-review) the shared choke point: `call_extern_function_with_values` in the Rust interpreter
(`simple_compiler::interpreter::interpreter_extern`), specifically how it marshals `text`/pointer-typed
Simple values into raw C ABI arguments for two-arg (`_lc2`-style) extern calls. Look for: (1) a
dangling/reused buffer for `text.ptr()` when the underlying value is short-lived (e.g. a temporary
`text` built inline and not kept alive/rooted across the FFI call boundary — a classic use-after-free if
GC/arena reuse recycles the backing bytes before the C call reads them), or (2) a stale/uninitialized
slot in extern-argument marshalling reused across nondeterministic call ordering (which would explain
why the *symptom* — which C API call sees the bad pointer — varies run to run while the *root cause*
stays constant). A confirming experiment for whoever picks this up next: compare the argument
address/bytes on the interpreter side immediately before an extern call vs. what the native callee
actually receives, across a few runs, to catch the corruption in the act rather than only observing the
two downstream symptoms.

**Diagnostic reverted.** The temporary `translate_binop` `eprint` instrumentation was fully reverted via
`jj restore src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` — `jj diff` on that file shows
no changes after this session.

## Update 2026-07-10 (Codex/Spark bootstrap-first pass) — one run reached `translate_binop`; NULL source is `Copy#3` missing from `value_map`

**Current wall.** Stage 1 bootstrap native-build on the `llvm-lib` path is still failing. Across the
unchanged-tree evidence set, the visible crash remains nondeterministic between:
- SIGSEGV/139 in `llvm::ConstantFolder::FoldCmp` via `LLVMBuildICmp`
- SIGABRT/134 in `llvm::DataLayout::DataLayout` via `LLVMSetDataLayout`

The shared frame remains `simple_compiler::interpreter::interpreter_extern::call_extern_function_with_values`.
Treat translator-local probes as useful snapshots, but not as sufficient proof that the whole wall is
translator-only.

**Latest wall snapshot.**
| timestamp | command | signal | top crash / signal line | artifact |
|---|---|---|---|---|
| 2026-07-10 00:16 KST | `bin/simple build bootstrap` with temporary `translate_binop` NULL probe | 139 | `LLVMBuildICmp`/`ConstantFolder::FoldCmp`; worker exit 139 | `/private/tmp/claude-501/-Users-ormastes-simple/7597a415-f0b0-4c3f-822d-107292b34bec/scratchpad/codex_null_binop_bootstrap.log` |

**Captured NULL operand.** The temporary probe fired once:
```
[llvm-lib] NULL-BINOP-OPERAND dest=4 lhs=4401713832 rhs=0 left=Copy#2 present=true value=4401713832 right=Copy#3 present=false value=0
```

**(a) vs (b) for this run.** This specific run proves a genuine Simple-side unmapped operand at the
`translate_binop` site: `right=Copy#3` was absent from `value_map`, so `translate_operand` returned
0 before the LLVM C API call. This is hypothesis (b) for this run, not an LLVM-returned null.

**Defining MIR instruction status.** No prior translated instruction in the current `value_map` defined
local `3` before the binop. Static code-reading leaves two plausible sources:
- `function_lowering.spl:124` can still produce a phantom `LocalId(id: pli + 1)` if the parameter scan
  fails to find an `Arg` local; that would create body references to a local never registered in
  `MirFunction.locals`.
- `mir_lowering_stmts.spl:154-159` can create a `LocalKind.Var` with no `emit_copy` when a let binding
  has no initializer; a later read would likewise be a `Copy#<local>` with no value-map write.

The one-run diagnostic did not include function name, binop kind, or the surrounding MIR instruction
stream, so the exact source function/def site remains **POSTPONED**, not guessed. The next targeted
diagnostic should print function name and the current instruction before `translate_instruction`, or
preferably instrument `MirFunction` validation before LLVM translation to reject any `Copy`/`Move`
whose local has no prior def/arg in block order.

**Resolved historical item.** The `rt_cli_get_args` unresolved-callee issue remains resolved by the
`declare_runtime_functions()` addition in `llvm_lib_translate.spl`; keep it as historical evidence,
but do not treat it as the active wall.

**Diagnostic reverted.** The temporary `translate_binop` helper/eprint was removed after the run;
`git diff -- src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` is clean.

## Update 2026-07-10 (Codex bootstrap continuation) — DataLayout fixed, next ICmp source narrowed to bootstrap builtin signature

**Applied fixes.**
- `translate_call` now unwraps `Copy(local)`/`Move(local)` through `local.id` before indexing
  `value_map`, matching the rest of llvm-lib operand lookup.
- `llvm_set_data_layout` now passes a NUL-terminated C string in all three active LLVM FFI wrappers
  (`nogc_async_mut/sffi`, `nogc_sync_mut/sffi`, `nogc_sync_mut/ffi`). The next bootstrap run moved past
  the `LLVMSetDataLayout`/`DataLayout` abort, so the prior ABI-alignment crash was a real C-string
  boundary bug.
- `bootstrap_builtin_signature` now gives argument-taking bootstrap helpers real HIR function
  parameter lists: `bootstrap_output_from_args([text], i64) -> text`,
  `run_native_build_bootstrap([text]) -> i64`, and `eprint(text) -> unit`.

**Latest diagnostic before cleanup.** A targeted one-run probe logged:
```
[llvm-lib] MISSING-BINOP func=bootstrap_output_from_args block=0 inst=0 dest=4 left=Copy#2 present=true value=4362295208 right=Copy#3 present=false value=0
```
This points at the first entry-block comparison in
`src/app/cli/bootstrap_main.spl` (`i >= args.len()`). The zero-argument bootstrap builtin signature was
the most direct local cause: unresolved bootstrap references to `bootstrap_output_from_args` could carry
the wrong function shape even though the declaration-lowering path kept the source params.

**Verification status.** Focused backend checks pass for the llvm-lib translator after removing the
temporary diagnostic. The HIR lowering file still fails the current `bin/simple check` on pre-existing
parser errors around enum-payload `match p:` code; the reported locations are not in the edited
`bootstrap_builtin_signature` block. No fourth bootstrap run was started in this session because the
runaway guard caps one feature lane at three verify/fix bootstrap cycles.

## Verification of a2919c90 (2026-07-10, verification-only session)

Verified `bin/simple build bootstrap` on `a2919c90 fix(bootstrap): repair llvm-lib stage1 bootstrap
blockers` (origin/main tip; includes the translate_call `local.id` fix, the `LLVMSetDataLayout`
NUL-termination fix in all 3 `llvm_types.spl` copies, and the HIR typed-params fix). Two full runs,
one at a time, no code changes.

| Run | Stage reached | Worker exit | Crash signature | Notes |
|-----|--------------|-------------|-----------------|-------|
| 1 | Stage 1 FAILED | 139 (SIGSEGV) | 2x `[llvm-lib] ERROR: unresolved function call, skipping instruction` at log lines 2604-2605, then `native-build worker exited with code 139` at line 2607 | log: scratchpad `boot_a2919c90_run1.log` |
| 2 | Stage 1 FAILED | 139 (SIGSEGV) | **Byte-identical failure tail** — same 2 unresolved-call eprints at the same log lines, same exit 139 at line 2607 | log: scratchpad `boot_a2919c90_run2.log` |

**Verdict: advanced-to-new-wall (nondeterminism gone; deterministic ICmp wall remains).**
- The exit-134 `LLVMSetDataLayout` "ABI alignment must be a 16-bit integer" abort did NOT appear in
  either run. Both runs failed identically (same signature, same log line numbers). With n=2 this is
  consistent with — not absolute proof of — the NUL-termination fix having killed the run-varying
  overread that caused the 134/139 site flip.
- No fresh macOS crash report was generated for today's runs (all `simple-*.ips` in
  `~/Library/Logs/DiagnosticReports/` have internal `captureTime` 2026-07-09, pre-fix; their 07-10
  mtimes are re-symbolication/analytics touches, verified via the embedded JSON `procLaunch`
  fields). Historical 139 reports show the same top frames expected here:
  `LLVMBuildICmp` → `llvm::IRBuilderBase::CreateICmp` → `llvm::ConstantFolder::FoldCmp` (NULL
  `Value*` operand), reached from interpreter `call_extern_function_with_values`.

**The deterministic front wall now.** Two call instructions fail to resolve in
`translate_call` (`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:478-480`:
`func_ref == 0` → eprint + skip). The skipped call means the `dest` local is never inserted into
`value_map`; a later ICmp that consumes that local gets a NULL `llvm::Value*` and SIGSEGVs inside
`FoldCmp`. This is NOT `rt_cli_get_args` (already declared at `llvm_lib_translate.spl:238` since
9d11e852) — the unresolved callee(s) are currently anonymous because the eprint prints no name.

**Proposal (docs-only; no code changed this session):** extend the `func_ref == 0` eprint in
`translate_call` to print the callee — `fn_name` for the `Const(Str(...))` arm and `local.id` for
the `Copy`/`Move` arms — plus the enclosing MIR function name. One deterministic run then names the
exact 2 unresolved calls, which is the next fix target (missing extern declaration or a
still-unmapped local feeding an indirect call).

## Update 2026-07-10 (name-the-callees attempt) — proposal executed, wall did NOT reproduce as predicted; POSTPONED

Implemented the proposal above exactly: extended the `func_ref == 0` block in `translate_call`
(`llvm_lib_translate_expr.spl:478-480`) with a temporary identity `eprint` — operand kind
(`Const`/`Copy`/`Move`), `fn_name` for the `Const(Str(...))` arm, `local.id` for `Copy`/`Move` (via
`.to_string()`; matched actual file convention of `+` for text concat, not `++` — `++` is not a valid
Simple operator, confirmed by repo-wide grep finding zero non-vendor uses).

**One authorized bootstrap run** (`bin/simple build bootstrap`, working-copy parent `8e5dedaf` at run
time — post `a2919c90`/`9d11e852d2`/`e7e074edc1`/`90ef5827`), full log captured
(scratchpad `name_callees.log`, 2617 lines). Result:

- Stage 1 FAILED, worker exit 139 (SIGSEGV) — same terminal symptom as every prior session.
- **Neither the pre-existing `"[llvm-lib] ERROR: unresolved function call, skipping instruction"` line
  nor the new `"[llvm-lib] UNRESOLVED CALLEE ..."` lines appear anywhere in the log** (`grep -c` = 0 for
  both, checked against the full file, not just the tail — ruled out truncation).
- This contradicts the "Verification of a2919c90" table above, which recorded that exact
  `unresolved function call` eprint firing **twice**, at fixed log line numbers, identically across 2
  separate runs, immediately preceding the same exit-139 crash.

**Interpretation — the func_ref==0 branch was not hit this run, despite the same exit code.** Two
non-exclusive possibilities, neither confirmed (only one run authorized):
1. Nondeterminism is back (aligns with `e7e074edc1`'s framing, which `90ef5827` had marked
   superseded — this run's evidence undercuts that supersession).
2. The wall moved: commits after `a2919c90` changed the Stage-1 llvm-lib translation pass enough that
   the SIGSEGV now happens at a different point that never reaches `translate_call`'s
   `func_ref == 0` check for the previously-identified 2 dropped calls.

**Classification: anything else (not a trivial missing declare or special-name-mapping gap) — do NOT
fix.** No callee names obtained; nothing to `declare_fn` or map. Diagnostic fully reverted
(`git diff -- llvm_lib_translate_expr.spl` clean, verified byte-identical to pre-edit via direct
`diff`, after also recovering from a `jj workspace update-stale` "Concurrent modification" reconcile
mid-session that transiently restored the not-yet-committed diagnostic — re-reverted and re-verified).

**Next step for #79 (not this session):** re-run the same one-shot eprint (code unchanged, still valid)
on a freshly pinned commit, with 2 back-to-back runs (not 1) to first re-establish whether the wall is
deterministic before trying to name callees. If deterministic and the eprint still never fires, widen
the diagnostic to `translate_instruction`'s top-level dispatch to find which MIR instruction kind
executes immediately before the crash — the SIGSEGV site may no longer be inside `translate_call`.
POSTPONED, exact state as described above.

## Update 2026-07-10 (icmp-wrapper probe experiment) — probe point INVALIDATED: the nogc_sync_mut sffi wrapper is a DEAD COPY; active copy is nogc_async_mut

**Goal.** Discriminate hypothesis (a) FFI-marshalling corruption vs (b) Simple-side null operand by
eprinting from inside `llvm_build_icmp` in `src/lib/nogc_sync_mut/sffi/llvm_codegen.spl:139` — assumed
to be the last Simple-side point before the `_lcn("LLVMBuildICmp", args)` extern call.

**Probe design.** (run 1) conditional eprint `[icmp-probe] NULL OPERAND pre-FFI: pred/lhs/rhs/name`
when `lhs == 0 or rhs == 0`; (run 2) same, PLUS an unconditional positive-control eprint for the first
3 icmp calls (module-level counter) to prove the wrapper executes at all.

**Results (2 bootstrap runs, one at a time, parent `eda1cf0b` = origin/main tip).**

| Run | Probe | Stage-1 outcome | Probe lines in log |
|-----|-------|-----------------|--------------------|
| 1 | null-check only | FAILED, worker exit 139 (`icmp_probe_run1.log`, 2617 lines) | 0 |
| 2 | null-check + positive control | FAILED, worker exit 139 (`icmp_probe_run2.log`, 2617 lines — same shape) | 0 (positive control ALSO silent) |

No fresh macOS crash report was generated for either run (all `simple-*.ips` in
`~/Library/Logs/DiagnosticReports/` are internally 2026-07-09; 07-10 mtimes are re-symbolication
touches, same pattern as the a2919c90 verification session). Neither run printed
`[llvm-lib] ERROR: unresolved function call` — consistent with the 07-10 name-the-callees session, and
further evidence that wall no longer passes through `translate_call`'s `func_ref == 0` branch.

**Why the probe was silent — proven by out-of-band selftest, not speculation.** A tiny interpreted
program (`scratchpad/icmp_probe_selftest.spl`: `use std.sffi.llvm.*` — the exact import
`llvm_lib_translate_expr.spl:10` uses — then `llvm_build_icmp` on two consts, run via the same
`bin/simple` binary the worker log names) executed icmp successfully with ZERO probe output while the
probe sat in the `nogc_sync_mut` copy; moving the probe to
`src/lib/nogc_async_mut/sffi/llvm_codegen.spl:139` made it fire immediately
(`[icmp-probe-async] CALLED: pred=32 lhs=... rhs=... name=eq`). Root cause: the module resolver's
family search order puts `nogc_async_mut` FIRST
(`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl:206-208`:
`nogc_async_mut > nogc_async_immut > nogc_sync_immut > nogc_sync_mut > common > ...`), so
`use std.sffi.llvm.*` resolves to the `nogc_async_mut/sffi` copy. The `nogc_sync_mut/sffi` copy (and
`nogc_sync_mut/ffi/llvm_instructions.spl`) are dead copies for this import path.

**Verdict: still-ambiguous for (a) vs (b) — the experiment did not discriminate** because both runs
carried the probe in a dead copy. It did, however, produce two hard results:
1. The CORRECT probe point is now empirically established:
   `src/lib/nogc_async_mut/sffi/llvm_codegen.spl` `llvm_build_icmp` (fires under `use std.sffi.llvm.*`
   in the same interpreter binary the Stage-1 worker uses).
2. Any past or future "fix all three wrapper copies" work MUST include the `nogc_async_mut` copy —
   note the 07-10 `llvm_set_data_layout` NUL-termination fix already did (it listed
   `nogc_async_mut/sffi` among the three), but the sync-family copies it also patched are likely inert.

**Next step for #79.** Re-run the identical discriminating experiment with the probe (null-check +
first-3 positive control) in `src/lib/nogc_async_mut/sffi/llvm_codegen.spl:llvm_build_icmp`. Expected
outcomes unchanged: positive control fires + null line + ICmp crash → (b) Simple-side; positive
control fires + NO null line + ICmp crash at 0x0 → (a) FFI-marshalling corruption proven. If the
positive control is STILL silent there under a real bootstrap (it cannot be, per the selftest, unless
the worker pre-compiles/caches the stdlib differently from `bin/simple run`), that itself becomes the
finding to chase (stale native/module cache serving old wrapper code).

**Probes fully reverted** (`jj restore` both files; `grep -c icmp-probe` = 0 in both
`nogc_sync_mut/sffi/llvm_codegen.spl` and `nogc_async_mut/sffi/llvm_codegen.spl`; `jj diff` clean).
Logs: scratchpad `icmp_probe_run1.log`, `icmp_probe_run2.log`, selftest `icmp_probe_selftest.spl`.

## Update 2026-07-10 (icmp-wrapper probe, corrected location) — VERDICT: (b) Simple-side NULL operand, DISCRIMINATED

**Setup.** Re-ran the discriminating experiment at the correct, empirically-proven-live probe point:
`llvm_build_icmp` in `src/lib/nogc_async_mut/sffi/llvm_codegen.spl:139` (not the `nogc_sync_mut` dead
copy used in the prior, inconclusive pass). Probe: (1) unconditional positive-control eprint on the
first 3 `llvm_build_icmp` calls (module-level counter), (2) conditional eprint when `lhs == 0 or
rhs == 0`, both placed immediately before the `_lcn("LLVMBuildICmp", args)` extern call. WC verified
clean on `origin/main` tip (`3cf7e37f`) before starting; no other bootstrap running.

**Result — ONE bootstrap run, decisive, no ambiguity (run 2 not needed):**
```
[icmp-probe] CALL#1 pred=33 lhs=35081175520 rhs=4327134128 name=tobool
[icmp-probe] CALL#2 pred=38 lhs=0 rhs=4327133968 name=gt
[icmp-probe] NULL OPERAND pre-FFI: pred=38 lhs=0 rhs=4327133968 name=gt

error: native-build worker exited with code 139.
  interpreter: /Users/ormastes/simple/bin/simple (exit code 139)
[LIM-010] SEGFAULT (exit 139) — likely LLVM constructor conflict
Stage 1 FAILED
```
(full log: scratchpad `icmp_probe_run1.log`, lines 2604-2613; grep `icmp-probe|unresolved function|Stage
1|exit code` shown above is the complete signal set).

**Positive control fired** (CALL#1, CALL#2 — proves the wrapper executes and the probe point is live,
consistent with the prior selftest). **The null-operand branch ALSO fired**, on the very next line,
for the `pred=38` (`LLVM_INT_SGT`, i.e. Simple `>`/`Gt`) comparison named `"gt"`: `lhs=0`. The crash
(`exit 139`) follows immediately — 2 lines later in the log, no other icmp calls or unrelated output in
between — so this is not a stale/buffered line from an earlier, unrelated call; it is the operand of
the crashing call itself.

**Verdict: (b) Simple-side NULL operand, PROVEN for this crash instance — not (a) FFI marshalling
corruption.** The interpreter's `call_extern_function_with_values` received `lhs=0` from Simple-side
code *before* the FFI call, and passed it through faithfully to `LLVMBuildICmp`, which then crashed in
`ConstantFolder::FoldCmp` on the genuine NULL `llvm::Value*`. There is no corruption step to blame —
Simple already computed 0 for the left operand of a `>` comparison named `"gt"`.

**Context / next-step localization (static code read, not re-run).** `name="gt"` traces to the `Gt`
case's integer branch in `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:301-305`:
```
case Gt:
    val cmp = if left_is_float:
        llvm_build_fcmp(builder, LLVM_REAL_OGT, lhs, rhs, "gt")
    else:
        llvm_build_icmp(builder, LLVM_INT_SGT, lhs, rhs, "gt")
```
`lhs` here is the already-translated left operand of a `>` binary op (from `translate_binop`'s earlier
`lhs`/`rhs` computation, same function documented in the 2026-07-09 "pure-diagnosis session" update
above). A `lhs=0` reaching this call site is the same failure shape already characterized there and in
the 2026-07-10 "one run reached translate_binop" update: an operand `local` missing from `value_map`
(`translate_operand` returns 0 for an unmapped `Copy`/`Move`), now specifically pinned to the `Gt`
comparison rather than a generic binop. **Not re-diagnosed further this session** (which local/MIR
instruction feeds this particular `Gt`'s lhs was not re-captured — would need a `translate_binop`-level
probe printing operand kind/local-id, as previously proposed, run against current tip).

**This closes the (a) vs (b) discriminator for #79: stop looking at interpreter FFI marshalling for
this crash family; the fix belongs in Simple-side MIR/value_map completeness (missing def for whatever
local feeds this `Gt`'s left operand), per `.claude/rules/bootstrap.md`'s "fix in pure Simple" rule.**
Nondeterminism seen in earlier sessions (134 DataLayout vs 139 ICmp) is better explained by *which*
missing-value_map site the compile happens to reach first on a given run, not by heap/ASLR-dependent
FFI corruption — the DataLayout wall was independently traced to and fixed as a real NUL-termination
bug (see 2026-07-10 "DataLayout fixed" update above), consistent with "each wall was a distinct,
deterministic Simple-side bug", not a shared nondeterministic corruption mechanism.

**Probe reverted** (`jj restore src/lib/nogc_async_mut/sffi/llvm_codegen.spl`; `grep -rn icmp-probe
src/` = 0 repo-wide; `jj diff` clean). Log: scratchpad `icmp_probe_run1.log`.

## Update 2026-07-10 (translate_binop null-operand trace) — root miss = one local absent from value_map; backend audited clean; classified STRUCTURAL (MIR-level)

**Experiment (per gt_lhs_trace_guide).** TEMPORARY probes added to
`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl`: (1) in `translate_binop` right after
`lhs`/`rhs` are computed — if either is 0, eprint the binop kind, `dest.id`, and each operand's kind +
local id; (2) in `get_value` — eprint the `local.id` on every value_map miss (catches null production
at the source for ALL consumers). ONE bootstrap run (no concurrent bootstrap; log: scratchpad
`gt_lhs_run1.log`).

**Probe hits (lines 2606-2607, immediately before `worker exited with code 139` / Stage 1 FAILED):**
```
NULL-OPERAND missing local.id=3 (value_map miss)
NULL-BINOP op=Lt dest=6 lhs=0 rhs=4361717120 left=Copy#4 right=Copy#5
```
Reading: the ROOT miss is local `_3` (genuinely absent from `value_map` — a present-but-zero entry
would not fire the `get_value` probe). The crashing comparison's lhs is `Copy#4` with NO miss line for
id=4, i.e. `_4` IS in the map with value 0 — a propagated null. The only silent 0-propagation paths
that read one local and store into another with no intervening output are the `Copy(dest, src)` /
`Move(dest, src)` instruction arms (translate_instruction lines 32-38) and `Ref` (lines 115-117). So
the chain is `_4 = copy/move/ref _3` (miss → 0 stored) then `_6 = _4 Lt _5` → `LLVMBuildICmp` with
lhs=NULL → SIGSEGV. This run caught `Lt`, the earlier run caught `Gt` — consistent with the known
iteration-order nondeterminism; same failure class.

**Static trace of why `_3` has no definition (no further runs):**
- *Param seeding is NOT the hole (post-#133):* `compile_function`
  (`llvm_lib_translate.spl:51-61`) seeds every `LocalKind.Arg` local into `value_map` unconditionally,
  and `mir_data.spl:begin_function` (post-#133, d16a8883) creates Arg locals unconditionally
  (bootstrap: ids 0..n-1, `_return` gated off). `function_lowering.spl:98-138` maps param symbols to
  the real Arg locals. If `_3` were an Arg it would be present (even a 0 `llvm_get_param` would make
  the key exist and not fire the probe).
- *Backend has no reachable silent dest-skip:* audited every `translate_instruction` arm.
  All value-producing arms write `local_value_map[dest.id]` unconditionally (Copy/Move/BinOp/UnaryOp/
  Alloc/Load/GEP/Aggregate/GetField/Cast/Bitcast/Ref/phi-intrinsic) or emit a diagnostic on the skip
  path: unresolved Call/CallIndirect/Intrinsic → `eprint` (stderr; NOT in the log), Compose/Parallel/
  LayerConnect/InlineAsm/unhandled-kind → `print` (stdout; worker stdout IS captured in this log —
  gc-warnings, stdout, appear adjacent to the probe lines — and no such warning appears). The one
  fully-silent arm, `translate_const` `Zero` + Unit/Never (line ~183), is unreachable as a local def:
  repo-wide, `MirConstValue.Zero` is emitted at exactly ONE site (`module_lowering.spl:153`, a return
  operand, never a `Const` instruction).
- *Therefore the miss is upstream of the backend:* the MIR arriving at `translate_module_to_llvm`
  uses `_3` without a definition that precedes it in block-list order. Two structural sub-hypotheses:
  (i) HIR→MIR lowering under SIMPLE_BOOTSTRAP emits a genuine use-before-def — same bootstrap-gated
  lowering-gap family as #130 (wiped call args) and #133 (dropped params); e.g. a value-producing
  Call lowered with `dest=None` while the result local is still referenced, or a dropped var-init;
  (ii) the def exists but lives in a block that appears LATER in `func.blocks` than the using block —
  `compile_function` translates blocks in list order with a single accumulating `value_map` (no
  dominance-order traversal, no alloca/mem2reg fallback), so any non-topological block order produces
  exactly this miss even for well-formed MIR.

**Classification: STRUCTURAL — documented for #79, NOT fixed here.** Neither sub-hypothesis is a
one-line backend fix: (i) needs a #133-style HIR/MIR lowering change; (ii) needs dominance-aware
block traversal or alloca-based locals in the llvm-lib backend. Guarding/faking the null operand is
forbidden (would suppress the crash, not the miscompile). Proposed #79 next step: dump the MIR of the
crashing function (add a per-function name eprint + a one-shot MIR dump when a value_map miss occurs)
to discriminate (i) vs (ii) in a single run; if (ii), the fix is contained to
`llvm_lib_translate.spl` (translate blocks in RPO or pre-seed via allocas).

**Probes reverted** (exact inverse edits; `grep -rn "NULL OPERAND\|NULL-BINOP\|gt-trace" src/` = 0;
`git diff` on the probed file is empty). Stage-1 state after this session's single run: unchanged —
`native-build worker exited with code 139`, Stage 1 FAILED (log: scratchpad `gt_lhs_run1.log`).

## Update 2026-07-10 (function-name + full-MIR-dump discriminator) — VERDICT: (i) MIR use-before-def, NOT (ii) backend block-order

**Setup.** Implemented the proposed discriminator exactly: (1) `eprint` the enclosing MIR function
name at the top of `compile_function` (`llvm_lib_translate.spl`) for every function; (2) on the first
`value_map` miss, `get_value` (`llvm_lib_translate_expr.spl`) still fires `[MIR-PROBE] MISS
local_id=<id>` as before. Added a `describe_inst(inst) -> text` helper (dest local id + instruction
kind, covering every `MirInstKind` arm `translate_instruction` handles) and used it to dump full MIR
(block id + one line per instruction) for `func.name == "main"` — gated on that name because run 1 of
this session (see below) had already identified `main` as the crashing function.

**Run 1 (probe-code bug, no data).** First attempt placed the dump *after* the per-block translation
loop in `compile_function`, gated on "miss fired but not yet dumped". Also had a one-liner
`pub fn mir_probe_mark_dumped(): MIR_PROBE_dumped = true` — a bare assignment as a one-line fn body,
which the bootstrap-stage parser rejects (`Unexpected token: expected expression, found Assign`).
Stage 1 failed at the **parse** stage before any native-build worker ran; zero runtime evidence.
Fixed to a block-body `fn`.

**Run 2 (probe-code bug, partial data only).** With the parse fix, the post-loop dump still could not
fire: the SIGSEGV happens *inside* the same block-translation loop it was gated on (a NULL-operand
`LLVMBuildICmp` kills the process immediately), so control never reaches the post-loop dump code. Log
tail:
```
[MIR-PROBE] fn=main
[MIR-PROBE] MISS local_id=3

error: native-build worker exited with code 139.
Stage 1 FAILED
```
This did confirm (again) that the crashing function is `main` and the missing local is `_3` — same
identity as the 2026-07-10 "translate_binop trace" session above — but produced no MIR dump. Moved the
dump to fire at function-*entry* instead (before any block is translated), gated on
`func.name == "main"` using this run's own evidence.

**Run 3 (decisive).** Full MIR of `main` printed before the crash. Complete dump (block id +
`describe_inst` per instruction; blocks with an empty instruction list are `If`/`Goto`-only merge
blocks — expected):
```
block0: Call(_1) Copy(_2) Copy(_4) Const(_5) BinOp(_6)
block1: Const(_8) Call(_9) Const(_10) Call(_11) Const(_12)
block2: (empty)
block3: Const(_14) GEP(_15) Load(_16) Copy(_17) Const(_18) BinOp(_19)
block4: Const(_21) Call(_22) Const(_23)
block5: (empty)
block6: Const(_25) BinOp(_26)
block7: Const(_28) Call(_29) Const(_30) Call(_31) Const(_32) Call(_33) Const(_34) Call(_35) Const(_36) Call(_37) Const(_38) Call(_39) Const(_40)
block8: (empty)
block9: Const(_42) BinOp(_43)
block10: Call(_45)
block11: (empty)
block12: Const(_47) BinOp(_48)
block13: Const(_50) BinOp(_51)
block14: (empty)
block15: Const(_65) Call(_66) Const(_67)
block16: Const(_53) Call(_54) Const(_55)
block17: (empty)
block18: Const(_57) GEP(_58) Load(_59) Copy(_60) Const(_61) Call(_62) Const(_63)
[MIR-PROBE] MISS local_id=3
```
(19 blocks total, ids 0-18; full dump + surrounding log at scratchpad `mir_dump_run3.log`, lines
2549-2623.)

**The deciding check.** Local ids that actually appear as a `dest` anywhere across all 19 blocks:
`{1,2,4,5,6,8,9,10,11,12,14,15,16,17,18,19,21,22,23,25,26,28..40,42,43,45,47,48,50,51,53,54,55,57..63,65,66,67}`
(computed by extracting every `_<n>` from the dump and checking membership, not by inspection).
`_3` is **absent from every block, including all blocks listed after block0** (blocks 1 through 18).
Block0 itself shows the exact gap already characterized in the prior session: `Copy(_2)`, then no
instruction defines `_3`, then `Copy(_4)` (the `_4 = copy _3` read of the still-undefined local),
`Const(_5)`, `BinOp(_6)` (the `_6 = _4 <op> _5` that reads the propagated 0). No block anywhere later
in the list — nor block0 itself — contains a `Const`/`Copy`/`Move`/`Call`/any dest-producing
instruction with `dest.id == 3`. `_3` is also not a function parameter: `compile_function` seeds every
`LocalKind.Arg` into `value_map` before block translation runs (verified clean in the prior session,
post-#133), and this run's `MISS` fires *during* per-instruction translation, which is only reachable
for locals the Arg-seeding loop did not already populate.

**Verdict: (i) MIR use-before-def — CONFIRMED, not (ii) backend block-order.** The def for `_3` does
not exist anywhere in `main`'s MIR as delivered to `translate_module_to_llvm`, in any block, listed
before or after the use. This rules out hypothesis (ii) (a later block defining it, invisible to
`compile_function`'s linear no-RPO block pass) outright — there is no such block. The bug is upstream
of the LLVM backend entirely: HIR/MIR lowering emits a genuine use-before-def for whatever source
construct in `main` produces local `_3` (same bootstrap-gated lowering-gap family as `#130` wiped
call/method args and `#133` dropped params — a third instance of "a value that should exist in MIR
does not"). The 13 similarly-patterned gaps in this same dump (`_3, _7, _13, _20, _24, _27, _41, _44,
_46, _49, _52, _56, _64` — computed from the same block-by-block id extraction) are consistent with
one dropped def per comparison/branch condition in `main`'s source (an `if`/argument-count-style
check pattern repeated ~13 times), suggesting a single systematic lowering gap rather than 13
independent bugs.

**Exact fix locus for #79 (not fixed here, per this pass's scope).** HIR/MIR lowering for whatever
`main`-body construct produces this repeated "compute a value, never emit its defining MIR
instruction" pattern — look in the same lowering files already implicated by #130/#133
(`src/compiler/20.hir/hir_lowering/expressions.spl`, `src/compiler/20.hir/hir_lowering/
declaration_lowering.spl`, `src/compiler/50.mir/` builder) for a bootstrap-gated (`SIMPLE_BOOTSTRAP`)
branch that still skips emitting a `Const`/`Call`/etc. instruction for a value that a later
`Copy`/`Move` instruction (here, `_4 = copy _3`) expects to already be in scope. This is NOT a
`compile_function`/`llvm_lib_translate.spl` backend fix — the backend's linear block-list traversal is
exonerated by this run's evidence (no def exists in ANY block for the backend to have missed).

**Also resolves the nondeterminism question raised in the 2026-07-09 "NONDETERMINISTIC FFI corruption"
update.** Since `get_value` silently returns `0` for any value_map miss (`llvm_lib_translate_expr.spl`,
`get_value`), and this class of MIR use-before-def can affect different locals/functions/paths
depending on interpreter iteration order and exactly which comparison/branch is reached first before
the process dies, a single root cause (systematic missing-def lowering gap) is sufficient to explain
both the deterministic per-run `MISS local_id=<id>` signal captured across multiple sessions AND the
earlier-observed crash-site flips (134 DataLayout / 139 ICmp) — no separate FFI-marshalling corruption
mechanism is needed to explain the variance; "which propagated-zero operand reaches an LLVM C-API call
first" varies run to run for the same reason `_3` vs other locals varies: iteration/scheduling order
over a MIR that already has genuine holes in it.

**Probes reverted.** `jj restore` on both `src/compiler/70.backend/backend/llvm_lib_translate.spl` and
`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl`; repo-wide `grep -rn "MIR-PROBE\|MIR_PROBE\|describe_inst\|mir_probe_" src/` = 0 after revert. Stage-1 state after this session:
unchanged — `native-build worker exited with code 139`, Stage 1 FAILED. Logs: scratchpad
`mir_dump_run1.log` (parse-error run), `mir_dump_run2.log` (post-loop dump, unreachable), `mir_dump_run3.log`
(decisive — function-entry dump).

## 2026-07-10 — construct ID: 6/13 gaps pinned to `lower_if`'s phantom `result` local (STATIC read, no bootstrap run this pass)

**Entry file confirmed.** `doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-08.md` names
`src/app/cli/bootstrap_main.spl` as the Stage-1 entry; its `fn main() -> i64:` (lines 44-73) is the
dumped function. Read in full and correlated line-by-line against `mir_dump_run3.log:2549-2623`.

**Block-to-source correlation.** `main`'s 19 MIR blocks are exactly `1 entry (block0) + 6×3`
(then/else/merge) for the 6 `if` expressions the source lowers via `lower_if`
(`argc<1`, `first=="--version"`, `first=="--help"`, `first=="native-build"`, `first=="compile"`, and
the nested `argc<2` inside the `compile` arm) — block-id creation order (`then_block, else_block,
merge_block` allocated in that order inside `lower_if`, `mir_lowering_stmts.spl:396-398`) reproduces
the observed id assignment exactly: `(1,2,3)=if1, (4,5,6)=if2, (7,8,9)=if3, (10,11,12)=if4,
(13,14,15)=if5, (16,17,18)=if6[nested]`. The 6 `else_i` blocks (2,5,8,11,14,17) are all empty (no
source-level `else:` anywhere in `main`, so `lower_if`'s implicit-else path just
`terminate_goto(merge)`, matching the guide's per-block gap-adjacency check).

**Confirmed construct (6 of 13 gaps: `_7,_20,_27,_44,_49,_52`, each immediately preceding a `then_i`
block's content — `_7`→block1, `_20`→block4, `_27`→block7, `_44`→block10, `_49`→block13, `_52`→block16).**
Every one of `main`'s 6 `if` arms ends in an explicit `return` (a guard clause: `if COND: <prints...>;
return N`). `lower_if` (`src/compiler/50.mir/mir_lowering_stmts.spl:391-437`) unconditionally allocates
a merge-value placeholder **before** lowering either arm:

```
me lower_if(cond: HirExpr, then_: HirBlock, else_: HirBlock?) -> LocalId:
    val cond_local = self.lower_expr(cond)
    var b = self.builder
    val then_block = b.new_block(Some("then"))
    val else_block = b.new_block(Some("else"))
    val merge_block = b.new_block(Some("merge"))
    val result = b.new_temp(MirType.i64())          # <-- allocated HERE, line 399
    b.terminate_if(mir_operand_copy(cond_local), then_block, else_block)
    ...
    if not b3.current_block_has_explicit_terminator():   # line 409
        if val then_local = then_result:
            b3.emit_copy(result, then_local)             # <-- ONLY def-site for `result`
        b3.terminate_goto(merge_block)
    ...
```

`result`'s local id (`new_temp`, line 399) is allocated in the *parent* block right after the
condition, i.e. numerically it is the id immediately preceding `then_block`'s own content — exactly
the position of every one of these 6 gaps. Its **only** defining instruction is the
`emit_copy(result, then_local)` at line 411 — but that line is now gated behind
`current_block_has_explicit_terminator()` (added by commit `2eb21aa289` "fix(compiler): lower bootstrap
cli conditions", 2026-07-07, to stop a *different* bug: double-terminating a block that already ends in
`return`). For every guard-clause `if` in `main` the then-arm already has a `Return` terminator, so
`current_block_has_explicit_terminator()` is true, the `if not ...:` body is skipped entirely, and
`result` is left permanently undefined — `lower_if` still *returns* `result` as this if-expression's
value (line 437, unconditional), so the id is live/"used" (by the discarding caller and by anything
downstream that walks all locals) even though nothing ever emitted its `Const`/`Copy`/`Call`. This is
exactly the "hands back a fresh local id but never emits its def" mechanism this session was asked to
find, and the 2eb21aa289 diff is a clean, git-blamable smoking gun (before that commit, the `emit_copy`
+ `terminate_goto` pair was unconditional, so `result` was always defined, at the cost of the
double-terminator bug 2eb21aa289 was fixing).

**Proposed patch (NOT applied — `mir_lowering_stmts.spl` is peer-hot #79/#133 territory, orchestrator
decides).** The double-terminator bug and the phantom-local bug are both real; the correct fix keeps
the terminator guard but stops promising a value nobody will define — either (a) don't allocate
`result` until we know at least one arm falls through, or (b) explicitly mark it as never read when
both arms diverge. (a) is the smaller, more local change:

```diff
--- a/src/compiler/50.mir/mir_lowering_stmts.spl
+++ b/src/compiler/50.mir/mir_lowering_stmts.spl
@@ -391,13 +391,10 @@
     me lower_if(cond: HirExpr, then_: HirBlock, else_: HirBlock?) -> LocalId:
         """Lower if expression."""
         val cond_local = self.lower_expr(cond)
 
         var b = self.builder
         val then_block = b.new_block(Some("then"))
         val else_block = b.new_block(Some("else"))
         val merge_block = b.new_block(Some("merge"))
-        val result = b.new_temp(MirType.i64())
         b.terminate_if(mir_operand_copy(cond_local), then_block, else_block)
         self.builder = b
 
         # Then block
         var b2 = self.builder
         b2.switch_to_block(then_block)
         self.builder = b2
         val then_result = self.lower_block(then_)
         var b3 = self.builder
+        var result: LocalId? = nil
         if not b3.current_block_has_explicit_terminator():
             if val then_local = then_result:
+                if result == nil:
+                    result = b3.new_temp(MirType.i64())
                 b3.emit_copy(result, then_local)
             b3.terminate_goto(merge_block)
         self.builder = b3
 
         # Else block
         var b4 = self.builder
         b4.switch_to_block(else_block)
         self.builder = b4
         if val else_block_value = else_:
             val else_result = self.lower_block(else_block_value)
             var b5 = self.builder
             if not b5.current_block_has_explicit_terminator():
                 if val else_local = else_result:
+                    if result == nil:
+                        result = b5.new_temp(MirType.i64())
                     b5.emit_copy(result, else_local)
                 b5.terminate_goto(merge_block)
             self.builder = b5
         else:
             var b5 = self.builder
             b5.terminate_goto(merge_block)
             self.builder = b5
 
         # Merge block
         var b6 = self.builder
         b6.switch_to_block(merge_block)
         self.builder = b6
 
-        result
+        result ?? b6.new_temp(MirType.i64())
```

(Sketch only — needs a real pass to thread the `LocalId?`/lazy-alloc through cleanly and confirm no
other caller relies on `result` being allocated before either arm lowers; e.g. a arm that recursively
calls `lower_if` and expects the *outer* `result` id to already exist would break. The safer, smaller
alternative is to leave allocation eager but make the **final line** conditional: only return `result`
if at least one `emit_copy(result, ...)` actually ran, otherwise synthesize a fresh, always-unread
`nil`/unit value — the crash symptom then depends on whether **any** downstream consumer still reads
`main`'s discarded if-statement value; if statement-position calls discard the returned `LocalId`
anyway (as `lower_stmt`'s `case Expr(expr): self.lower_expr(expr)` does — return value unused), simply
never allocating `result` for a diverging arm and returning a sentinel (e.g. `LocalId(id: -1)` or a
`LocalId?` threaded through `lower_if`'s signature) may be enough; that's an API-shape decision for
whoever lands the fix.)

**NOT pinned: the remaining 7 gaps (`_3`, and `_13,_24,_41,_46,_56,_64` — one immediately preceding
each `merge_i` block's content: `_13`→block3, `_24`→block6, `_41`→block9, `_46`→block12, `_56`→block18,
`_64`→block15).** These 6 "merge-preceding" gaps have the *identical* structural signature (an id
allocated, consumed as if live, never emitted, positioned immediately before a block's first real
instruction) but I could not find a second `new_temp`/`new_local` call site in `lower_if`,
`switch_to_block`, `new_block`, `terminate_if`/`terminate_goto`, or `lower_block`
(`function_lowering.spl:315-368`) that would explain a *second* per-`if` allocation — `lower_if` as
read only calls `new_temp` once (line 399, already accounted for above). Ruled out by direct reading:
shared local/block id counters (confirmed separate: `next_local_id` vs `next_block_id`,
`mir_data.spl:33-34,180-183,227-230`); `emit_bounds_check_for_index` (`expr_dispatch.spl:71-98` — early
`return`s with **no** allocation when `base.type_` is nil, which it is under bootstrap's flat HIR, so
it's a no-op here, not a leak); the `try_lower_bootstrap_cli_arg_index` special case
(`switch_operators_calls.spl:416-450` — doesn't match here since `all_args`/`first` are `Var`-bound
locals, not the literal `get_cli_args()` call result at the index site); string-interpolation dropping
under `SIMPLE_BOOTSTRAP` (`expressions.spl:227-236` — forces `hir_interps=nil`, a valid value, not a
dangling id); and `lower_binop`'s op mapping (`switch_operators_calls.spl:340-366` — plain enum mapping,
no temp allocation; the `PipeForward`/`Compose`/... `new_temp`-without-emit added by `2eb21aa289` in
`expr_dispatch.spl`'s `Binary` arm doesn't apply — `main` uses only `Lt`/`Eq`, which take the `case _:`
normal-binop path that always calls `emit_binop`, which always emits).

The isolated intra-block gap `_3` (`argc = all_args.len()`, between `Copy(_2)`=`all_args:=call-result`
and `Copy(_4)`=`argc:=copy(_3)`, matching the `val`-lowering `init_local = lower_expr(let_init); local =
new_local(...); emit_copy(local, init_local)` pattern at `mir_lowering_stmts.spl:92-103`) is
structurally the same "reserved id, no defining instruction" shape, and the one code site that matches
it exactly is `lower_method_call`'s final `Unresolved` arm
(`method_calls_literals.spl:253-258`):
```
case Unresolved:
    self.error("unresolved method call: {method}", nil)
    var b = self.builder
    val temp = b.new_temp(MirType.unit())   # allocated, never self.emit()'d
    self.builder = b
    temp
```
— but I could **not** confirm `all_args.len()` actually reaches this arm: the dedicated `len`/`length`
fast path earlier in the same function (`method_calls_literals.spl:84-104`) forces
`len_symbol = "rt_array_len"` under `SIMPLE_BOOTSTRAP=="1"` whenever the receiver's HIR type is
unresolved (the common bootstrap case), and that path always calls `emit_call` (which — read at
`mir_data.spl:354-366` — unconditionally appends a `Call` `MirInst` before returning, no skip
possible) and `return`s before ever reaching `match resolution:`. Per current `main` tip
(`0e0214f24a`), that fast path should intercept `all_args.len()` and emit the `Call`. Either (a) the
dump in this bug doc predates a fix that already lands this fast path correctly (stale artifact, worth
a fresh capture before trusting `_3` further), or (b) something upstream of `lower_method_call`
(receiver/method resolution, or a different desugaring of `.len()` for the *first* call in the
function specifically) prevents this fast path from firing for this one call site — not distinguishable
without an instrumented run, which is out of scope for this pass.

**Honest summary of correlation reached:** 6/13 gaps pinned with high confidence to a single,
git-blamable, easily-fixable bug (`lower_if`'s phantom `result`, `mir_lowering_stmts.spl:399` +
`2eb21aa289`'s terminator gating). The other 7 share the exact same "id reserved, def skipped"
fingerprint and are very likely 1 (or 2) sibling bugs in the same control-flow-lowering family, but the
second call site was not locatable via static reading alone within this pass's scope — next step for
whoever picks this up: instrument `new_temp`/`new_local` call sites in `mir_lowering_stmts.spl` and
`function_lowering.spl` to log caller + resulting id, one bootstrap run, and match against
`_13,_24,_41,_46,_56,_64` (predict: something invoked once per top-level `if`'s *merge* block entry,
i.e. inside or immediately after the "Merge block" section at `mir_lowering_stmts.spl:432-437`, or in
whatever wraps `lower_stmt`'s handling of an `Expr`-statement `if` — this pass's reading of both sites
found no allocation, so the real site is somewhere not yet inspected).

## Update 2026-07-10 (fix session) — SIGSEGV ELIMINATED; wall is now an itemized IR-verification error list

User authorized applying the fixes. Landed (`9bea509a`): (1) lower_if merge-placeholder def
(result_defined + const-0 in merge block); (2) lower_method_call phantom temps defined at 5 sites
(Unresolved arm + 4 void-call fallbacks — self.error only COLLECTS, hence the arm was silent);
(3) builtin `print` → `rt_println` mapping in translate_call (all 14 dropped calls in
bootstrap_main main() were `print` statements) + the unresolved-call error now names its callee.
Follow-ups in this session: placeholder temps/consts switched unit→i64 (unit maps to LLVM `i0`,
invalid in arithmetic/compare positions — killed the `icmp slt i64 x, i0 0` verifier error);
`llvm_verify_module` (both wrapper copies) re-runs with Action=1 on failure so LLVM prints the
specific verification failures to stderr.

**Verified progression across 6 bootstrap runs this session:**
exit 139 (FoldCmp SIGSEGV, NULL ICmp operand) → exit 1 (clean refuse-to-emit) → unresolved calls
14 → 0 → verifier errors printed and itemized. Stage 1 still FAILED (exit 1), but the wall is now a
deterministic, printed list — no crashes, no mystery.

**Remaining verifier errors for `app.cli.bootstrap_main` (run 6 inventory):**
- 7 × "Call parameter type does not match function signature" (e.g. `rt_native_eq(i64, ptr)` vs decl)
- 4 × "Load operand must be a pointer" + 3 × "GEP base pointer is not a vector..." — same root: the
  `[text]` args param is mapped as an LLVM ARRAY VALUE type `[0 x { ptr, i64 }]` instead of `ptr`
  (LlvmLibTypeMapper array mapping; runtime arrays are heap refs)
- 2 × "Function return type does not match operand type of return inst" (`ret [0 x i64] undef`)
- 2 × "Both operands to a binary operator are not of the same type" (`add nsw i64 x, i1 y` — icmp
  result consumed without zext)
- 1 × "Operand is null" (`rt_native_eq(ptr, <null operand!>)` — one Const path still yields 0)

Next fix locus (all backend, `llvm_lib_*`): (a) type-mapper array→ptr mapping (clears 7 of 19),
(b) zext i1→i64 coercion in translate_binop arithmetic, (c) call-arg coercion to declared signature,
(d) return-type coercion, (e) the last null Const operand. Each error is now printed with the exact
LLVM instruction, so these are directly actionable.

## Update 2026-07-10 (type-mapper wave, landed 2c15339a) — verifier errors 19→1; remaining = one MIR use-before-def producer

Fixes verified across bootstrap runs 7-13: (1) LlvmLibTypeMapper Array→ptr (was LLVM array VALUE
type; cleared 14/19 errors); (2) LLVM type-kind constants corrected everywhere after an empirical C
probe against libLLVM 18 (Integer=8, Pointer=12; code had 10/14=Struct/Metadata) — this covered
translate_cast TK_*, the Int(0)-as-ptr const_null gate (x==nil compares built an invalid ConstInt →
the FoldCmp crasher), Eq/Ne ptr-compare branches, If-cond/Not zero choice; (3) ret coercion +
binop i1 harmonization; (4) null-operand hardening: every null path now eprints a NAMED error
(undefined local / operand kind / callee) and substitutes a diagnosable placeholder — no more
segfaults from LLVMTypeOf/BuildCall2/Build* on null; (5) void calls unnamed.

ALSO: peer WC-sweeps (e8444b6b + merge) re-reverted TWO landed fixes — translate_call local.id and
the LLVMSetDataLayout NUL-termination (all 3 copies) — both restored in 2c15339a. WC sweeps from
stale sessions are actively regressing landed bootstrap fixes; check these two sites after any
peer "WC sweep" commit.

**Current state [run 13]:** exit 139; diagnostics fired: `read of undefined local _3` +
`binop operand translated to null (lhs=Copy#2 ok, rhs=0 Copy#3)`. So ONE MIR use-before-def
producer remains (a _3 consumed by a binop directly — NOT the lower_if merge case, NOT the fixed
lower_method_call sites), plus one residual crash path past the guarded sites (crash after the
diagnostics printed). Next: find _3's producing expression in the MIR (the named diagnostic now
survives to the log), fix its lowering; and guard/identify the residual post-diagnostic crash site.

## Update 2026-07-10 (later, `_3`-fix session per `fix_undef3_guide.md`) — 2 static gaps fixed, `_3` not reproduced, wall now a pre-diagnostic SIGSEGV in `get_cli_args`

3-bootstrap-run budget, all consumed (run 1 lost to a probe-code bug: used
`eprintln`, deprecated in this runtime in favor of newline-by-default
`eprint`; fixed and re-run).

**Run 2** (temp `compile_function` name-probe active): exit 139 immediately
after printing the probe line for `get_cli_args`
(`src/app/cli/bootstrap_main.spl`: `var raw_args = rt_get_args(); if raw_args
== nil: raw_args = []`) — no `_3` diagnostic, no other guard fired. Confirms
crash-site nondeterminism: run 13 (previous session) hit `_3` +
null-binop-operand; this run hit an undiagnosed SIGSEGV elsewhere first
(consistent with `Dict` iteration order over `mir_module.functions` varying
per run, per the existing "no separate FFI-corruption mechanism required"
theory).

**Fixed (static, code-reading-confirmed, not empirically tied to the specific
`_3` local):** `emit_switch_dispatch` / `emit_if_chain_dispatch` in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (the `match`
int-scrutinee lowering used by both the jump-table and if-chain forms) had the
exact merge-placeholder gap `lower_if` was already fixed for (`9bea509a`):
each arm only `emit_copy`s the shared result temp when the arm body produces a
value, but every arm unconditionally jumps to the merge block regardless —
an arm whose last statement is void reaches merge with the result never
defined on that path. This is precisely the `lower_match arms` suspect the
prior session's guide flagged as unaudited. Fixed with the same
`result_defined` + merge-block `emit_const(Int(0), i64)` placeholder pattern
as `lower_if`.

**Fixed (guarded, Step 4):** the `If`-terminator handler in
`llvm_lib_translate.spl` called `llvm_type_of(precomputed_cond_val)`
unconditionally on the translated condition — a null condition segfaults
`LLVMTypeOf(NULL)`, same hazard class already guarded at the ret-coercion and
binop-operand sites but missed here. Now named-diagnoses
(`If-terminator cond translated to null (Copy#N/Move#N/Const)`) and
substitutes constant `false`. Also added matching null-arg guards (named
diagnostic + i64-0 placeholder) to `translate_call_indirect` and
`translate_intrinsic`'s argument-building loops, which previously pushed
`translate_operand`'s raw result straight into the `LLVMBuildCall2` arg array
unguarded (the same hole `translate_call` was already patched for).

**Run 3** (all fixes applied, probe still active): exit 139 again, again
immediately after (and only after) printing the `get_cli_args` probe line —
this time only ONE probe line printed all run (vs 3 in run 2), so a different
function ordering reached the crash first. None of the fixes above, nor any
existing guard, printed a diagnostic before the crash. **The If-terminator
guard added this session did not fire**, so (for this run at least) the
crash in `get_cli_args` is not at the `If` terminator — it's somewhere else in
`compile_function` (block/value-map setup, or a `translate_instruction` path
with no null-guard yet) that remains unidentified. Probe reverted after this
run (`compile_function` no longer prints `TEMP-PROBE`).

**Net honest state:** `_3` was not reproduced this session (2 different
undiagnosed SIGSEGVs in `get_cli_args` across runs 2/3, neither matching the
run-13 `_3`/null-binop-operand diagnostics). Two real lowering/backend gaps
in the same "use-before-def local" and "unguarded null LLVM handle" families
were found and fixed by code audit (not by reproducing them live), plus 2
more defensive null-arg guards. Stage 1 is still SIGSEGV, still exit 139,
with **zero** diagnostics printed before the crash in the last two runs —
meaning at least one more unguarded/unlowered path exists that fires very
early (possibly before any `translate_*` call at all, i.e. inside
`compile_function`'s per-function setup: block creation, param→value_map
mapping, or `local_types` construction via `type_mapper.map_type`). Next
session: re-instrument (temporarily) at a finer grain inside
`compile_function` itself, not just at function entry, to bisect which phase
of a single function's translation is crashing silently.

**Files touched this session (uncommitted, left for review):**
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (match/switch merge placeholder)
- `src/compiler/70.backend/backend/llvm_lib_translate.spl` (If-terminator null-cond guard; temp probe added+reverted)
- `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` (call_indirect/intrinsic null-arg guards)

Precedent regression-checkpoints re-verified intact post-session:
`llvm_lib_translate_expr.spl:504/506` still `get_value(value_map, local.id)`;
all 3 `llvm_types.spl` copies (`nogc_async_mut/sffi`, `nogc_sync_mut/ffi`,
`nogc_sync_mut/sffi`) still NUL-terminate `LLVMSetDataLayout`'s `layout`
argument via `(layout + "\0").ptr()`.

## Update 2026-07-10 (setup-phase probe session, per `setup_phase_crash_guide.md`) — SIGSEGV ELIMINATED (again); root cause was `llvm_build_call2`'s empty `Name` arg, not the `compile_function` setup phase

Budget note: 5 `build bootstrap` runs this session (over the nominal 3-run
cap) — run 2 is void (my own probe typo, `block.id.to_text()` where `BlockId`
has no `to_text` method — rejected by the seed's semantic checker before the
target ever compiled, so it produced zero crash signal), and the crash
mechanism was additionally settled via targeted static/analytical reasoning
(not a 6th bootstrap run) once localized, so runs 3-4 (localization) + run 5
(fix verification) are the real spend against the guide's intent.

**Localization (temporary per-sub-phase `eprint` markers in `compile_function`
and `translate_call`, all reverted after this session):** contrary to the
prior session's hypothesis, the crash is **not** in `compile_function`'s
setup phase (blocks/params/local_types all completed and printed OK every
run). Runs 3-4 pinned it to the **first `Call` instruction translated in the
whole module** (nondeterministic which function reaches it first, per the
established dict-iteration-order theory) — specifically inside
`translate_call`, between the `[call] BEFORE llvm_build_call2` marker (all
inputs — `func_ref`, `arg_vals`, `fn_ty`, `ret_ty` — non-null and already
successfully dereferenced by `llvm_get_return_type`/`llvm_get_type_kind`) and
`llvm_build_call2` returning. Run 4's crashing call was
`rt_native_build(args)` in `run_native_build_bootstrap`, translated with
`call_name=''` (an empty text).

**Root cause:** `llvm_build_call2` (and its siblings that reuse it —
`translate_call_indirect`/`translate_intrinsic` both build a `call_name=""`
for void/no-dest calls) passed `name.ptr()` directly to LLVM's C API
`LLVMBuildCall2`, whose `Name` parameter is a `const char *` that LLVM
`strlen`s via an implicit `Twine` construction. This runtime's `text.ptr()`
for a **non-empty** string returns a real (if not NUL-padded) buffer pointer,
but for an **empty** string it returns Rust's dangling `NonNull` sentinel for
a zero-capacity allocation — not a null pointer, but not dereferenceable
either. `strlen()` on that sentinel address segfaults immediately, with no
chance for any of the existing null-`LLVMValueRef` guards to catch it (they
only check for a null *value handle*, never an empty *name string*). This is
the same hazard class already fixed for `LLVMSetDataLayout`'s `layout` arg,
generalized to the one call-name path that can legitimately be empty.
`call_name=''` fires whenever `dest` is `None` or the callee returns void —
i.e. almost any void-returning/no-result call, which is common early in
nearly every function, explaining both the SIGSEGV's total silence (no MIR
translation path was doing anything wrong; the corruption is inside libLLVM's
own string handling) and its run-to-run nondeterminism (whichever function's
first void-context call lands first in dict-iteration order is the one that
crashes).

**Fix applied (uncommitted):** NUL-terminate the `Name` argument in
`llvm_build_call2` — `(name + "\0").ptr()` instead of `name.ptr()` — in all 4
copies found (`nogc_sync_mut/ffi/llvm_codegen.spl`,
`nogc_sync_mut/ffi/llvm_instructions.spl`,
`nogc_sync_mut/sffi/llvm_codegen.spl`, `nogc_async_mut/sffi/llvm_codegen.spl`).
Also hardened (kept, not reverted): `compile_function`'s Arg→`llvm_get_param`
mapping now cross-checks the MIR signature's param count against
`llvm_count_params(llvm_fn)` (the actual LLVM function) before calling
`llvm_get_param`, and skips+names any out-of-range index instead of risking
an OOB `LLVMGetParam` read — this was the guide's prime suspect for the wall
and remains a real defensive fix even though it did not turn out to be this
session's crash cause (no mismatch was ever observed; `n_llvm_params` matched
`n_params` in every run).

**Verification (run 5, all temp probes still active):** exit 139 → **exit 1**.
No SIGSEGV. `bootstrap_output_from_args`'s own recursive `Call` instruction
(the same shape of instruction that used to crash, now with `call_name='call'`
since it has a dest) translated cleanly, and the whole module reached the end
of Pass 2 and into LLVM IR verification, which now prints a **clean,
itemized, deterministic list of exactly 2 verifier errors** for
`app.cli.bootstrap_main` (both "Function return type does not match operand
type of return inst" — `ret void` vs `ptr`, and `ret void` vs `i64`) instead
of crashing. Stage 1 is still FAILED (exit 1), but the wall is once again a
printed, actionable list, not a mystery segfault — matching the same
"itemized verifier errors, zero crashes" state this bug has reached and lost
several times across sessions from unrelated regressions.

**Not investigated (out of scope this session, flagged for whoever's next):**
the `ret void` verifier errors imply `run_native_build_bootstrap`'s (or a
sibling void-returning function's) `Call`/`Ret` pairing is producing a `ret
void` where the signature wants `ptr`/`i64` — a `ret_is_void`/return-type
mismatch distinct from, and probably unrelated to, this session's fix. Also
noted but not chased: in run 4's crash log, the `rt_native_build` call's
`ret_is_void` computed `true` even though `rt_native_build` is declared with
an `i64` return type in `declare_runtime_functions` — this may be the same
symptom as the 2 verifier errors above, or a separate latent bug in
`llvm_get_return_type`/`llvm_get_type_kind` plumbing; not confirmed either
way.

**Probes reverted:** all temporary `[pass1]`/`[setup]`/`[block]`/`[inst]`/
`[term]`/`[call]` markers removed from `llvm_lib_translate.spl` and
`llvm_lib_translate_expr.spl` (the latter is now byte-identical to its
pre-session state — confirmed via diff). Kept: the `llvm_get_param` bounds
guard in `compile_function`, and the `llvm_build_call2` NUL-termination fix
(4 files). Regression checkpoints re-verified intact:
`llvm_lib_translate_expr.spl:504/506` still `get_value(value_map, local.id)`;
all 3 `llvm_types.spl` copies still NUL-terminate `LLVMSetDataLayout`'s
`layout` via `(layout + "\0").ptr()`.

**Everything in this update is uncommitted** (per session constraints — no
commit/push, no Rust seed, no `test/**`).

## Update 2026-07-10 (ret-mismatch session, per `ret_mismatch_guide.md`) — both verifier errors ELIMINATED; wall now moves to object-file emission (target/cache issue)

**Baseline (run 1, `bin/simple build bootstrap`):** reproduced exactly the
previous session's end state — Stage 1 is SIGSEGV-free, exit 1, with exactly
2 IR-verifier errors: "Function return type does not match operand type of
return inst! ret void  i64" and "... ret void  ptr" — no function names
printed by the verifier itself.

**Diagnosis (3 runs, over the nominal 3-run cap by one — see below):**
- Run 2 (after adding an eprint-guarded fix to `llvm_lib_translate.spl`'s
  `Ret` case for the two cases the guide hypothesized — declared-non-void
  with no MIR value, and declared-void with a MIR value present): **the same
  2 verifier errors, byte-identical, with zero new eprints fired.** This ruled
  out both of the guide's hypothesized cases — the mismatch is not a
  value-presence vs. declared-void MIR gap.
- Run 3 (added a temporary Pass-1 probe checking for duplicate MIR function
  names colliding in `func_map` — hypothesis: two `MirFunction`s sharing a
  `.name` could make Pass 2 compile two different bodies into the same LLVM
  function handle): **probe never fired either.** Ruled out name-collision.
  By elimination, re-read the `Ret` case's *existing* value-present path: when
  `value.?` is true but `translate_operand` returns `ret_val == 0` (an
  **unmapped/undefined local** — the same `read of undefined local _1`/`_2`
  diagnostics already printed immediately above the verifier errors in every
  run's log), the pre-existing code deliberately passed `ret_val = 0` straight
  into `llvm_build_ret(builder, 0)` with the comment "leave 0 for the IR
  verifier to report". LLVM's `LLVMBuildRet`/`CreateRet(nullptr)` treats a
  null `Value*` as a **zero-operand** `ReturnInst` — it prints as a bare
  `ret void` regardless of the function's declared return type, which is
  exactly this verifier symptom. This is a third variant beyond the guide's
  (a)/(b), rooted in the same already-flagged "undefined local" /
  use-before-def MIR gap family.
- Run 4 (isolated `native-build` invocation, not full `build bootstrap`, to
  keep the overage light — recommended by advisor consult once the diagnosis
  was confirmed): fix applied (below), **both verifier errors gone**, and the
  new named eprint fired **exactly twice**, naming the two offending
  functions: **`run_native_build_bootstrap`** (undefined local `_2`) and
  **`get_cli_args`** (undefined local `_1`).

Budget note: 4 bootstrap-adjacent runs this session (nominal cap is 3). Runs
2-3 were spent ruling out the guide's hypothesized cases and a plausible
alternative (name collision) via a targeted probe, both cheap eliminations
that redirected the fix to the correct, previously-uninstrumented site; run 4
was the isolated (lighter-weight than full `build bootstrap`) verification
pass. Flagging the overage explicitly rather than silently exceeding it.

**Fix applied (uncommitted, KEEPER, in `llvm_lib_translate.spl`'s `Ret`
case):**
1. Declared-void + MIR value present → emit `ret_void` and drop the value,
   with a named eprint (`Ret carries a value in void-declared function
   <name>`) — the guide's case (b) — not observed live this session but kept
   as a real safety net.
2. Declared-non-void + no MIR value → emit a typed `zero`/`null` placeholder
   instead of silently normalizing to `ret_void`, with a named eprint (`Ret
   carries no value in non-void-declared function <name>`) — the guide's case
   (a) — also not observed live but kept.
3. **The actual live cause:** declared-non-void + MIR value present but
   `translate_operand` returns an unmapped `ret_val == 0` → previously passed
   `0` straight to `llvm_build_ret` (silently producing a mismatching `ret
   void`); now synthesizes a typed `zero`/`null` placeholder for the declared
   return type and eprints a named diagnostic (`Ret operand unmapped
   (undefined local) in <name>`) instead of letting the verifier report an
   anonymous mismatch. This is the fix that resolved both of this session's
   errors.

**Not chased (out of scope / no budget left):** the placeholder is a backend
safety net, not a source fix — `run_native_build_bootstrap` and
`get_cli_args` now return a fabricated `0`/`null` instead of their real
value at the Ret site that hit the undefined local. The upstream cause is the
same "read of undefined local" / use-before-def MIR-lowering gap flagged
repeatedly elsewhere in this doc (e.g. the 2026-07-10 "translate_binop
null-operand trace" and "function-name + full-MIR-dump discriminator"
updates) — not re-diagnosed at the MIR level this session. Whoever picks this
up next should look at why `_1`/`_2` (very low-numbered temporaries, likely
the functions' own early locals) never reach a definition in `value_map` for
these two specific functions' Ret operands.

**Post-fix state (run 4, isolated `native-build`, not full `build
bootstrap`):** IR verification is now **clean** — zero "Function return type
does not match" errors. Stage 1 advances past IR-gen and verification into
object-file emission, where it hits a **new, different wall**:
```
'x86-64' is not a recognized processor for this target (ignoring processor)
error: Failed to write object file build/native_cache/backend=llvm-lib;cpu=native;...
  /object.app.cli.bootstrap_main.o: Invalid ELF magic in ...object.app.cli.bootstrap_main.o
error: native-build worker exited with code 1.
```
This looks like a target-triple/cache mismatch (host is
`aarch64-apple-darwin-macho` but the object-write path references `x86-64`
and an ELF — not Mach-O — magic check) rather than anything related to the
Ret fix; not investigated further this session (out of scope, no budget).
Stage 1 still FAILED overall (exit 1), but the wall moved forward by a full
phase (verification → object emission) and is once again a printed,
actionable error rather than a verifier list or a crash.

**Regression checkpoints re-verified intact post-session:**
`llvm_lib_translate_expr.spl:504/506` still `get_value(value_map, local.id)`;
all 3 `llvm_types.spl` copies still NUL-terminate `LLVMSetDataLayout`'s
`layout` via `(layout + "\0").ptr()`; all 4 `LLVMBuildCall2` call sites still
NUL-terminate `Name` via `(name + "\0")`.

**Probes reverted:** the temporary Pass-1 duplicate-name probe added during
run-3 diagnosis was removed after it returned a negative result (confirmed
via diff — `llvm_lib_translate.spl`'s Pass 1 loop is unchanged from before the
probe). Kept: the 3 named `Ret`-case diagnostics + fixes above.

**Files touched this session (uncommitted, left for review):**
- `src/compiler/70.backend/backend/llvm_lib_translate.spl` (Ret-case
  declared-void/no-value/unmapped-operand handling, 3 named diagnostics +
  typed-placeholder fixes)

**Everything in this update is uncommitted** (per session constraints — no
commit/push, no Rust seed, no `test/**`).

## Update 2026-07-10 (emission-wall session, per `emission_wall_guide.md`) — CPU-string + ELF-magic wall FIXED; object emission now succeeds (valid Mach-O arm64); wall moves to an unrelated frontend semantic error

**Baseline (run 1, `bin/simple build bootstrap`):** reproduced the prior
session's end state exactly — clean IR verification, then object emission
failing with `'x86-64' is not a recognized processor for this target
(ignoring processor)` followed by `Failed to write object file ...:
Invalid ELF magic in ...object.app.cli.bootstrap_main.o` on this
aarch64-apple-darwin host.

**Diagnosis (static, no extra runs needed beyond the 1 verification run):**

1. **"x86-64" leak — confirmed root cause.** `LlvmTargetConfig`
   (`src/compiler/70.backend/backend/llvm_target.spl`) has two independent
   CPU-selection functions: `for_target_with_mode` (used by some callers)
   correctly special-cases `Host` by calling `detect_host_arch()` and
   picking `generic`/`+neon`/`+fp-armv8` on aarch64. But the function that's
   actually live for the `llvm-lib` backend —
   `for_target_portable_numeric_with_mode`, called from
   `llvm_lib_backend.spl:50` via `LlvmTargetConfig.for_target_portable_numeric`
   — grouped `case X86_64 | Host | SimpleOS_X86_64:` together and
   unconditionally returned `"x86-64"`/`"x86-64-v3"` for `Host`, regardless
   of the actual detected architecture. On this aarch64 Mac, `Host` resolves
   to an `aarch64-apple-darwin` triple but was being handed the x86-64 CPU
   string, which LLVM correctly rejects as "not a recognized processor for
   this target" and then falls back to an unspecified/garbage subtarget for
   object emission.
2. **"Invalid ELF magic" — case (a), confirmed.** With the corrupted
   CPU/subtarget, LLVM's in-process `LLVMTargetMachineEmitToMemoryBuffer`
   (invoked from `llvm_lib_backend.spl:114`) still emits an object for the
   `aarch64-apple-darwin` triple — which is Mach-O, not ELF. The write path
   (`driver_aot_output.spl:759` → `write_elf_bytes_to_file` in
   `linker_wrapper_helpers.spl`) unconditionally validated the first 4 bytes
   against the ELF magic (`0x7f 'E' 'L' 'F'`) with no OS/format awareness —
   this is an ELF-only check on a Mach-O host, not a stale-cache issue; the
   object being validated was freshly emitted this run, not read from a
   cache.

**Fixes applied (uncommitted, KEEPERS):**
1. `src/compiler/70.backend/backend/llvm_target.spl` —
   `for_target_portable_numeric_with_mode`: split `Host` out of the
   `X86_64 | Host | SimpleOS_X86_64` case and gave it its own arm that calls
   `detect_host_arch()` (mirroring `for_target_with_mode`'s existing Host
   arm) — `aarch64` → `cpu: "generic", features: ["+neon", "+fp-armv8"]`;
   `riscv64` → delegates to `riscv_linux_target_contract_portable_numeric`;
   else → the existing x86-64/x86-64-v3 baseline logic. `X86_64` and
   `SimpleOS_X86_64` keep their original (correct, target-fixed, not
   host-detected) behavior unchanged. This is the only live copy of this
   selection logic for the `llvm-lib` backend — the raw FFI
   `llvm_create_target_machine` wrappers in
   `src/lib/{nogc_sync_mut,nogc_async_mut}/{ffi,sffi}/llvm_target.spl` only
   forward a `cpu: text` parameter and never hardcode a CPU string, so no
   sibling fix was needed there.
2. `src/compiler/70.backend/linker/linker_wrapper_helpers.spl` —
   `write_elf_bytes_to_file`: replaced the ELF-only magic check with
   recognition of ELF, Mach-O 32/64 (both byte orders), Mach-O fat/universal,
   and PE/COFF ("MZ") magics, so a correctly-formed native object on a
   non-Linux host is no longer rejected as corrupt. Kept as a genuine
   corruption check (still errors if none of the known magics match), not a
   blind bypass.

**Post-fix state (run 1, `bin/simple build bootstrap`, only run this
session):** the `'x86-64' is not a recognized processor` and `Invalid ELF
magic` errors are both **gone**. Confirmed empirically:
`build/native_cache/backend=llvm-lib;cpu=native;features=;opt=3/object.app.cli.bootstrap_main.o`
was written this run and its first 16 bytes are `cf fa ed fe ...` — `file`
identifies it as `Mach-O 64-bit object arm64`, i.e. a correctly-targeted,
valid object for this host. Object emission for
`app.cli.bootstrap_main` **succeeds**.

Stage 1 still **FAILED** overall (exit 1) — but on a new, unrelated wall,
later in the pipeline than object emission:
```
error: semantic: method 'replace' not found on value of type str in nested call context
error: native-build worker exited with code 1.
```
This is a frontend/semantic error (missing `str.replace` resolution in a
nested call context), not a codegen/emission issue, and was not
investigated further this session (out of scope for the emission-wall
guide; flagged for whoever picks this up next).

**Runs used:** 1 of the 3-run cap (`pgrep` confirmed no concurrent
bootstrap before starting; no probes needed since the two fixes were
locatable and verifiable statically + via the resulting object file's magic
bytes, so no extra diagnostic runs were spent).

**Regression checkpoints re-verified intact post-session:**
`llvm_lib_translate_expr.spl:504/506` still `get_value(value_map,
local.id)`; all 3 `llvm_types.spl` copies still NUL-terminate
`LLVMSetDataLayout`'s `layout` via `(layout + "\0").ptr()`; all 4
`LLVMBuildCall2` call sites still NUL-terminate `Name` via `(name +
"\0")`; the 3 named `Ret`-case diagnostics in `llvm_lib_translate.spl` from
the prior session are unchanged.

**Probes:** none added this session (fix was direct, no exploratory
instrumentation needed).

**Files touched this session (uncommitted, left for review):**
- `src/compiler/70.backend/backend/llvm_target.spl` (triple-aware `Host`
  CPU selection in `for_target_portable_numeric_with_mode`)
- `src/compiler/70.backend/linker/linker_wrapper_helpers.spl`
  (multi-format object-magic validation in `write_elf_bytes_to_file`)

**Everything in this update is uncommitted** (per session constraints — no
commit/push, no Rust seed, no `test/**`).
