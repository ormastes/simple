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
