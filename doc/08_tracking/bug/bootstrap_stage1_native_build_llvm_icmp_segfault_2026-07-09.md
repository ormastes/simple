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
