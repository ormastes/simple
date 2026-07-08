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

## Fix direction

Instrument the `LLVMBuildICmp` extern binding (or `call_extern_function_with_values` for opaque
pointer args) to log/validate the two `llvm::Value*` operands before the call; compare the pointer
values seen by the interpreter vs. what LLVM receives, to decide between (1) marshalling corruption
and (2) a genuine null operand from Simple codegen. If (1), fix the interpreter's opaque-pointer
extern marshalling; if (2), fix the Simple LLVM IR builder call site. Per `.claude/rules/bootstrap.md`,
the fix belongs in pure-Simple (the IR builder) or the interpreter FFI path, and the deployed binary
re-built — not a fall-back to the seed.
