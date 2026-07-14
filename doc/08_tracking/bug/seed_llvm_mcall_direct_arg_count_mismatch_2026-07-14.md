# Bootstrap-seed LLVM backend: `mcall_direct` emits wrong argument count → whole-compiler LLVM build fails verification

Found by Lane INGUEST-RUN while attempting an LLVM-clean rebuild of the
SimpleOS Simple toolchain (the redeploy path that would dodge the cranelift
enum miscompile). This is the concrete reason the **LLVM** seed backend cannot
build the compiler — so, together with the cranelift enum bug, **both** seed
backends are defective and the #99 redeploy is blocked on fixing at least one.

## Symptom

Building the compiler with the bootstrap seed's LLVM backend
(`src/compiler_rust/target/bootstrap/simple`, which has `--features llvm`)
fails at LLVM IR verification, systemically, in many modules:

```
llvm codegen: semantic: LLVM verification failed:
  Incorrect number of arguments passed to called function!
  %mcall_direct = call i64 @str.substring(i64 %v103311, i64 %v108312)
  Incorrect number of arguments passed to called function!
  %mcall_direct = call i64 @compiler_rust__lib__std__src__core__list__List_dot_join(i64 %a, i64 %b)
  ...
```

Affected call sites span the whole tree: `str.substring`, `List.join`,
`SdnValue.int`/`SdnValue.float`, `BorrowChecker.convert_place/convert_terminator`,
`CompilerContextImpl.check_types`, `Formatter.*` (fix_array_commas,
break_method_chain[4 args], break_at_operators[4 args], …), `TracingAspect.before/after`,
`LeanBackend.*`, `MirToLua.*`, `VulkanBackend.*`, `SpirvBuilder.id_str`, etc.

## Root cause (LLVM direct method-call lowering)

The `mcall_direct` path — the LLVM backend's DIRECT (statically-resolved)
method-call lowering — emits a `call` whose argument count does not match the
callee function's declared LLVM signature. The mismatch is consistent with the
receiver/`self` (or a trailing arg) being dropped or double-counted at the call
site vs the definition:

- `str.substring(start, end)` on a receiver should lower to `substring(self,
  start, end)` (3 args); the call emits 2.
- `SdnValue.float()` (no-arg method) emits 1 arg against a signature that
  expects a different count.
- `Formatter.break_method_chain(a,b,c)` emits 4; `TracingAspect.before(x,y)`
  emits 3 — i.e. the arity skew is not a fixed ±1, it tracks a per-method
  self/arg accounting error in `mcall_direct`.

LLVM's verifier rejects the module, so no object is produced — the compiler
cannot self-build via LLVM at all.

## Why it matters (the redeploy wall, precisely)

The #99 redeploy needs an LLVM-clean whole-compiler build (the cranelift seed
miscompiles enum single-payload extraction → the guest interpreter traps
`field access on nil receiver`, proven in-guest by Lane INGUEST-RUN). But the
LLVM path fails here. So the redeploy is blocked on fixing **one of two** seed
backend bugs:
1. cranelift: enum/tag-box payload miscompile (this file's sibling;
   `x64_freestanding_*` family + the deployed-binary interp trap).
2. LLVM: this `mcall_direct` argument-count mismatch.

Fixing (2) is likely the shorter path to a clean redeploy, since the LLVM
backend is otherwise the "good" path (no enum miscompile).

## Fix

In the LLVM backend's direct method-call lowering (`mcall_direct` — search
`src/compiler/70.backend/backend/` LLVM IR builder / method-call emit), make the
emitted argument list match the callee's declared parameter list exactly:
prepend the receiver as the first argument iff the callee signature includes
`self`, and don't drop/duplicate trailing args. Add an assertion at emit time
that `len(call_args) == len(callee_param_types)` so a future skew fails loudly at
codegen rather than at LLVM verify.

## Verification handle

`src/compiler_rust/target/bootstrap/simple` building any module that calls
`str.substring` (e.g. `src/lib/nogc_sync_mut/path.spl`) with the LLVM backend:
must pass LLVM verification (currently fails). Evidence:
`scratchpad/inguest_run_recover/llvm_build_errors_summary.txt`,
`llvm_failing_callees.txt`.

## Context: in-guest RUN is otherwise REACHABLE

This bug does NOT block a plain in-guest run: `/usr/bin/simple --version` runs
in-guest on SimpleOS x86_64 under real OVMF (ring-3 `cs=0x2b`, prints
`Simple v1.0.0-beta`, `rc=0`) — loader, ring-3 transition, syscalls, and FAT32
I/O all work. Only self-interpretation of arbitrary programs hits the
cranelift enum trap; only the LLVM rebuild hits this `mcall_direct` bug.
