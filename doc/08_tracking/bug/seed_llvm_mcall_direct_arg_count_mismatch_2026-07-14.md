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

## RESOLVED in the pure-Simple backend (2026-07-14)

Fixed where it matters for the deployed compiler: the **pure-Simple** LLVM IR
backend (`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`,
`translate_call`). It emitted exactly `args.len()` arguments against a
signature-derived `declare` with **no arity-reconciliation guard** (unlike the
Rust `compile_call`, which already handled this via an indirect call). Added the
same reconciliation in IR-text form: when the callee's declared parameter count
(`lookup_function_param_count`) differs from the call's argument count, emit an
EXPLICIT function-type signature — `call RET (argtys) @f(args)` — which keeps the
call well-formed for llc (the callee is treated as a typed pointer). Engages only
on a KNOWN mismatch, so matching calls are byte-identical to before.

Regression test: `test/01_unit/compiler/backend/llvm_call_arity_reconcile_spec.spl`
(2/2 under the seed) — a 2-arg call to a 3-param callee emits the explicit
`(i64, i64)` signature; a 3-arg call to the same callee stays a bare call. No
regression in the existing LLVM backend specs.

### Temporary Rust seed repair (2026-07-17)

The pure llc/text path cannot yet bootstrap end to end: Stage 2 cross-target
dispatch and Stage 3 `rt_native_build` re-enter the Rust seed, while the
Cranelift seed has separate enum/payload corruption. The smallest bootstrap
repair therefore makes `mcall_direct` use the same typed-indirect arity
reconciliation already used by sibling LLVM call paths. Matching calls remain
direct. The focused LLVM verifier regression
`method_call_static_arity_mismatch_uses_typed_indirect_call` passes.

## Fresh bootstrap evidence (2026-07-17)

A clean, cgroup-capped bootstrap from pushed `main` rebuilt the Rust seed and
runtime successfully, then failed Stage 2 with this same seed-only LLVM defect:
43 files failed verification, led by `str.substring` calls with two arguments
against three-argument declarations. The retained evidence is
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`; no
Stage 2 binary was produced. The bootstrap exited 2 normally, without timeout,
OOM, crash, or orphaned child.

After the temporary seed repair, the same bounded Stage 2 run reported zero
argument-count verifier errors (down from the systemic 43-file failure). Stage
2 now stops later on 19 files with 38 undeclared-global diagnostics; that is a
separate symbol-lowering bug, led by `char_to_ascii`, `self`, `Shared`, and
generic symbols. No pure compiler or deployment was produced.

## Context: in-guest RUN is otherwise REACHABLE

This bug does NOT block a plain in-guest run: `/usr/bin/simple --version` runs
in-guest on SimpleOS x86_64 under real OVMF (ring-3 `cs=0x2b`, prints
`Simple v1.0.0-beta`, `rc=0`) — loader, ring-3 transition, syscalls, and FAT32
I/O all work. Only self-interpretation of arbitrary programs hits the
cranelift enum trap; only the LLVM rebuild hits this `mcall_direct` bug.
