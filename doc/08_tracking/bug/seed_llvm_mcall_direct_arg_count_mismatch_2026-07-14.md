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

A bounded follow-up tested exact-arity lazy declarations for mapped imported
function values. Its focused LLVM verifier regression covered both one- and
zero-argument imports, but the real Stage 2 result was unchanged: 19 files and
38 diagnostics. The project path resolves `char_to_ascii` as the double-prefixed
`backend__backend__common__ascii_utils__char_to_ascii`, which does not match the
discovered arity key. The ineffective code was removed. A fresh scoped session
must repair import-key normalization before retrying; unresolved locals,
generics, enum cases, and static receivers must remain fail-closed rather than
being declared as external symbols. The run exited 2 normally with no timeout,
OOM, crash, or orphan.

The next isolated fix unified regular and pattern-leading `elif` branches
through one pattern-aware HIR lowering helper. Its HIR/MIR regression first
reproduced `UnknownVariable("unwrapped")`, then passed with the binding retained
as a local. The single bounded bootstrap removed both real manifestations,
`global_local` and `receiver_mir_type_uw`; current `main` also removed the
separate `local_unsigned` leak. Stage 2 now reports 32 undeclared-global
diagnostics (down from 38), with no argument-count errors. The run exited 2
normally without timeout, OOM, crash, hang, or orphan.

LLVM now receives the existing project import-arity index and predeclares only
exact known function-valued `GlobalLoad` symbols before compiling bodies. The
focused verifier covers the canonical layered `char_to_ascii` name, a
zero-argument `cuda_available` sibling, and an unresolved `self` negative case.
The single bounded bootstrap removed all ten imported-function diagnostics,
reducing the total from 32 to 22. Unknown locals, generics, enum cases, and
static receivers remain fail-closed. The run exited 2 normally without
timeout, OOM, crash, hang, or orphan.

Import discovery now records exact arities for concrete class, struct, enum,
trait, impl, extend, and extern-class methods, including implicit receivers,
while excluding abstract/pass-only trait methods. Focused discovery coverage
passes. The single bounded bootstrap removed `Tensor.T` and `Iterator.count`,
reducing undeclared globals from 22 to 18. A newly exposed `slice` failure
remained for separate classification; unknown enum/generic/static/local symbols
remain fail-closed. The run exited 2 normally without timeout, OOM, crash, hang,
or orphan.

Implicit receiver discovery now recurses through `as` casts. A focused HIR/MIR
regression proves a cast-wrapped `self` is an injected parameter rather than a
`GlobalLoad`; the single bounded bootstrap removed all four `self` diagnostics,
reducing undeclared globals from 18 to 14. The run exited 2 normally without
timeout, OOM, crash, hang, or orphan. Review also identified `slice` as generic
struct-literal parsing, not import discovery, so it remains a separate lane.

Generic identifier lookahead now recognizes an enabled `{` continuation and
routes `SliceIter<T> { ... }` through the existing struct initializer while
preserving comparison backtracking and control-flow brace suppression. The
focused AST regression passes; the single bounded bootstrap removed both
`slice` diagnostics, reducing undeclared globals from 14 to 12. The run exited
2 normally without timeout, OOM, crash, hang, or orphan.

`Tensor<T, N>.ndim` now returns the runtime shape rank from
`self._shape.len()` instead of loading the generic type parameter `N` as a
value. The source-contract regression pins the complete method body; the single
bounded bootstrap removed both `N` diagnostics, reducing undeclared globals
from 12 to 10. The run exited 2 normally without timeout, OOM, crash, hang, or
orphan.

Seed HIR match lowering now distinguishes subject-owned unit variants from
real identifier bindings, initializes guarded bindings before guard evaluation,
restores shadowed locals, and preserves mutable patterns. Four focused HIR/MIR
regressions pass. Two bounded bootstrap cycles found no new crash or hang; the
first exposed and separately fixed a concurrent `SliceIter` syntax regression,
while the second proved this correctness fix does not remove the imported-enum
`Shared` diagnostics. After concurrent `C`/`Array` source repairs, Stage 2 now
stopped on six diagnostics: four unqualified imported `Shared` variants and two
`CompareExchange` uses. Owner-qualifying the CUDA/OpenCL `CompareExchange`
expression and match arms removed both diagnostics and the CUDA failing root.
Two bounded follow-ups did not advance past `Shared`; both wrapper logs record
normal Stage 2 exit 1 and strict fallback refusal, and the retained final Stage
2 log names only the HIP/OpenCL dependency closures. Qualified `Shared` match
arms and comparisons were therefore rejected as ineffective workarounds. The
remaining fix is
import-aware enum-owner registration/lowering, not an external declaration or
another call-site spelling change.

The Rust seed now resolves a bare unit variant from the typed subject's global
enum summary only when that subject is an empty imported-enum placeholder.
Materialized local variants remain authoritative, payload variants keep their
existing binding behavior, and a focused HIR/MIR regression covers two owners
that both define `Shared`, a foreign-owner-only unit, and a nonempty same-name
local enum. The regression passes. One strict, full-bootstrap admission from a
clean `origin/main` worktree rebuilt the seed/runtime and exited 1 normally at
Stage 2 discovery, before HIP/OpenCL were compiled, on a nested-empty-string
interpolation in `parser_preprocessor.spl:207`. Hoisting that `join("")` result
to an identifier fixes the parse while retaining the compact interpolation; a
real preprocessing regression covers spaced `=` and `==` with the detected host
architecture. The next bounded Stage 2 run no longer mentioned
`parser_preprocessor` and advanced to the next same-class nested-string parse
error in
`trait_solver.spl:72:47` (`expected expression`, found `Comma`). Using the
language's single-quoted raw separator inside that interpolation is pinned by a
focused Rust lexer regression (1 pass) and advances Stage 2 again. Hoisting the
newline-preserving `lean_backend.spl:166` join is covered by an exact
`LeanBuilder.build()` regression and advances discovery to the same-class
`vulkan/spirv_builder.spl:234` nested `member_ids.map("{_}")`. Therefore the
imported-`Shared` Stage 2 delta remains provisional. All bounded runs exited 1
normally with no timeout, OOM, crash, hang, orphan, or seed fallback.

## Context: in-guest RUN is otherwise REACHABLE

This bug does NOT block a plain in-guest run: `/usr/bin/simple --version` runs
in-guest on SimpleOS x86_64 under real OVMF (ring-3 `cs=0x2b`, prints
`Simple v1.0.0-beta`, `rc=0`) — loader, ring-3 transition, syscalls, and FAT32
I/O all work. Only self-interpretation of arbitrary programs hits the
cranelift enum trap; only the LLVM rebuild hits this `mcall_direct` bug.

### 2026-07-17 follow-up (FULLBOOT lane): reproduced byte-for-byte on a fresh from-scratch seed; full 19-file/symbol table captured
Ran the authoritative `scripts/bootstrap/bootstrap-from-scratch.sh
--full-bootstrap --full-cli --mode=dynload --output=build/bootstrap
--jobs=half` gate as the redeploy-readiness test for
`hir_stmt_expr_payload_extraction_nil_2026-07-17.md` (that lane's own cert-
import wall is separately fixed and confirmed on disk). Rebuilt the Rust
seed clean from scratch (`cargo build --profile bootstrap -p simple-driver`
detected, so no backend/feature fix was needed for the seed itself). Stage 2
failed with **exactly** this doc's already-diagnosed "ineffective"
follow-up result: **19 files, 38 diagnostics** — an exact match on both
counts, confirming this is the same still-open symbol-lowering bug, not a
new regression introduced since. (Initially misfiled as a new bug in this
lane's first pass; retracted after `git diff origin/main` showed the
working tree still carries this investigation's in-progress edits —
notably `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl`,
`backend_types.spl`, `mir_lowering_stmts.spl`, and the Rust-side
`src/compiler_rust/compiler/src/pipeline/native_project/{compiler,imports,mod,tests}.rs`
uncommitted vs `origin/main`, consistent with "the ineffective code was
removed" being an in-progress, not-yet-committed revert rather than a
completed one. Since the reproduced file/diagnostic counts match this doc's
prior entry exactly, the current on-disk state — committed or not — is the
same state already diagnosed here, so this is confirmation, not new
information about causation.)
Full 19-file → undeclared-symbol table (supplementing "led by
`char_to_ascii`, `self`, `Shared`, and generic symbols" above with the
complete set observed this run):
| File | Undeclared symbol |
|---|---|
| `src/app/io/feature_registry.spl` | `nogc_sync_mut__io__cuda_sffi__cuda_available` |
| `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` | `global_local` |
| `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` | `receiver_mir_type_uw` |
| `src/compiler/70.backend/backend/cuda_backend.spl` | `CompareExchange` |
| `src/compiler/70.backend/backend/hip_backend.spl` | `Shared` |
| `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` | `local_unsigned` |
| `src/compiler/70.backend/backend/native/isel_aarch64.spl` | `backend__backend__common__ascii_utils__char_to_ascii` |
| `src/compiler/70.backend/backend/native/isel_riscv32.spl` | `backend__backend__common__ascii_utils__char_to_ascii` |
| `src/compiler/70.backend/backend/native/isel_riscv64.spl` | `backend__backend__common__ascii_utils__char_to_ascii` |
| `src/compiler/70.backend/backend/native/isel_x86_64.spl` | `backend__backend__common__ascii_utils__char_to_ascii` |
| `src/compiler/70.backend/backend/opencl_backend.spl` | `Shared` |
| `src/compiler_rust/lib/std/src/core/collections.spl` | `nogc_sync_mut__src__tensor__Tensor_dot_T` |
| `src/compiler_rust/lib/std/src/core/list.spl` | `nogc_sync_mut__src__tensor__Tensor_dot_T` |
| `src/compiler_rust/lib/std/src/core/traits.spl` | `C` (the `collect<C: FromIterator<Self.Item>>` generic param) |
| `src/lib/nogc_async_mut/io/buffer.spl` | `self` |
| `src/lib/nogc_sync_mut/io/buffer.spl` | `self` |
| `src/lib/nogc_sync_mut/src/array_builder.spl` | `Array` |
| `src/lib/nogc_sync_mut/src/table.spl` | `compiler_rust__lib__std__src__core__traits__Iterator_dot_count` |
| `src/lib/nogc_sync_mut/src/tensor.spl` | `N` (the `Tensor<T, N>` generic param) |
Every "bare" undeclared symbol cross-checked against its source is a
generic type parameter (`C`, `N`) or a method receiver (`self`) — matching
this doc's existing "unresolved locals, generics, enum cases, and static
receivers must remain fail-closed" diagnosis precisely. Evidence:
`build/native_probe/redeploy-gate-fullboot-20260717.log.gz` (gate wrapper),
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log.gz`
(full 19-file detail). No stage2/3/4 binary was produced; Stage 4 correctly
refused a seed fallback (`error: full CLI build requires a verified
pure-Simple stage2/stage3 compiler; refusing seed fallback`, exit 2) rather
than silently shipping an unverified candidate.
**No new action needed beyond this doc's existing prescription**: repair
import-key normalization so unresolved locals/generics/enum
cases/static receivers fail closed instead of being emitted as external
`declare`s, then re-run this same gate command. The redeploy-gate verdict
recorded in `hir_stmt_expr_payload_extraction_nil_2026-07-17.md` is
NOT-READY, citing this doc as the concrete, already-open blocker.
