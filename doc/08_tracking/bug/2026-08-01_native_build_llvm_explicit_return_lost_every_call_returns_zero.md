# `native-build --backend llvm`: every user function using `return` silently returned 0

- **Date:** 2026-08-01
- **Status:** FIXED (verified by built-and-run ELF, RED/GREEN A/B on the same tree)
- **Severity:** Critical — silent wrong answer, exit 0, real ELF, no diagnostic
- **Area:** `src/compiler/20.hir/hir_lowering/`, `src/compiler/70.backend/backend/_MirToLlvm/`
- **Lane:** `bin/simple_seed native-build <file>.spl --backend llvm` (the pure-Simple
  compiler interpreted by the Rust seed). The seed's own interpreter (`simple run`)
  is NOT affected — it never goes through this HIR/MIR/LLVM path.

## Summary

Any user-defined function whose value left the body through an explicit `return`
statement compiled to `ret i64 0`. Inline arithmetic in the entry function was
correct, so the failure was invisible except as zeros appearing through every
function boundary. Exit code 0, a real ELF, no error, no interpreter-fallback
notice.

A second, independent defect made a function that returns a *named local* (via a
MIR `Copy`) also emit `ret <ty> 0`, even on the tail-expression form.

Measured, LLVM native lane, identical program before/after:

| source form | before | after |
|---|---|---|
| `fn add(a,b) -> i64: return a + b` | **0** | 5 |
| `fn add(a,b) -> i64: a + b` (tail) | 5 | 5 |
| `fn const42() -> i64: return 42` | **0** | 42 |
| `fn f1(a) -> i64: val x = a*2; return x` | **0** | 10 |
| `fn f2(a) -> i64: if a>0: return 111; return 222` | **0 / 0** | 111 / 222 |
| `fn f3(a) -> i64: val y = a+1; y` (tail of a local) | **0** | 6 |
| `fn f4() -> text: return "hello"` | **empty** | hello |
| `fn f5() -> text: "world"` (tail literal) | world | world |

The emitted IR for the RED case (captured with `SIMPLE_KEEP_LLVM_IR=1`):

    define i64 @add(i64 %l1, i64 %l2) nounwind readonly alwaysinline {
    bb0:
      ret i64 0
    }

The call site was always correct (`mov $2,%edi; mov $3,%esi; call add; mov %rax,%rbx`),
so this was neither a call-site nor a register-ABI bug — the callee body was empty.

## Root cause 1 (the big one): `case Some(...)` matched against a plain nullable

`src/compiler/20.hir/hir_lowering/statements.spl`, the disc-guarded
`StmtKind.Return` fast path (which SHADOWS the ordinary `case StmtKind.Return`
arm further down the same function):

    val rt_val: Expr? = ...            # correctly holds the returned expression
    val rt_hir: HirExpr? = match rt_val:
        case Some(rt_val_e): self.lower_hir_expr(rt_val_e)
        case _: nil                    # <-- ALWAYS taken

`rt_val` is a plain NULLABLE `Expr?`, not an `Option` box, so `case Some(...)`
never matches it on this lane. Every `return <expr>` therefore lowered to
`HirExprKind.Return(nil)`, MIR produced `Ret(nil)`, and the LLVM backend
faithfully emitted the documented "no value" `ret <ty> 0`.

Proved with a level-gated probe (`SIMPLE_MIR_RET_TRACE=1`):

    [hir-ret-fast] ast_nil=false hir_nil=true     # value present in AST, dropped in HIR
    [llvm-ret-top] fn=f1 value_nil=true           # backend sees Ret(nil)

**Fix:** bind with `if val`, the repo idiom for nullables.

This is the same defect family as
`.claude/memory/reference_case_some_on_nullable_never_matches.md`; that fix
landed elsewhere, this call site was missed. *A sweep that does not enumerate the
family leaves siblings.*

## Root cause 2: `Copy` destinations were never marked defined

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`.
`translate_instruction` has disc-guarded fast paths for `Const` and `Copy` that
`return` early — before the trailing `self.mark_instruction_dest_defined(inst)`
call at the bottom of the method. `translate_const` sets `defined_locals` itself,
so `Const` was covered; `translate_copy_move` did not, so **no Copy destination
was ever recorded as defined**. `translate_terminator`'s not-defined guard then
fired and emitted `ret <ty> 0` for any function returning a named local:

    if self.return_locals.has(id) or not self.local_types.has(id) or not self.defined_locals.has(id):
        emit ret <ty> 0

Probe output: `[llvm-ret] fn=f3 local=4 is_return_local=false has_type=true defined=false`.

**Fix:** set `self.defined_locals[dest_id] = true` in `translate_copy_move`, at
the value-defining site, so the fast path and the `Move` arm agree.

Both fixes are required: with only fix 1, `f1`/`f3` still returned 0.

## Verification (PROVED)

RED baseline was re-measured on pristine origin content for both files
(`git show <origin-tip>:<path>`), then the fixes were restored and re-measured on
the same tree — an A/B with only these two files toggled. Positive artifact: a
built ELF printing distinctive non-zero values derived through function calls
(`f2a=111 f2b=222 fact=120 outer=120`).

Family sweep on the fixed lane (all correct): 5-argument function, `bool`, `f64`,
`text`, struct-by-value return, direct recursion (`fact(5)=120`), nested calls,
class methods (`me` and non-mutating), and both explicit-`return` and
tail-expression forms. `fn main() -> i64` now propagates its returned value to
the process exit code (`return t` where `t==5` exits 5); before the fix it
exited 0.

`scripts/check/native-smoke-matrix.shs` must be run with
`SIMPLE_BINARY=bin/simple_seed` — its default `bin/simple` crashes on
`native-build` (`runtime error: field access on nil receiver`), so the default
invocation reports nothing about this lane. With the seed it is very slow
(~5 min/case, each case rebuilds the pure-Simple compiler under the seed
interpreter with `--clean`). Cases 1-2 PASS on the fixed tree
(`arith_fn_call` rc=7, `if_elif_else` rc=3, 0 interpreter-fallback hits); case 3
`while_sum` fails to build, pre-existing (see below).

## Adjacent gaps found, NOT caused by this bug (pre-existing, reproduced on
## pristine origin content)

- `unresolved method call: merge` in MIR lowering. Reproduced identically on
  pristine origin content in every case below — pre-existing, not a regression.
  Two shapes hit it:
  - a `me` method that MUTATES a field and then returns it
    (`self.n = self.n + d; return self.n`);
  - a `while` loop whose accumulator is then returned — this is exactly
    `native-smoke-matrix.shs` case 3 (`while_sum`), which fails to BUILD.
  A `while` loop on its own is fine (`var i = 0; while i < 3: i = i + 1` builds
  and prints 3), and so is a returned mutated `var` without a loop
  (`var t = 0; t = t + 5; return t` exits 5), so it is the combination.
- Lambdas/closures fail this lane with `MIR lowering error: undefined variable: z`.
- `--backend c` is rejected outright: "native-build backend 'c' is not available
  in the pure Simple command path". LLVM is the only usable native-build backend
  here, so this defect had no working sibling lane to cross-check against.
- The self-hosted `bin/simple` (not the seed) crashes with
  `runtime error: field access on nil receiver` on `native-build`, so the seed is
  currently the only way to exercise this path.

## Debug probes added (level-gated, default OFF)

- `SIMPLE_MIR_RET_TRACE=1` — `[hir-ret-fast]` in `statements.spl`: whether the
  AST return value survived into HIR.
- `SIMPLE_LLVM_RET_TRACE=1` — `[llvm-ret-top]` / `[llvm-ret]` in
  `core_codegen.spl`: whether the backend saw a value on `Ret`, and which of the
  three zero-fallback conditions fired.
- `SIMPLE_KEEP_LLVM_IR=1` (pre-existing) keeps `/tmp/simple_llvm_<pid>.ll`.
