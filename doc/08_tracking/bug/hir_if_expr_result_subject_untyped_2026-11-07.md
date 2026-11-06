# Untyped `if` expression yielding Ok/Err makes a later match ambiguous

- **ID:** hir_if_expr_result_subject_untyped_2026-11-07
- **Severity:** P2 (2 Stage 2 MIR errors in run 13)
- **Status:** open

## Symptom

`src/compiler/99.loader/loader/jit_instantiator.spl:419`:

    val code_result = if typed_result.success:
        Ok(typed_result.code)
    else:
        Err(...)
    match code_result:
        case Ok(compiled_code): ...

fails with `enum match: bare variant 'Ok' is ambiguous (declared in multiple
enums) ... has type unresolved` (and the same for `Err`).

## Root cause

HIR lowers `ExprKind.If` with an else-branch to `HirExprKind.If` with
`has_type_: false, type_: Unit` (`src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`,
If arm), so the bound local has no type and MIR's bare-variant resolver has no
subject owner. With any other enum in the closure declaring `Ok`/`Err`, the
match fails closed (correctly, given no type).

Minimal repro (in-process HIR+MIR, `lower_closure` harness): another module
declares `enum Status: Ok, Err(code: i64)`; `val r = if b: Ok(1) else: Err("x")`
then `match r: case Ok(v): v case Err(_): 0` -> ambiguity error. The same
match on a typed `Result<i64, text>` call result lowers clean.

## Fix direction

Type the if-expression from its branch tails (unify `Result<T, _>` /
`Result<_, E>`), rather than accepting a guessed owner in MIR.
