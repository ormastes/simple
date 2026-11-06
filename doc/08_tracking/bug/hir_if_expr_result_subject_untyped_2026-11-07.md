# Untyped `if` expression yielding Ok/Err makes a later match ambiguous

- **ID:** hir_if_expr_result_subject_untyped_2026-11-07
- **Severity:** P2 (2 Stage 2 MIR errors in run 13)
- **Status:** fixed

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

## Fix (2026-11-07)

`binding_kind_type` (`src/compiler/20.hir/hir_lowering/statements.spl`) types
a binding from an `if` / `if-elif` expression with an else branch by the join
of its branch tails (`binding_branch_join`), but only when the join is a fully
known Result. Branch tails are typed by `binding_block_value_type`: a bare
builtin `Ok(v)` / `Err(e)` is a Result with the other arm unknown, unsuffixed
literals have their literal type, `base.field` uses the declared field type,
and a nested `if` is joined recursively. Two Results join arm by arm (an
unknown arm takes the other side, otherwise the arms must be equal); other
types join only when identical. A partial join (an arm neither branch knows)
or a non-joining pair leaves the binding untyped, as before, so no Error arm
reaches type inference or MIR `lower_type`, and the match still fails closed.

Independent review of the first draft found that it typed partial joins
(`Result<T, Error>`), which leaked an `E-MIR-TYPE-Error` advisory and would
check the initializer against an Error arm; and that two different unsettled
arms (`Ok(t: T)` vs `Ok(u: U)`) joined silently. Both are fixed and pinned by
the spec (it also fails on any `HirTypeKind.Error` MIR advisory).

Spec `test/01_unit/compiler/50.mir/if_expr_result_join_subject_spec.spl`:
before 3/6 (only the three fail-closed negatives pass), after 6/6, including
the exact `jit_instantiator.spl:419` shape (struct-field payloads, nested if).
