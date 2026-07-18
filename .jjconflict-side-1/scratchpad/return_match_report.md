# Native `return` inside match arms of a value-returning function — root cause + fix

## Status: FIXED, verified against oracle, full smoke matrix gate passes.

Worktree: `/tmp/wt_retmatch` (base `7780fcde1948126f46b8bce163a3d43c92ba294c`), removed after this run.
Patch: `/home/ormastes/dev/pub/simple/scratchpad/return_match.patch` (source-only diff, worktree bin/release symlink noise excluded).

## Re-verification of the premise

Confirmed the repro still reproduces on the pinned base commit (post the recent SSA id-0
store-drop fix in `var_reassign_ssa.spl`): native build exits rc=0 but prints garbage
(`2147483652101395029022328` instead of oracle `100`/`14`). Statement-position match and
plain `case x:` bindings (no `return`) are unaffected — this is specific to `return`
appearing as the *trailing expression* of a match arm's body.

## Root cause

File: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`

`HirExprKind.Return(value)` is lowered as an **expression** in
`_MirLoweringExpr/expr_dispatch.spl:1240`: it evaluates the return operand, calls
`builder.terminate_return(Some(operand))` on the *current* block (correctly capturing the
real return value in the `Ret` terminator), then — because every expression must yield
*some* `LocalId` to its caller — allocates and returns a fresh `MirType.unit()` dummy temp
(`ret_temp`) that is **never assigned**.

`match` on integers lowers via `emit_if_chain_dispatch` (sparse, <4 arms — the repro's path)
and `emit_switch_dispatch` (dense, jump-table). Both, before this fix, ended each arm/default
block unconditionally with:

```
val arm_result = self.lower_block(body)
var b_arm2 = self.builder
if val arm_result_local = arm_result:
    b_arm2.emit_copy(result, arm_result_local)
    result_defined = true
b_arm2.terminate_goto(merge_block)
```

When an arm's body is `return 100`, `lower_block` treats the bare `return` as the block's
trailing value, so `arm_result = Some(ret_temp)` (the *unassigned* unit dummy, not `100`).
Two things then go wrong on that same block, which already carries a correct `Ret(100)`
terminator set by the Return-expression lowering:

1. `emit_copy(result, ret_temp)` appends a *new* instruction into a block that already has
   a terminator. Per `mir_data.spl`'s `finalize_block` / `switch_to_block` bookkeeping, once
   another block is later switched-to, the buffered instruction list for this block gets
   replaced/finalized — this silently **wipes the `return 100` const/copy instructions**
   that had already been emitted for the real return value, leaving only the bogus `result`
   copy of an undefined register.
2. `terminate_goto(merge_block)` calls `set_terminator`, which **unconditionally overwrites**
   whatever terminator is already set (`mir_data.spl:463-472`, `set_terminator` always does
   `block.terminator = term`). This clobbers the correct `Ret(100)` with `Goto(merge_block)`,
   so control that should have returned 100 instead falls into `match_merge`, which then
   reads the garbage/undefined `result` register and (via the function-level
   `current_block_has_explicit_terminator()` guard in `function_lowering.spl:233`) returns
   *that* garbage as the function's value — exactly the huge garbage numbers observed.

This is the identical bug class already fixed for `lower_if` (`mir_lowering_stmts.spl:645`,
`:665`), `lower_loop`/`lower_while` (the recently-landed loop/break fix), and — notably —
already fixed for **enum** matches in `lower_enum_match` (same file,
`switch_operators_calls.spl:802-834`, with an explicit code comment documenting this exact
failure mode). The int-match paths (`emit_if_chain_dispatch`, `emit_switch_dispatch`) were
simply never given the same guard when `lower_enum_match` was patched.

## Fix

Wrapped the arm-body and default-body epilogues in both `emit_if_chain_dispatch` and
`emit_switch_dispatch` with the same `current_block_has_explicit_terminator()` guard already
used by `lower_if` / `lower_enum_match`:

```
if not b_arm2.current_block_has_explicit_terminator():
    if val arm_result_local = arm_result:
        b_arm2.emit_copy(result, arm_result_local)
        result_defined = true
    b_arm2.terminate_goto(merge_block)
```

When the arm body already terminated (via `return`), nothing further is emitted into that
block — the real `Ret` terminator (and its correct operand) is left intact, and the arm
never reaches `match_merge`. No new fallback/error paths were introduced; unaffected arms
(no `return`) behave exactly as before.

## Battery (oracle vs native, `env -u SIMPLE_BOOTSTRAP bin/simple run` vs
`native-build --entry ... && ./out`)

| # | Case | File | Oracle | Native (after fix) | Match |
|---|------|------|--------|---------------------|-------|
| 1 | Repro: `case 1: return 100` / `case x: return x*2` | `p.spl` | `100`,`14` | `10014` | YES |
| 2 | Return in first arm + fall-through arm computing a value | `battery2.spl` | `100`,`27` | `10027` | YES |
| 3 | Mixed: one arm returns, other assigns local, `return` after match (statement-position match) | `battery3.spl` | `200`,`21` | `20021` | YES |
| 4 | Match-with-return inside a `while` loop | `battery4.spl` | `300`,`1006`,`-1` | `3001006-1` | YES |
| 5 | Multi-construct: 2 value-returning fns w/ match+return + a statement match + a `while` loop, one program | `battery5.spl` | `111`,`10`,`222`,`12`,`10` | `111102221210` | YES |

(Oracle seed prints each program's output twice — JIT-fallback-then-interpreter re-run
artifact, unrelated/pre-existing; only the first half was compared.)

## Full smoke matrix (`sh scripts/check/native-smoke-matrix.shs`)

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

Only failure: `option_nil_check` (rc got=1 want=7) — this is the pre-existing allowed
failure named in the task's gate (`>=14/15, 0 codegen_fallback_hits, only allowed fail =
option_nil_check`). Gate satisfied, no regressions.

## Deliverables

- Patch: `/home/ormastes/dev/pub/simple/scratchpad/return_match.patch`
  (source-only diff of `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`)
- This report: `/home/ormastes/dev/pub/simple/scratchpad/return_match_report.md`
- Worktree `/tmp/wt_retmatch` removed after verification; nothing committed/pushed per
  instructions.
