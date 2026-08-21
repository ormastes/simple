# SSA alloca lane rejects `Ret(Some(..))` — four reproducer specs RED, two specs assert the opposite

- **Status:** OPEN (left RED deliberately, per `.claude/rules/testing.md`)
- **Filed:** 2026-08-21
- **Component:** `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`
- **Related:** `doc/08_tracking/bug/llvm_constants_lost_ret_zero_2026-08-01.md`

## Symptom

Four artifacts under `test/01_unit/compiler/mir_opt/` are RED on one shared root
cause:

| artifact | Results |
|---|---|
| `runtime_array_assignment_ssa_spec.spl` | `Results: 7 total, 0 passed, 7 failed` |
| `ssa_alloca_value_return_slotting_spec.spl` | `Results: 6 total, 0 passed, 6 failed` |
| `ssa_alloca_terminator_use_coverage_spec.spl` | `Results: 7 total, 4 passed, 3 failed` |
| `ssa_alloca_store_retention_native_check.spl` | `FAIL: alloca rewrite dropped a defining instruction or its slot store` (rc=1 under `bin/simple run`) |

Note the fourth is a `*_check.spl` script, not a spec: under `bin/simple test`
it reports `reason=zero-examples`, which is a harness category error, not its
real verdict. Run it with `bin/simple run`.

## Root cause

`ssa_alloca_transform_blocks` (`var_reassign_ssa.spl:1646`) rejects any function
with a value-returning terminator:

```
if ssa_term_has_value_return(block.terminator):
    return ssa_var_transform_reject("unsupported value return terminator", blocks, [])
```

with two consequences downstream: `ssa_collect_term_operand_locals` (`:1276`)
never counts a returned local as a use, and `ssa_alloca_rewrite_term` (`:1580`)
never loads a slotted local back out for the return. The four artifacts above
each assert the opposite behaviour.

## Why this was NOT "fixed" by admitting value returns

Two currently-GREEN specs assert the rejection on the *same* function, so
flipping it makes them RED — a net-zero trade, not a fix:

- `test/01_unit/compiler/driver/ssa_local_payload_source_spec.spl:33-39` pins the
  literal source text (`fn ssa_term_has_value_return`, `case Ret(value): value != nil`,
  `"unsupported value return terminator"`).
- `test/unit/compiler/mir_opt/var_reassign_analysis_spec.spl:67` calls
  `ssa_alloca_transform_blocks` and asserts
  `result.reason == "unsupported value return terminator"`.

The rejection also carries a standing hazard note in the source: the
`Ret(Some(..))` `MirOperand` payload must not be inspected on the staged-native
lane. Removing that gate is a real codegen-risk change and must not be done
opportunistically while a bootstrap is mid-flight.

## Regression verdict

Not a regression. A/B against a clean `HEAD` worktree (today's `src/compiler/50.mir/**`
work — the `enum_variant_owners` index and the trace gating — excluded) produced
byte-identical `Results:` lines for all four. Pre-existing.

## Unblock condition

Decide the single owner of the value-return contract, then land it in one change:
either (a) admit `Ret(Some(..))` into the alloca lane and update the two specs
above with evidence that the staged-native payload read is safe, or (b) keep the
rejection and retire the four reproducers with a written rationale. Do not do
half of either.

## Update 2026-08-21 (test-infrastructure lane) — no spec-side fix; decision still owed

Re-examined for a spec-lane fix and there is none. Both sides of the conflict
are legitimate artifacts under `.claude/rules/testing.md`:

- The four reproducers assert behaviour the product does not have -> stay RED.
- The two GREEN specs pin the current, deliberate rejection -> must not be
  weakened.

Weakening either side to make numbers move is exactly what the rules forbid, so
nothing was changed. One observation worth recording for whoever takes the
decision: `test/01_unit/compiler/driver/ssa_local_payload_source_spec.spl:33-39`
pins the LITERAL SOURCE TEXT of `var_reassign_ssa.spl` (`fn
ssa_term_has_value_return`, `case Ret(value): value != nil`, the diagnostic
string). A source-text pin makes any refactor of that function a spec failure
even when behaviour is preserved, which is a spec-design defect independent of
the value-return decision. When option (a) is taken, replace that pin with a
behavioural assertion through `ssa_alloca_transform_blocks` (the shape
`test/unit/compiler/mir_opt/var_reassign_analysis_spec.spl:67` already uses)
rather than editing the pinned strings.

Owner of the unblock decision remains `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:1646`.
