# Seed: `return` in a match/if arm of an `it` body fails with "try: early return"

- Status: verification-pending
- Found: 2026-11-28 (ft-29 group G2)
- Specs: test/03_system/app/traceability/feature/admission_spec.spl (0/11),
  test/03_system/app/traceability/feature/run_evidence_spec.spl (0/12)

## Root cause

A `return` inside a match or if EXPRESSION arm is raised on the `TryError`
channel (`interpreter/expr/control.rs`, bug interp_return_in_match_expr_swallowed_2026-06-30).
Function, method and lambda boundaries catch it. BDD example bodies run through
`exec_block_value` / `exec_lambda` in `interpreter_call/bdd.rs`, whose
`localize_bdd_return` only localized `BlockReturn`, so `TryError` escaped and the
example was reported as the error text "try: early return". The specs use
`match ...: case Err(reason): fail(reason); return` in every `it`.

## Fix

`localize_bdd_return` also maps `TryError(v)` to `Ok(v)`, and `exec_block_value`
applies it to both its lambda and block-closure paths.

## Tests

- Repro and prevention: `test/01_unit/compiler/bdd_it_match_arm_return_spec.spl`
- The two traceability specs above now run their bodies (they fail closed with the
  documented BLOCKED reasons via `fail()`, which is their in-development contract).

## Verification

Pending native verification on a redeployed seed.
