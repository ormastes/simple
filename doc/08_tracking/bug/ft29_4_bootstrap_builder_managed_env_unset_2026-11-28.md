# ft29-4: bootstrap_builder specs assert instead of reporting a precondition when the managed scope is absent

Status: verification-pending

## Symptom
- `distributed_builder_spec.spl` 0/7 (first failure at the qualifier `assert(file_is_regular_no_follow(...))`).
- `phase4_compiler_acceptance_spec.spl` 0/3 (`require_phase4_binding` asserts on empty `SIMPLE_MANAGED_PHASE4_*`).

## Root cause
Both specs are driven by the managed bootstrap scope (`src/app/bootstrap_builder/managed_suite*.spl`),
which exports `SIMPLE_BUILDER_QUALIFIER` (compiled native qualifier) and `SIMPLE_MANAGED_PHASE4_*`
(admitted produced CLI/interpreter + sha pins). Run standalone via `simple test <spec>` those
variables are unset, so the specs failed with a bare assertion. The tools are genuinely
unavailable there; nothing in the compiler was wrong.

## Fix
`builder_qualifier_precondition()` / `phase4_binding_precondition()` return a reason when the
binding is absent; each `it` then does `fail("precondition: <reason>")` and returns, which the
runner reports as BLOCKED (`parse_blocked_examples`). With the binding present the original
assertions run unchanged (nothing weakened).

## Tests
- Repro: the two specs (before: failed 0/7, 0/3; after: BLOCKED 7, 3).
- Prevention: `test/01_unit/app/bootstrap_builder/managed_preconditions_spec.spl` (2/2).
- Verified in-scope execution still needs a managed bootstrap run (not available here).
