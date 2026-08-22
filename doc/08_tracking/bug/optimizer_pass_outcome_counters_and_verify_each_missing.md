# Optimizer Pass Outcome Counters and Verify-Each Are Missing

## Status

Open, narrowed. A function-pass boundary now produces a structural before/after receipt,
but this still blocks treating planning evidence as proof of full MIR correctness.

## Evidence

The MIR pass registry can now describe status, expectation, backend selection, witness
contracts, and deterministic requested-pipeline planning. The dispatcher does not yet
return a common verified change receipt with candidate, transformed, rejected,
instruction-delta, and rejection-reason counters. The repository also lacks one general
post-pass verifier covering CFG targets, unique block/value identity, SSA dominance,
types, ownership, and loop boundary invariants.

`run_named_pass_with_record` now verifies non-empty functions, unique non-negative block
and local identities, entry membership, and branch/unwind target membership before and
after a function-scoped pass. It records instruction counts and an honest serialized-MIR
change outcome. It deliberately does not invent native candidate or rejection counts,
and it is not yet the pipeline-wide `--verify-each` gate.

Consequently `simple.opt-pipeline-report/v1` deliberately records
`run_outcome: not-run` and null execution counters. Selection must not be interpreted as
execution.

## Required fix

1. Make every pass adapter return a common `PassOutcome` without discarding its native
   statistics.
2. Populate `PassRunRecord` from the actual adapter result, with stable coalesced reason
   codes and injected timing.
3. Extend the structural receipt with operand/local validity, SSA dominance, types,
   ownership, and loop boundaries, then require it after every changed function/module
   pass in test and `--verify-each` modes.
4. Reject transformed records without candidates, impossible instruction counts,
   missing verifier receipts, or missing active witness contracts.
5. Add positive, negative, malformed-MIR, and deterministic report fixtures.

## Unblock condition

Focused pure-Simple Stage 4 tests prove the execution record is produced by the real
dispatcher, all changed outputs pass the general verifier, and disabling a pass makes
its positive witness report no transformation.
