# Optimizer Pass Outcome Counters and Verify-Each Are Missing

## Status

Open, narrowed. A function-pass boundary now produces a structural before/after receipt,
but this still blocks treating planning evidence as proof of full MIR correctness.

## Evidence

The MIR pass registry can now describe status, expectation, backend selection, witness
contracts, and deterministic requested-pipeline planning. The function dispatcher now
returns exact native candidate/transformed counts for the active `write_coalesce` and
`syscall_batch` adapters, with stable positive-witness reasons and instruction deltas.
Those counts now come from the hints actually emitted in the rewrite, avoiding the former
second recognizer scan and preventing recognizer/rewrite drift in recorded outcomes.
It rejects an active function adapter that lacks exact outcome support rather than
inferring a Boolean candidate from serialized MIR change. Module-pass outcomes and
native rejected-candidate reasons remain unavailable. The repository also lacks one general
post-pass verifier covering SSA dominance, types, ownership, and loop boundary invariants.

`run_named_pass_with_record` now verifies non-empty functions, unique non-negative block
and local identities, canonical instruction/terminator access coverage, declared-local
membership for every modeled DEF/USE, entry membership, and branch/unwind target membership
before and after a function-scoped pass. Identity membership uses dictionaries instead of
quadratic growing-array searches. Its exact counter adapters cross-check native counts
against serialized change and fail on disagreement. It is not yet the pipeline-wide
`--verify-each` gate.

Consequently `simple.opt-pipeline-report/v1` deliberately records
`run_outcome: not-run` and null execution counters. Selection must not be interpreted as
execution.

## Required fix

1. Extend the exact `PassOutcome` adapter contract to active module passes and future
   rehabilitated passes without discarding native statistics.
2. Extend actual adapter results with stable rejected-reason codes and injected timing.
3. Extend the structural receipt beyond deployed operand/local validity into SSA dominance,
   types, ownership, and loop boundaries, then require it after every changed function/module
   pass in test and `--verify-each` modes.
4. Reject transformed records without candidates, impossible instruction counts,
   missing verifier receipts, or missing active witness contracts.
5. Add positive, negative, malformed-MIR, and deterministic report fixtures.

## Unblock condition

Focused pure-Simple Stage 4 tests prove the execution record is produced by the real
dispatcher, all changed outputs pass the general verifier, and disabling a pass makes
its positive witness report no transformation.
