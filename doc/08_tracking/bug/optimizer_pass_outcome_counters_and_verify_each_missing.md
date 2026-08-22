# Optimizer Pass Outcome Counters and Verify-Each Are Missing

## Status

Open. This blocks treating optimizer planning evidence as proof that a pass executed or
preserved MIR invariants.

## Evidence

The MIR pass registry can now describe status, expectation, backend selection, witness
contracts, and deterministic requested-pipeline planning. The dispatcher does not yet
return a common verified change receipt with candidate, transformed, rejected,
instruction-delta, and rejection-reason counters. The repository also lacks one general
post-pass verifier covering CFG targets, unique block/value identity, SSA dominance,
types, ownership, and loop boundary invariants.

Consequently `simple.opt-pipeline-report/v1` deliberately records
`run_outcome: not-run` and null execution counters. Selection must not be interpreted as
execution.

## Required fix

1. Make every pass adapter return a common `PassOutcome` without discarding its native
   statistics.
2. Populate `PassRunRecord` from the actual adapter result, with stable coalesced reason
   codes and injected timing.
3. Add a general MIR verifier and require its receipt after every changed pass in test
   and `--verify-each` modes.
4. Reject transformed records without candidates, impossible instruction counts,
   missing verifier receipts, or missing active witness contracts.
5. Add positive, negative, malformed-MIR, and deterministic report fixtures.

## Unblock condition

Focused pure-Simple Stage 4 tests prove the execution record is produced by the real
dispatcher, all changed outputs pass the general verifier, and disabling a pass makes
its positive witness report no transformation.
