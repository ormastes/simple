# Fiber scheduler completion ownership — 2026-10-28

## Defect and repair

At release base `39ce4bca7a6`, `fiber_sched_complete` accepts a completion
without checking whether that worker picked the fiber. Repeating DONE subtracts
its estimate twice, falsely freeing another admitted fiber's reservation;
repeating YIELD duplicates its queue entry. Completing a pending or parked fiber
also violates reservation/state accounting. Invalid indices reach array access.

The existing single-carrier representation records a picked fiber as READY,
owned by the worker, and absent from that worker's runnable queue. Validate that
predicate and both indices before mutation. Reject invalid delivery with a
latched diagnostic and unchanged reservation/queues. Preserve an earlier error;
allow valid owners to finish and drain even after an admission/ownership error.
No new scheduler, state ABI, thread carrier, or process evidence is introduced.
This does not detect an old delivery arriving after the same fiber is picked
again: v1 has no per-pick generation. Arbitrarily corrupted public state and
concurrent mutation remain outside this pure-core contract.

## Regression evidence

`test/01_unit/lib/common/task_runner/fiber_scheduler_spec.spl` adds seven cases:
duplicate DONE, unpicked READY, pending completion, duplicate YIELD, parked
completion followed by wake/drain, foreign worker followed by owner drain, and
negative/out-of-range worker/fiber indices. Existing overflow/progress tests
remain present.

Baseline `/tmp/shared-scheduler-admission-red.log`: 14 existing examples passed;
six new examples failed, including reserved 0 instead of 10, duplicate queue
`[0, 0]`, and reserved -10. The final invalid-index example timed out at the
120-second child limit. This is a partial failing baseline, not a completed
21-case receipt.

After repair, `/tmp/shared-scheduler-admission-green.log`: 21 declared/executed/
passed, zero failed/skipped/dropped, 37ms reported test duration. Command used
`test <spec> --mode=interpreter --no-session-daemon --sequential --no-db
--no-cache --assert-ran`, with `SIMPLE_LIB` at the changed source tree.
Producer: existing Phase 1 generation `aa58a24ebe00248b428d4507e5cb0c58ec497c28ec8b2a3ed71ec65d697f756c-ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`
under `/Users/ormastes/wt/release-bootstrap-integration-20261025`.
Carrier regression `/tmp/shared-scheduler-admission-carrier.log`: existing
`file_fiber_v1_spec.spl` passed 12/12 (2268ms), including admission-error draining
and overflow terminalization. `direct-env-runtime-guard --working` and diff
whitespace checks passed.

Native backend qualification and shared BuildRunner/TestRunner admission are
not established by this interpreter evidence. No Phase 2 rebuild was performed.
