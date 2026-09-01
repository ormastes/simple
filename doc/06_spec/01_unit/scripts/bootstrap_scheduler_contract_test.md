# Bootstrap scheduler contract specification

Executable source:
`test/01_unit/scripts/bootstrap_scheduler_contract_test.shs`.

The contract test validates the immutable DAG schema and five scheduler flows:

1. Stage 3 begins after Stage-2 smoke admission while parent qualification is
   still active; both task receipts admit one qualified lineage.
2. A late parent-qualification failure recursively invalidates Stage 2, Stage
   3, Stage 4, deploy, and release while preserving the child as tainted
   evidence.
3. A changed generation lease prevents final lineage publication even when a
   task otherwise reports success.
4. A one-CPU/low-memory reservation serializes qualification after the compiler
   critical path and records that overlap was not claimed.
5. A requested release flag is removed from provisional Stage 2/3 execution
   and appears only on the post-qualification Stage-4 continuation under the
   scheduler release-admission authority.

The final negative case proves task-command overrides are accepted only when
the explicit scheduler self-test authority is active.
