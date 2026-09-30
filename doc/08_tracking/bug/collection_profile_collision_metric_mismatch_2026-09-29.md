# Collection explanation reports the wrong collision metric

Status: open. Owner: seven-plan item 7. The three-cycle investigation limit is
exhausted; retain this failure for a separately authorized bounded investigation.

The existing collision-profile scenario in
`test/01_unit/app/optimize/collection_plan_cli_spec.spl` supplies probe count 100
and collision count 40, but the Phase 1 Windows diagnostic reports
`profile.hash_collisions_p95=100` rather than 40. The expected value is meaningful
and has not been weakened. The complete file remains 8/9 after the independent
constructor-explanation correction.

Inspection found the serializer uses metric values, the reader retains metric
names/values, and the lookup key contains the name and exact target/site. This
does not establish which boundary is defective. A minimal separate envelope
probe failed admission before measuring values and was inconclusive. Do not
attribute the bug to the seed, serializer, or production planner without a
reproducer that separates those owners.

Resume by retaining an admitted envelope and comparing decoded named metrics,
index insertion/readback, and final explanation through the real owners. Require
actual executed assertions and a second distinct-metric control. The diagnostic
runner is not native or admitted SPipe evidence.

See `doc/03_plan/evidence/seven_plans/windows/item7_initializer_explanation_2026-09-29.md`
for the exact runner hash, counts, and retained log paths.
