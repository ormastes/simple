# Explicit HIR parallelism ledger regressions

Owner bug: `parse_disable_suppresses_explicit_hir_parallelism_2026-10-05`.
Scope: the existing real filesystem recovery ledger, separate from the primary
owner's native-build admission/environment tests. Executable source is
`test/03_system/compiler/driver/hir_shard_recovery_spec.spl`.

Three added cases:

1. Twenty distinct owners each claim one module. A competing owner cannot claim
   it or publish a cached PASS. The legitimate terminal is immutable, exactly
   twenty terminals exist, every owner has one claim, and closure succeeds.
2. An owner completion marker does not complete its active module. Inventory
   closure rejects the unknown outcome. After the coordinator's separately
   proven reap, sealing preserves the prior good terminal and attributes the
   crash; replacement claims only unclaimed work. Aggregate status stays failed.
3. A structurally valid CACHE_STORED/PASS copied from a different module/owner
   is rejected by accounting even though terminal files exist. The donor
   remains unchanged and aggregate admission fails.

All executable cases are UNRUN. They exercise deterministic API interleavings
against actual claim/terminal files; they do not simulate process death or
claim simultaneous race coverage. Cache markers are ledger metadata, not proof
that HIR bytes were decoded or reused. Existing codec validation remains the
cache owner's responsibility.

Later admitted native validation must observe distinct process owners, real
crash/reap receipts and cache hit/commit identities, preserving twenty jobs per
new task and the eighty-slot global coordinator. Capture elapsed time and
aggregate RSS; compare the same source/cache identity to the serial baseline.
No production code, memory policy, live queue, frozen source or cache was changed.
