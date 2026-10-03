# Snapshot scratch reclamation

Executable: `test/01_unit/lib/scv/compile_snapshot_reclamation_spec.spl`.
Native execution and SPipe doc generation: pending. This manual records the
test contract, not a passing result.

The allocation scenario materializes UTF-8/CRLF source through both the
unscoped control and scoped production helper. After warming literal caches,
eight results are retained for each route. The scoped route must retain less
than half the registered objects of the control; every row, content digest,
byte count, drift flag and written file must remain correct after later
scopes have ended.

The refusal scenario supplies a stale inventory digest, then a correct entry.
The first result must preserve its exact drift error and empty row after the
second materialization succeeds. This verifies failure cleanup and retained
result lifetime together.

Registered object counts do not measure resident bytes or elapsed time.
Cold/warm bootstrap RSS, cache reuse and timing remain separate acceptance
requirements in `doc/08_tracking/bug/bootstrap_snapshot_memory_retention_2026-10-02.md`.
