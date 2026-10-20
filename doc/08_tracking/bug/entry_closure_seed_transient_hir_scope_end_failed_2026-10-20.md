# native-build --entry-closure on the seed: `transient HIR scope end failed`

Found 2026-10-20 while fixing `cannot cast object to i64` (same lane).

FIXED (this change): `cannot cast object to i64`. `driver as i64` (27 sites) and
`execution as i64` (3 sites) cast a class to its address; the seed interpreter has
no such cast and an Object address is not stable under copy-on-write. Per-compilation
pins now key on `CompilerDriver.identity_id` / `MonoArchiveExecutionV1.identity_id`
(process-unique counter, never reused, 0 = unassigned and refused at pin capture).
Follow-up: `_driver_current_pins_v1`, `_driver_hir_semantic_pins_v1`,
`_hir_production_holds_v1` entries are not removed when a driver dies (before, an
address reuse overwrote them); bounded per compile, grows in long-lived processes.

Next layer, NOT fixed: hello world with the coverage-wrapper flags
(`--backend llvm --refresh-source-authority --entry-closure --runtime-bundle
core-c-bootstrap`, `SIMPLE_SCV_INVENTORY_COLD_INIT=1`, MemoryMax=8G; 4G is
OOM-killed) now reaches phase3 HIR of `main`, then fails in
`driver_hir_pipeline_lowering.spl:549`: `driver_publish_reverse_reference_parse_scope_v1`
returns false (seal / `driver_end_transient_parse_scope` / publish; which step is
not yet isolated). Those paths assume native transient-arena runtime semantics.
`test --coverage` therefore still reports Files tracked: 0.
