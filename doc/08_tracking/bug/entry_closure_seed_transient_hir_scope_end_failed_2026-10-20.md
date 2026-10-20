# native-build --entry-closure on the seed: `transient HIR scope end failed`

Found 2026-10-20 while fixing `cannot cast object to i64` (same lane).

FIXED (this change): `cannot cast object to i64`. `driver as i64` (27 sites) and
`execution as i64` (3 sites) cast a class to its address; the seed interpreter has
no such cast and an Object address is not stable under copy-on-write. Per-compilation
pins now key on `CompilerDriver.identity_id` / `MonoArchiveExecutionV1.identity_id`
(process-unique counter, never reused, 0 = unassigned and refused at pin capture).
Follow-up FIXED: `driver_hir_archive_production_release_v1`, called at the end of
`CompilerDriver.compile()`, now drops the driver's holds, current/semantic/mono-final
pins, source-body custody and MIR declaration publication (spec:
`compiler_driver_identity_release_spec.spl`).

FIXED too: `transient HIR scope end failed`. `reverse_reference_module_seal_v1`
did `val batch = global.unwrap(); batch.sealed = true`; on the seed `unwrap()` yields
a copy, so the seal was lost and `reverse_reference_module_publish_v1` refused
(found by printing in `driver_publish_reverse_reference_parse_scope_v1`). The batch
is now stored back after mutation (no-op natively). Follow-up review found the
same loss at every other batch mutation (`facts`, `known_families`,
`incomplete_families`, `aliases`, the index, and `valid = false` on late
registration): measured through the driver publish path, publish succeeded with
facts=0 and a falsely complete family. All are stored back now (spec:
`reverse_reference_batch_writeback_spec.spl`). Not the closmem
"scope already active" fallback class.

Next layer, NOT fixed: hello with the coverage-wrapper flags (`--backend llvm
--refresh-source-authority --entry-closure --runtime-bundle core-c-bootstrap`,
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`, MemoryMax=8G; 4G is OOM-killed) now fails
in HIR of `main` with `semantic: unknown extern function: rt_enum_id` (the seed
interpreter has no such extern). `test --coverage` still gives Files tracked: 0.
