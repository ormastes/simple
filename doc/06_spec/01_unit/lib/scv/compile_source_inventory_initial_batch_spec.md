# Cold inventory initial batch

Source: `test/01_unit/lib/scv/compile_source_inventory_initial_batch_spec.spl`.
Status: authored, not executed; Phase 2 MIR blockers prevent native evidence.

The spec compares reversed unique creates against the sequential reducer,
including canonical encoded output and generation. Duplicate events, deletes,
and invalid paths must defer to sequential validation. Empty and singleton
inputs preserve their boundary behavior.

Native lifetime coverage is in `test/fixtures/scv_inventory_memory/main.spl`.
See `doc/08_tracking/bug/macos_scv_inventory_scratch_retention_2026-09-21.md`
for measured compile results and outstanding acceptance.
