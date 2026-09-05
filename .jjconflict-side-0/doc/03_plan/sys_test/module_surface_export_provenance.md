# Module Surface Export Provenance Test Plan

## Scope and traceability

| Scenario | Requirements |
|---|---|
| Direct named re-export reports canonical owner | REQ-001, REQ-003 |
| Aliased export preserves public and original names | REQ-001, REQ-003 |
| Physical/symlink aliases coalesce | REQ-002, REQ-008 |
| Package `__init__`, relative, glob, and multi-hop facades resolve | REQ-003 |
| Cycle, missing source, and competing owners fail deterministically | REQ-004 |
| Direct dictionaries/bodies are not duplicated | REQ-005 |
| Explicit and glob registration agree | REQ-006 |
| Streaming, retained, and C-entry construction finalize maps | REQ-007 |
| Existing imports remain green | REQ-008 |
| Future graph seam remains source-compatible | REQ-009 |

## Planned executable evidence

Extend focused unit specs:

- `test/01_unit/compiler/hir/module_surface_spec.spl`
- `test/01_unit/compiler/hir/resolve_import_symbols_spec.spl`
- `test/01_unit/compiler/driver/driver_source_loading_spec.spl`
- `test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl`
- `test/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.spl`

Add system scenario
`test/03_system/compiler/module_surface_export_provenance_spec.spl` with manual
steps frozen before sidecar work:

1. `Build canonical module surfaces`
2. `Resolve named and aliased facade exports`
3. `Resolve package and glob exports`
4. `Reject ambiguous or cyclic provenance`
5. `Compare Stage 4 diagnostic fan-out`

Helpers: `setup_surface_fixture`, `check_export_origin`,
`check_provenance_failure`, `check_stage4_fanout`. Until implemented, helpers
must fail explicitly with `assert(false)`; no placeholder passes.

## NFR evidence

- Stable results under reversed source insertion order.
- Linux path, Windows separator, repository symlink alias fixtures.
- Stage 4 elapsed time/max RSS before and after; ceilings from NFR-002/003.
- Debug counters prove zero ambiguity suppression and eventually zero fallback.
- Compare exact diagnostic families and file fan-out, not only total count.

Run each acceptance check at most once per session and stop on convergence.
