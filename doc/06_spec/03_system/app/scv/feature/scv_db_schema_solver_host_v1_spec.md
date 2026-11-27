# Shared DB schema solver host: authored manual

Source: `test/03_system/app/scv/feature/scv_db_schema_solver_host_v1_spec.spl`.
Status: authored expected behavior; not generated, executed or qualified. Admitted runtime, native SPipe/docgen and coverage evidence remain unavailable.

1. Setup the historical schema, original signed-envelope bytes and explicit historical V1-to-V2 binding.
2. Add different columns independently on two sides. Call the actual V2 schema solver through the shared host.
3. Inspect the three-column draft, rename the original column, and adapt a real old-schema edit to the same column UID. Original patch bytes, digest and signature survive.
4. Inspect host-owned exact-subject check requirements and `needs_inputs` for unavailable executing-provider identity and validators. No result is cache-admitted.
5. Independently create same-name columns and inspect typed schema conflicts retaining all three original schemas.
6. Substitute a source provider or different actual schema bytes; inspect refusal without text fallback. Oversized metadata and deeply nested defaults refuse before canonical encoding.

These scenarios prove no row admission, DB settlement, persistent conflict storage, executing-provider artifact qualification or operational deployment.
