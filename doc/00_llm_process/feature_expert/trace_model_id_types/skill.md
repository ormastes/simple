# Trace model id types

Feature: validated id and path types for the traceability model.

- Types: `src/lib/common/traceability/trace_ids_v1.spl` (`TraceEntityIdV1`, `TracePathV1`, `TraceEdgeIdV1`, `TraceOriginIdV1`; one-field wrapper structs).
- Parsers return `T?` (None on invalid): `trace_entity_id_parse_v1`, `trace_path_parse_v1` in `schema.spl`. Kind/relation checks return the checked value as an Option: `trace_test_node_kind_v1`, `trace_implementation_node_kind_v1`, `trace_endpoint_relation_v1`, `trace_test_role_relation_v1`. Callers test `.is_none()` / `.is_some()`.
- `evidence.spl` `trace_text_find_v1(values, value) -> text?` replaces the bool membership test.
- `TraceEdgeOrigin` (model.spl) carries `TraceEdgeIdV1` / `TraceOriginIdV1`; the SDN wire format is unchanged (wrap/unwrap in `sdn_codec.spl`).
- `primitive_api` lint flags only pub fn signatures, not struct fields; bare fields in the other model.spl structs remain (TraceNode 62 sites, SnapshotSubject 41, TraceDiagnostic 45, TraceEdge 32, TracePolicy 29, TraceClaim 28, TraceLocator 25, TraceQuery 18, TraceOrigin 16, TraceConventionRule 13, TraceDocument 11, TraceQueryResult 9, TraceAuthority 8).
- Proof: specs under `test/01_unit/lib/common/traceability` (model_codec, resolution, query*, evidence).
