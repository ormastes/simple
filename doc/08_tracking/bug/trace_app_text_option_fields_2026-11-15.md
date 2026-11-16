# Traceability app option structs still carry closed sets as text (2026-11-15)

The `primitive_api` lint only inspects `pub fn` signatures, so these were not
required by the lint slice and were left to avoid rewriting every render caller:

- `src/app/traceability/query_options_v1.spl` `TraceQueryOptionsV1`: `operation`, `kind`, `format` (now has `TraceQueryFormatV1` + parser), `snapshot`, `limit` (i64), `bug_db`.
- `src/app/traceability/cli_options_v1.spl` `TraceCliOptionsV1`: `scope`, `progress` (closed sets).
- Readers of `options.format`: `query_main.spl` (4 sites), `query_render_v1.spl:111`, `query_render_refs_v1.spl:58`, `query_render_missing_v1.spl:22`.

Unblock: retype the fields to enums and convert at the 3 render sites; no wire format changes.

Also pre-existing and untouched: `export_outside_init` errors at `cli_options_v1.spl:137` and the export lines of `structural_report_v1.spl` (other modules import these names), and 2 failing examples in `test/03_system/app/traceability/feature/traceability_capture_limits_spec.spl` ("refuses actual native find output truncated at successful exit", "rejects incomplete enumeration even with successful process status") which fail identically before and after this change.
