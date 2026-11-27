# Source-view foundation detail design

Status: authored, execution unverified.

- `source_project_ranges_v1(snapshot, selections, max_bytes)` rejects unordered/overlapping/out-of-bounds/split-UTF8 selections. It returns concatenated exact selected bytes, ordered source ranges and every omitted range. It reports raw-text evidence, never resolved semantics.
- `source_project_raw_v1(snapshot, start_byte, max_bytes)` accepts only whole-line cursors, keeps newline bytes and returns `next_byte = -1` at EOF. Empty input is complete and valid. A continuation still has prior omitted ranges, so EOF does not incorrectly make a partial page complete.
- `source_view_session_new_v1` requires host-supplied workspace and authenticated binding values. `source_view_set_preferences_v1` uses a monotonic request sequence and expected preference version. Repeated matching requests do not mutate twice; payload mismatches and stale versions fail. Only 64 receipts are retained; older retries explicitly expire.
- `source_view_commit_open_v1` consumes first-help state only on successful open. The caller must commit returned state atomically; pure transitions do not supply concurrency control or authentication.
- `source_open` parses strict typed JSON, bounds inputs, validates workspace-relative paths, reads bounded bytes, validates UTF-8, hashes path/content and applies the shared raw projection. It returns explicit unsupported/stale/denied/error states through MCP `isError`.

Shared interfaces: `SourceSnapshotV1`, `SourceRangeV1`, `SourceProjectionV1`, `SourceViewPreferencesV1`, `SourceViewSessionV1`. Manual step names describe projection, cursor validation and preference commits rather than implementation helpers. Tests assert independent expected strings/offsets and negative outcomes; there are no placeholder passes.

Focused specs: `test/01_unit/lib/source/source_view_foundations_spec.spl` and `test/01_unit/app/mcp/source_open_contract_spec.spl`. They are unit/handler evidence, not public process lifecycle, real concurrent first-open, backend parity or release proof. Admit a pure-Simple full CLI before executing these and generating the mirrors. Then run the applicable compiler/lib/MCP/LSP checks, native smoke, stdio integration and whole release suite.
