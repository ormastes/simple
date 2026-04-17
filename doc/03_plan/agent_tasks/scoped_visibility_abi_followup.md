# Scoped Visibility ABI Follow-up

Status: pending after Simple-side propagation

Scoped visibility now survives the active Simple parser/HIR/desugar path, but the external query contract still flattens access to `is_public`.

Remaining coordinated work:
- Update `src/compiler/90.tools/query_types.spl` so query/LSP symbols expose structured visibility rather than only `is_public`.
- Update `src/compiler/90.tools/ffi_gen/specs/compiler_query.spl` to match the new symbol payload.
- Update the Rust query/FFI implementation to populate the new field and preserve compatibility at the MCP/LSP boundary.
- Review `src/compiler/90.tools/api_surface.spl`, `src/compiler/90.tools/symbol_analyzer.spl`, and `src/compiler/90.tools/query_helpers.spl` after the schema change so ranking and API manifests stop treating scoped visibilities as plain private.

Acceptance for the ABI slice:
- Hover/completion/document-symbol/workspace-symbol surfaces can distinguish `public`, `peer`, `up`, `internal`, `package`, and `private`.
- No Rust/FFI caller depends on `is_public` as the sole visibility signal.
- Compatibility behavior for `peer` warnings remains unchanged.
