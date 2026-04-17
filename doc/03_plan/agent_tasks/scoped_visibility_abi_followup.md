# Scoped Visibility ABI Follow-up

Status: partially implemented

Scoped visibility now survives the active Simple parser/HIR/desugar path, but the external query contract still flattens access to `is_public`.

Implemented so far:
- `src/compiler/90.tools/query_types.spl` now defines additive scoped-visibility transport types:
  `VisibilitySurface`, `DeclaredVisibility`, `VisibilityMetadata`, `SymbolV2`, `ScopeV2`, `DefinitionResultV2`.
- `src/compiler/90.tools/ffi_gen/specs/compiler_query.spl` now declares additive v2 query externs and payloads.
- `src/compiler/90.tools/query_helpers.spl` now provides compatibility adapters that upgrade legacy bool-only `Symbol` values into `SymbolV2`.
- `src/compiler/90.tools/query_api.spl` now exposes additive `symbol_at_v2`, `find_definition_v2`, `document_symbols_v2`, and `workspace_symbols_v2` methods so callers can migrate without breaking the legacy query API.
- `src/compiler/90.tools/__init__.spl` now re-exports the scoped-visibility query types and v2 helper functions.
- Rust parser visibility now supports `Public`, `Peer`, `Up`, `Internal`, `Package`, and `Private`.
- Direct Rust MCP/LSP transport now exposes declared visibility strings for live symbol output.

Remaining coordinated work:
- Implement the missing Rust runtime query bridge for the `compiler_query` extern family. There is currently no `rt_find_symbol_at_position` / `rt_extract_all_symbols` implementation in `src/compiler_rust/compiler/src/ffi_bridge.rs` or another runtime bridge module.
- Add the corresponding `app.io` extern declarations or generated bindings for the additive v2 query functions once the Rust bridge exists.
- Switch higher-level query and LSP callers from legacy `Symbol` results to the new `query_api` v2 methods where structured visibility materially improves behavior.
- Review `src/compiler/90.tools/api_surface.spl`, `src/compiler/90.tools/symbol_analyzer.spl`, and ranking/filtering helpers so scoped visibilities stop being reduced to `is_public`.
- Add executable end-to-end coverage for the Rust-side scoped parser tests currently placed under `src/compiler_rust/test/`; that crate is not a workspace member yet, so those tests are not reachable from the normal Cargo workspace runs.

Acceptance for the ABI slice:
- Hover/completion/document-symbol/workspace-symbol surfaces can distinguish `public`, `peer`, `up`, `internal`, `package`, and `private`.
- No Rust/FFI caller depends on `is_public` as the sole visibility signal.
- Compatibility behavior for `peer` warnings remains unchanged.
- The self-hosted query runtime can materialize `SymbolV2` through `app.io`, not just through the direct Rust MCP/LSP path.
