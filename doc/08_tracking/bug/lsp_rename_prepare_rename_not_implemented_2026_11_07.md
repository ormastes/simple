# LSP server has no textDocument/rename, prepareRename, organizeImports or extract handlers (-32601)

- **Filed:** 2026-11-07 (L2 tools batch; no prior record existed — this record
  created by the 2026-11-13 P3 tools lane from the batch title)
- **Status:** FIXED (2026-11-13, P3 tools lane) for prepareRename; rename was
  already implemented; organizeImports/extract remain open feature requests
- **Server:** `std.nogc_sync_mut.lsp` (the std LSP server behind
  `src/lib/nogc_sync_mut/lsp/main.spl`, the one that exposes
  `simple/refactor/closure`)

## Triage 2026-11-13 (P3 tools lane, work/p3-tools-20261113, base origin/release/1.0.0)

The batch title is partially stale against current release/1.0.0:

- `textDocument/rename` **is implemented**: `lsp_handle_rename`
  (`src/lib/nogc_sync_mut/lsp/lsp_handlers.spl`, dispatched at
  `src/lib/nogc_sync_mut/lsp/main.spl`), advertised as
  `renameProvider: true` (boolean, pinned by
  `test/01_unit/app/lsp/rename_formatting_spec.spl`).
- `textDocument/prepareRename` was **missing** — it fell into the
  unknown-method `-32601` branch (`main.spl` else-arm), which clients that
  probe prepareRename surfaced as a hard rename failure.

## Fix (this lane)

- Added `lsp_query_word_span_at_v1` (`src/lib/nogc_sync_mut/lsp/lsp_query_symbol.spl`):
  identifier word + 0-based half-open span at a 1-based line/col, same scan
  alphabet/bounds as `lsp_query_symbol_at_v1` so the two cannot disagree.
- Added `lsp_handle_prepare_rename` (`lsp_handlers.spl`): returns
  `{range, placeholder}` for the identifier at the cursor, or JSON `null` on a
  non-identifier position.
- Dispatched `textDocument/prepareRename` in `main.spl`.
- `renameProvider` stays boolean `true` (object form would break the pinned
  capability-type spec); answering prepareRename without advertising
  `prepareProvider` is harmless for gate-compliant clients and fixes the
  -32601 for probing clients.

## Verification

- `test/01_unit/app/lsp/rename_formatting_spec.spl`: 6/6 PASS (added two cases:
  range+placeholder at a call site; JSON null on whitespace).
- `test/01_unit/app/lsp/server_capabilities_spec.spl`: 38/38 PASS.
- Canary `test/02_integration/app/context_log_modes_spec.spl`: 4/4 PASS.

## Remaining (separate feature requests, not bounded fixes)

- `source.organizeImports` code action: no import-organizing edit provider
  exists in-tree; a truthful implementation needs a real organizer, not an
  empty edit.
- Extract-method / extract-variable refactor handlers: only
  `simple/refactor/closure` exists; generic extract needs the fix engine.
