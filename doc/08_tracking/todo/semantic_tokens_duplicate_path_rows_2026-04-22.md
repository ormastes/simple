# semantic_tokens_duplicate_path_rows

Date: 2026-04-22
TODO rows: 11, 12
Status: fixed

## Research

Rows 11 and 12 point at two symlinked app paths for the same semantic-token handler. `src/app/lsp` resolves to the LSP implementation under `src/lib/nogc_sync_mut/lsp`, and `src/app/lsp.handlers` resolves to the same handlers tree. The canonical implementation is `src/lib/nogc_sync_mut/lsp/handlers/semantic_tokens.spl`.

## Plan

Close the duplicate tracker rows as stale path duplicates. Treat any future native tree-sitter FFI work as a separate task against the canonical lib handler path, not as two app-path TODO rows.

## Fix

Closed rows 11 and 12 with issue key `semantic_tokens_duplicate_path_rows`.

## Verification

- Confirmed both rows now reference the closure issue and have `closed` status in `doc/08_tracking/todo/todo_db.sdn`.
