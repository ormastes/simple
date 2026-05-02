# Simple LSP Visibility Support Research

**Date:** 2026-03-30
**Scope:** `src/lib/nogc_sync_mut/lsp`

## Summary

The live Simple LSP server is under `src/lib/nogc_sync_mut/lsp/`, with request handlers in `handlers/*.spl`, a lightweight query runner in `lsp_query.spl`, and shared query types in `src/compiler/90.tools/query_types.spl`.

Current behavior is mostly textual:

- `hover` and `completion` show type/doc strings only
- `documentSymbol` and `workspace/symbol` are built from query output without structured visibility metadata
- `semantic_tokens` exposes syntax categories, but not visibility

The compiler already has richer visibility knowledge in:

- `doc/07_guide/language/module_system.md` for boundary/export rules
- `src/compiler/00.common/dependency/visibility.spl`
- `src/compiler/35.semantics/visibility_checker.spl`

That makes the best seam a query-layer visibility payload consumed by the live LSP, rather than handler-local heuristics.

## Findings

- The LSP server path is already separated from the older `src/app/lsp/` docs.
- `workspace/symbol` and `documentSymbol` need visibility-aware filtering/ranking to avoid surfacing inaccessible symbols first.
- The compiler has enough metadata to support a hybrid model: public/boundary-private for UX, with optional richer `internal/package/friend` fields when available.
- Semantic tokens can carry visibility as token modifiers without changing syntax or parser behavior.

## Recommendation

Use a layered model:

1. Query API computes visibility once.
2. LSP serializes it in `detail`, hover text, and optional structured fields.
3. Semantic tokens encode visibility modifiers for UI styling.
4. MDSOC data is attached only as provenance, not as the access-control source of truth.
