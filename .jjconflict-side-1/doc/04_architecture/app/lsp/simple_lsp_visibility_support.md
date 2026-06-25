# Simple LSP Visibility Support Architecture

**Live path:** `src/lib/nogc_sync_mut/lsp`

## Summary

Add visibility support by extending the compiler query layer first, then consuming the richer results from the live LSP handlers.

The live server currently routes most code-intelligence operations through `lsp_query.spl` and query helpers. That makes the safest architecture:

1. compute visibility in `src/compiler/90.tools/query_api.spl` and `query_types.spl`
2. serialize visibility in the live LSP handlers
3. keep the LSP layer thin

## Layering

- Query layer owns visibility truth, ranking, and filtering.
- LSP layer owns protocol negotiation and JSON shaping.
- Semantic-token layer owns visibility modifiers for editor styling.
- MDSOC data is optional provenance only.

## Data Flow

1. `documentSymbol`, `workspace/symbol`, `completion`, and `hover` call into the query API.
2. Query results carry structured visibility metadata.
3. LSP handlers map that metadata to standard fields plus optional `simpleVisibility`.
4. Clients without support still get readable `detail` strings.

## Protocol Strategy

- Use an experimental capability handshake for structured visibility.
- Keep `detail` and hover prose as the fallback path.
- Include visibility modifiers in the semantic-token legend so clients can dim or filter symbols consistently.

## Constraint

Do not move access-control policy into the LSP handlers. The handlers should not independently infer visibility from file names or tree-sitter shape when the compiler/query layer can already answer the question.
