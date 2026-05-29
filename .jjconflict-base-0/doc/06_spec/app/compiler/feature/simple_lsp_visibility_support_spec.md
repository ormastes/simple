# Simple LSP Visibility Support Specification

**Feature ID:** Simple LSP Visibility Support
**Category:** LSP / Compiler Tooling
**Live path:** `src/lib/nogc_sync_mut/lsp`

## Scope

This spec covers visibility metadata surfaced by the live Simple LSP server for:

- hover
- completion
- document symbols
- workspace symbols
- diagnostics
- semantic tokens

## Expected Behavior

### Visibility display

- `public` symbols are surfaced as externally reachable API.
- `boundary` symbols are surfaced as visible within their owning boundary, but not as external API.
- `private` symbols are surfaced as file-local or otherwise inaccessible.

### Completion and workspace symbol behavior

- Inaccessible symbols are not promoted in completion or workspace symbol results.
- Public symbols rank above boundary symbols.
- Structured visibility is included when the client negotiates support.

### Hover and definition

- Hover always includes visibility information for the target symbol.
- Go-to-definition continues to work for direct references, even when the symbol is not externally reachable.

### Semantic tokens

- Visibility-aware semantic token modifiers are emitted alongside the existing token type legend.
- Clients may use the modifiers to dim or filter non-public symbols.

## Scenarios

1. A symbol exported by a boundary manifest is returned as `public`.
2. A symbol inside a boundary but not exported is returned as `boundary`.
3. A file-local helper is returned as `private`.
4. A client without experimental capability still receives readable hover and detail text.
5. A client with experimental capability receives structured `simpleVisibility` data.
6. Diagnostics are produced for illegal access, not silently hidden.

## Non-Goals

- No new syntax.
- No friend/package enforcement changes.
- No MDSOC policy enforcement.
