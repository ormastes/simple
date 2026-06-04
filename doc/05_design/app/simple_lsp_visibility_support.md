# Simple LSP Visibility Support Design

**Feature:** Simple LSP Visibility Support
**Live path:** `src/lib/nogc_sync_mut/lsp`

## Design

Introduce a shared visibility payload in the query API and expose it through the live LSP server.

### Core payload

- `display`: `public | boundary | private`
- `declared`: optional `public | internal | package | private`
- `reachable`: bool
- `boundary_kind`: `open | boundary | bypass`
- `boundary_module`: optional module identifier
- `exported_by`: optional manifest path or module id
- `friend_packages`: optional list
- `capsule`: optional MDSOC provenance block

### Handler behavior

- `completion`: return only reachable candidates; include visibility in `detail` and structured `data`
- `documentSymbol`: include visibility in `detail` and structured metadata when negotiated
- `workspace/symbol`: search reachable symbols only and rank `public` before `boundary`
- `hover`: always show visibility
- `definition`: do not block explicit navigation
- `semanticTokens`: add visibility modifiers for styling

### Negotiation

- Client advertises `experimental.simpleVisibility`
- Server advertises `experimental.simpleVisibilityProvider`
- Without negotiation, the server returns text-only visibility

### MDSOC usage

MDSOC data is attached only when a symbol can be mapped to a capsule. It is informative, not authoritative.

## Implementation Order

1. Extend query types and query serialization.
2. Update live LSP handlers to consume structured visibility.
3. Add semantic-token modifiers and capability wiring.
4. Keep all fallback text paths intact.
