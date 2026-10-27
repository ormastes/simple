# SCV structural storage v1 detail design

The complete representation, integration and trust-boundary design is in
`doc/04_architecture/scv_structural_storage_v1.md`. This document identifies
implementation ownership and acceptance surfaces without duplicating that
contract.

| Module | Responsibility |
|---|---|
| `structural_span_v1.spl` | Validate canonical six-field preorder host spans, containment, leaf ancestry, sibling ordering and parser bounds. |
| `structural_store_v1.spl` | Complete-node/gap byte DAG, canonical records and secure IDs, bounded iterative parser-free decode, opaque classification, shadow equality, tree/file binding. |
| `wasm_executor.spl` | Strict lock/artifact/provider admission; no simulator-success path. |
| `store.spl`, `file_buffer.spl` | Integrate normal writes and commit restore while retaining raw content and reading old file records. |
| `maintenance.spl`, `integrity.spl` | Retain the reconstruction closure and validate linked structural data. |
| `parser_session.spl` | Preserve derived line-index fallback with an honest label after strict provider failures. |

Errors propagate through `Result`; parsing unavailability selects an opaque
unit, while storage failures abort publication. No new parser, foreign shim,
runtime fallback, codec or build-runner surface is introduced. See the
architecture document for explicit remaining provider and performance gates.
