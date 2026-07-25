# Simple LSP Visibility Support NFRs

**Feature:** Simple LSP Visibility Support
**Status:** Draft

## Performance

- NFR-LSPVIS-001: Visibility metadata must be computed with the same cached query path used for the rest of the LSP server.
- NFR-LSPVIS-002: Completion and hover should remain interactive for normal files; visibility annotation must not require a full project scan on each request.

## Compatibility

- NFR-LSPVIS-003: The server must continue to work for existing clients that only read `detail`, hover text, and standard LSP fields.
- NFR-LSPVIS-004: Experimental structured fields must be additive and ignorable by clients that do not recognize them.

## Reliability

- NFR-LSPVIS-005: If visibility cannot be computed, the server should fall back to text-only annotations rather than failing the request.
- NFR-LSPVIS-006: Diagnostics must remain stable and deterministic for the same source input.

## UX

- NFR-LSPVIS-007: Public symbols should rank above boundary/private symbols in workspace search.
- NFR-LSPVIS-008: Visibility should be visible in hover and outline views without forcing clients to parse prose.

## Testability

- NFR-LSPVIS-009: The implementation must have unit coverage for visibility serialization and filtering.
- NFR-LSPVIS-010: The implementation must have an integration spec for the live LSP path under `src/lib/nogc_sync_mut/lsp`.
