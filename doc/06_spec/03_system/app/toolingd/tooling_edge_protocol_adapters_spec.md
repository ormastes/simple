# Toolingd Edge Protocol Adapters

## Requirement

`REQ-KPF-IDE-EDGE-001`: toolingd exposes LSP diagnostics/code actions and a
minimal test protocol as JSON edge projections over typed document sessions.

## Scenarios

1. Protocol versions are negotiated before a connection is allocated.
2. Content-Length framing rejects malformed JSON and incomplete payloads.
3. Stale revisions and cancelled requests cannot publish results.
4. Typed diagnostics and fixes project to LSP diagnostics and code actions.
5. LSP and test requests for the same snapshot share one analysis ticket.

## Ownership

JSON exists only in `src/app/toolingd/protocol_adapters`. The daemon session,
revision, digest, cancellation, diagnostic, and fix records remain typed.
