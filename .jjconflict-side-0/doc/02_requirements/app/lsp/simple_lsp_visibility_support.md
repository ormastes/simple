# Simple LSP Visibility Support Requirements

**Feature:** Simple LSP Visibility Support
**Status:** Draft
**Live path:** `src/lib/nogc_sync_mut/lsp`

## Goal

Expose Simple visibility information through the live LSP server so editors can show, filter, and rank symbols by reachability without relying on ad hoc handler heuristics.

## Functional Requirements

- REQ-LSPVIS-001: The server shall expose visibility metadata for symbols returned by completion, hover, document symbols, workspace symbols, and diagnostics.
- REQ-LSPVIS-002: The server shall distinguish at least `public`, `boundary`, and `private` visibility for user-facing display.
- REQ-LSPVIS-003: The server shall preserve richer compiler visibility when available, including `internal`, `package`, and `friend` as optional structured fields.
- REQ-LSPVIS-004: The server shall filter completion and workspace symbol results so inaccessible symbols are not presented as primary results.
- REQ-LSPVIS-005: The server shall continue to resolve hover and go-to-definition for explicit references even when the target is not reachable from the current scope.
- REQ-LSPVIS-006: The server shall emit semantic-token visibility modifiers for styling and dimming.
- REQ-LSPVIS-007: The server shall keep diagnostics as the enforcement channel for illegal access.
- REQ-LSPVIS-008: The server shall support capability-negotiated structured visibility metadata and degrade cleanly to text-only output.

## Out of Scope

- No new source-language visibility syntax.
- No new friend/package semantics in the parser.
- No MDSOC policy enforcement in v1.

## Acceptance

- A symbol that is exported through a boundary manifest appears as `public`.
- A symbol that is reachable only within its owning boundary appears as `boundary`.
- A file-local symbol appears as `private`.
- Clients without extension support still see usable `detail` and hover text.
