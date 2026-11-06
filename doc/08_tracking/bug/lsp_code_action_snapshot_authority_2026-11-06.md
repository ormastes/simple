# LSP code actions lack snapshot authority — 2026-11-06

Owner: release100_memory_mcp_lsp / debug_truth.
Status: implementation prepared; executed validation pending admitted runtime.

## Exact evidence at 77b05b3

- `src/lib/nogc_sync_mut/lsp/lsp_code_action.spl:133`: generated document edits use `version: null`; malformed edits may survive as actionable-looking title-only rows.
- `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:149`: didOpen reads disk for diagnostics, ignoring editor text.
- `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:156`: didChange is a no-op although full synchronization is advertised.
- `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:729`: codeAction queries disk and passes no document revision to conversion.
- `src/lib/nogc_sync_mut/lsp/server.spl`: an existing LspServer document cache owns URI/version/content, but the live handlers do not use it.
- `test/01_unit/app/lsp/document_sync_spec.spl`: a placeholder skipped test passes on the length of its pending reason; it is not sync evidence.

## Existing owner to preserve

`compiler.tools.fix.source_edits.validate_fix_proposals` owns actual source
proposal revision, bounds, overlap and reparse validation. The LSP adapter must
not add another filesystem writer or competing transaction owner. It should
retain exact documentChanges versions so the editor can reject stale apply.
`std.editor.document.transaction` is a byte-edit skeleton, not an admitted
cross-file versioned LSP transaction engine.

## Planned boundary

Reuse LspServer for live full-sync notifications. Code actions may only bind a
disk query to an editor revision when the exact captured editor bytes equal
the analyzed disk bytes and stay unchanged until response. Unsaved overlays
must receive explicit unavailability until the compiler query accepts an
immutable overlay; disk content must not masquerade as editor analysis.
Preserve deletions and all nonoverlapping replacements; reject malformed,
overlapping, duplicate-document or stale-version edits atomically. Mark an
unusable action disabled rather than retain a title as an apparent repair.

## Required evidence

Actual owner tests must cover open/change/close, monotonic versions, empty
content, stale changes, malformed sync payloads, deletion, multiple files,
version mismatches and overlap. Public protocol execution and editor partial
application remain required; no source inspection counts as release PASS.

## Prepared change

Full-sync handlers now reuse LspServer. Exact child source stamps and per-URI
editor versions gate edits. Invalid/overlapping/stale edits disable the whole
action. The skipped document-sync placeholder was replaced with actual owner
assertions. No runtime, public-protocol, partial-application or release PASS is
claimed. Owner now bounds retained documents/bytes and revokes synchronization authority
after malformed newer updates without changing accepted content/version.
Follow-up: immutable overlay compiler query and real client application receipts.

## Static review and retained limits

Independent review identified byte-count ambiguity, repeated per-action source
hashing, same-version reopen ambiguity, malformed-row empty success, ambiguous
edit representations, raw-path retargeting and unbounded disk comparison reads.
The prepared patch addresses those with explicit byte budgets, one source map
per admitted revision, authority invalidation, strict row validation, atomic
representation rejection, exact original-path binding and canonical bounded
UTF-8 reads. Focused regressions were added; they remain unexecuted. Scoped
whitespace validation passed after the source fixes. Protocol message parsing,
full diagnostic provenance/failure handling and real client partial-apply
receipts remain separate open requirements.
