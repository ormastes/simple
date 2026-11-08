# LSP revision-bound code actions

The live full-sync notifications now update the existing `LspServer` document
owner through `lsp_document_sync`. `didOpen` retains URI, integer version and
exact content (including empty text); `didChange` accepts only newer versions
and validates all full replacements before updating; `didClose` evicts the
record. Malformed newer changes retain the last accepted content/version but
revoke synchronization authority. Only a valid full synchronization at or after
the newest observed version restores it. A stale lower revision cannot restore
access. Malformed input without a recoverable URI does not invalidate unrelated
documents. No second overlay registry or filesystem writer is introduced.

The owner admits at most 256 documents, 1 MiB per document, 16 MiB total retained
source, and 4 KiB per URI. Replacement and close reclaim the byte budget; an
oversized newer change revokes authority without retaining its source. These
are retained-state ceilings, not a claim that protocol input parsing itself is
allocation-bounded.

## Query and application authority

`lsp_code_action_handler` captures an open document revision. The current query
backend reads disk, so the adapter requires equality with the captured editor
bytes before querying and again before response. Both disk reads and the
new synced-diagnostic preflight use the canonical regular-file, no-follow,
1 MiB bounded read with UTF-8 decoding; a file that grows after open cannot
force an unbounded comparison allocation. Refusal remains explicit. It also checks that the
editor owner still matches. Unsaved editor text returns an explicit error;
disk-derived fixes are never passed off as overlay analysis.

Before/after equality is insufficient by itself: a file can change and revert
while a child runs. Actual source-generated query actions therefore carry
`data.simpleSourceSnapshots`, containing each source path and its canonical
EasyFix `snapshot_version` SHA-256 identity. The adapter requires exactly one
matching stamp for every edited URI and compares it to the exact captured
source. This is a trusted local child contract, not cryptographic provider
authentication. Missing, duplicated or mismatched stamps disable the action.

The producer chain is `collect_fixes_from_source` → `fix_unit_from_source` →
`source_snapshot` → `run_fix_producers`. Producers consume the supplied unit
source; each proposal is bound to that snapshot's version. Query emission also
requires the proposal version to equal the source map's version. Constructor
and pass edits use that same map. The separate earlier `check_file` call emits
no-edit diagnostic suggestions, which remain disabled; its timing is not
misrepresented as the edit source identity.

Each `documentChanges` entry carries the captured editor version. A producer's
existing integer version must agree; it is never silently overwritten when
stale. Every targeted URI requires its own analyzed revision. The current
single-file query route supplies only its requested document; future
multi-file providers must supply all immutable revisions and stamps.

The converter preserves empty deletion text and every valid replacement. It
rejects malformed edits, invalid UTF-16 boundaries, out-of-source ranges,
overlap, shared insertion points and repeated document entries atomically.
An unusable action carries a disabled reason, `isPreferred=false`, and neither
an edit nor a follow-up command. Preferred remains metadata, not permission to
apply. Wire admission caps are 256 replacements per document and 64 documents
per action; the bounded pairwise overlap check cannot scan arbitrary edit
counts. The live query additionally admits at most 128 actions and a 4 MiB
result, reporting over-budget responses as analyzer failures. Each admitted
revision's line map and canonical digest are computed once per conversion,
then reused across its actions. Explicit byte lengths enforce Unicode source
and URI quotas; scalar-character counts are not used as byte budgets.

The editor remains responsible for version-checked application. The shared
compiler `validate_fix_proposals` remains the source-edit/reparse owner for
compiler fix routes. This adapter does not add another apply transaction,
claim client rollback, or claim successful repair after analysis failure.

## Remaining work and verification

Full FIX-01 through FIX-07 acceptance is NOT established. Unsaved-overlay
compiler queries, client partial-application outcomes/rollback, versioned
cross-file analysis, diagnostic freshness after analyzer failure, and public
protocol execution remain open. Runtime checks and generated-manual admission
are pending an admitted full pure-Simple runtime.

Relevant executable specs:

- `test/01_unit/app/lsp/document_sync_spec.spl` replaces the previous skipped
  placeholder with actual owner/notification assertions.
- `test/01_unit/app/lsp/code_action_revision_spec.spl` covers exact versions,
  deletion/multiple edits, source stamps, per-URI bindings, stale versions,
  overlaps, malformed later edits and UTF-16 boundaries.
- Existing code-action wire and deletion roundtrip specs retain compatibility
  checks; malformed replacements now require explicit disabled results.

## Scoped integration status

The canonical LspServer is the single live document owner. Public notification handlers delegate to it; didOpen suppresses disk-derived diagnostics when the unsaved editor snapshot differs from disk. Existing diagnostic infrastructure is otherwise retained; immutable overlay diagnostics remain separate work.

The live child-success path calls lsp_code_action_complete_v1 with its actual captured DocumentInfo and the exact producer source-path spelling submitted to the child. Filesystem rereads use the captured disk path; source stamps match the query's workspace-relative spelling where applicable. Close/reopen lifetime changes reject stale completion even if source and editor version are identical.

Explicit public APIs added without signature changes: LspServer, DocumentInfo and their ServerState, touched notification/codeAction handlers, and canonical lsp_json.make_json_result/make_error. No visibility baseline waiver or competing envelope serializer is introduced. Query source-fix emission additionally requires the canonical proposal base version to match its source map before stamping the action.

Runtime, docgen, external child/protocol and performance qualification: NOT_RUN. In-process completion tests use genuine ordinary producers and real files; a separate actual child-route scenario requires SIMPLE_BINARY. Source review does not execute it or complete FIX-01–07.

The actual code-action query passes a 4MiB capture ceiling to the canonical process runner before output allocation. Because its tuple return lacks a truncation bit, reaching the exact stdout or stderr ceiling fails closed, even if captured text is valid JSON. Other query callers retain the existing unlimited-output default. The real child-output fixture and public query path are isolated in test/02_integration/app/lsp/revision_code_action_child_spec.spl, with a60s child watchdog and explicit admitted SIMPLE_BINARY requirement; this integration remains NOT_RUN.
