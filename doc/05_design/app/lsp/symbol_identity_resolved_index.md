# LSP symbol identity, resolved index, trace sharing and parity

## 1. Status and scope

Status: design only, no code (2026-11-06). Base: `release/1.0.0`.
Covers four not-started structural todo items:

- L11 symbol identity (`LspSymbolKeyV1` plus snapshot-bound locator)
- L5 compiler-resolved declaration/call-edge index (the only producer of `exact`)
- L6 trace-service sharing (LSP consumes the trace query API)
- L7 parity spec (engine text == child stdout == MCP adapter text == LSP JSON)

A shared truncation/partial-result contract (section 6) ties them together. A
sibling code PR implements the partial marker for the textual engine; this
document fixes the contract the index path must honour.

Current state this design builds on:

- Wire format `name|file|def_line|site_line|site_col|resolution` is produced by
  `lsp_call_edge_format_v1` and strictly parsed (exactly 6 fields, resolution in
  `exact|bounded_set|heuristic|unknown`) by `lsp_call_edge_parse_v1`
  (`src/lib/nogc_sync_mut/lsp/lsp_call_edges.spl:166-181`).
- `exact` is documented as reserved for the resolved index
  (`lsp_call_edges.spl:6`, `src/app/cli/query_call_edges.spl:7`), and
  `lsp_call_edges_resolution_for_hits_v1` can only return `unknown`,
  `bounded_set` or `heuristic` (`lsp_call_edges.spl:157-162`).
- The textual engine identifies a function by bare name:
  `engine_outgoing_calls_lines(file, symbol)` and the incoming variant take a
  file plus a name (`query_call_edges.spl:22,70`). No kind, no module, no
  signature. Two `fn parse` in different modules are distinguishable only by
  `file`.
- LSP `CallHierarchyItem` JSON has `name, kind (12 always), detail, uri, range,
  selectionRange` and no `data` (`src/lib/nogc_sync_mut/lsp/lsp_call_hierarchy.spl:39-48`);
  `detail` carries `"resolution: <label>"` (`lsp_call_hierarchy.spl:60`).
- Query output locations are `file:line[:col]` (`LspQueryLocationV1`,
  `src/lib/nogc_sync_mut/lsp/lsp_location.spl:11-15`): no snapshot, no blob.

## 2. L11 Symbol identity

### 2.1 LspSymbolKeyV1

A stable, human-readable, content-light key:

    kind:module_path:qualified_name[:signature_digest]

- `kind`: the declaration keyword, one of `fn`, `struct`, `class`, `enum`,
  `trait`, `val`. Methods are `fn` with a qualified name `Type.method`.
- `module_path`: repo-relative file path with `/` replaced by `.` and the
  `.spl` suffix dropped, e.g. `src/lib/nogc_sync_mut/lsp/lsp_call_edges.spl`
  becomes `src.lib.nogc_sync_mut.lsp.lsp_call_edges`. It is derived from the
  path, not from `use` resolution, so the textual engine and the index compute
  it identically. Path separators are normalised to `/` first, and Windows drive
  prefixes are stripped by the same rule `lsp_location.spl:31`
  (`_has_drive_prefix`) already uses.
- `qualified_name`: `name` for top-level declarations, `Owner.name` for members.
- `signature_digest` (optional, present when overloads or same-name members can
  collide): first 12 hex chars of `sha256_text` (already used by the
  traceability code, `src/lib/common/traceability/query_refs_v1.spl:7`) over the
  normalised declaration line: comments and string bodies blanked with
  `lsp_call_edges_strip_code_v1`, whitespace runs collapsed, trailing `:`
  removed. The digest disambiguates; it is not an integrity check. It changes
  when the signature changes, which is intended: a signature change is a
  different symbol for call-edge purposes.

The key is stable across line moves inside a file and across whitespace and
comment edits; it changes on rename, file move, kind change or signature change.
Rename and move tracking are non-goals (section 7).

### 2.2 Snapshot-bound locator

A key names a symbol; it does not say which bytes it was computed from. Pair it
with a locator using the trace model's vocabulary (`TraceLocator{entity_id,
path, locator_kind, locator, blob_id}` and `SnapshotSubject.snapshot_id`,
`src/lib/common/traceability/model.spl:67-135`):

    LspSymbolLocatorV1 { snapshot_id, path, blob_id, line, col }

- `snapshot_id`: the snapshot the LSP session resolved against, or `""` for an
  unversioned worktree read (preview).
- `path`: repo-relative, `/` separators.
- `blob_id`: content id of the file as read (git blob id for a clean tree,
  `sha256:`-prefixed hash of the bytes otherwise; the prefix distinguishes them).
- `line`, `col`: 1-based, matching the existing wire columns; the LSP layer
  converts to 0-based exactly as `lsp_call_hierarchy_calls_json_v1` does today
  (`lsp_call_hierarchy.spl:62-66`).

Staleness rule: a consumer holding `{key, locator}` compares `locator.blob_id`
with the current blob of `locator.path`; on mismatch line/col are advisory only
and the key is re-resolved by name.

### 2.3 Transport: `CallHierarchyItem.data`, never in-place widening

LSP 3.17 gives `CallHierarchyItem` an opaque `data?: LSPAny` slot that clients
echo back in `callHierarchy/incomingCalls|outgoingCalls`. The key and locator
travel there:

    "data": {"symbolKey": "fn:src.app.cli.query_call_edges:engine_outgoing_calls_lines",
             "locator": {"snapshotId": "...", "path": "...", "blobId": "...",
                         "line": 22, "col": 4}}

`lsp_call_hierarchy_request_item_v1` already parses `params.item`
(`lsp_call_hierarchy.spl:19-32`); it gains an optional `data.symbolKey` read and
keeps the uri/selectionRange fallback so clients that drop `data` still work.

Wire format v2 for the query child and MCP adapter:

    name|file|def_line|site_line|site_col|resolution|key

Rules:

1. v1 lines (6 fields) keep parsing. `lsp_call_edge_parse_v1` today returns nil
   unless `parts.len() == 6` (`lsp_call_edges.spl:174`); the change is one
   parser accepting 6 or 7 fields, `LspCallEdgeV1` gaining `key: text`
   defaulting to `""`, and every existing field position left untouched.
2. The key must not contain `|`. Qualified names and module paths are
   `[A-Za-z0-9_.]` with `:` separators, so this holds; the formatter asserts it
   and omits the 7th field rather than emit an ambiguous line.
3. `lsp_call_edge_format_v1` emits 6 fields when `key == ""` (every current
   textual caller and existing golden output stays byte-identical) and 7 when a
   key is present.
4. The textual engine MAY populate `key` for the declaration it found (kind from
   the declaration line, module_path from the path) but still labels the edge
   textually. A key alone never upgrades a resolution label.

## 3. L5 Compiler-resolved index

### 3.1 Why the existing pieces cannot be the index

- The textual engine matches identifier-then-`(` on blanked lines
  (`lsp_call_edges_call_names_v1`, `lsp_call_edges.spl:66-89`). `obj.foo(1)` on
  an unrelated type matches a local `fn foo`; that is why a single hit is
  `heuristic` (`lsp_call_edges.spl:159-161`).
- The sem-query `calls` predicate is textual too: it builds the needle
  `callee + "("` and substring-matches (`src/app/cli/query_sem_query.spl:413-421`,
  predicate recognised at `:398-399`). It is not compiler-resolved and must not
  be advertised as such.
- `src/compiler/10.frontend/core/call_graph.spl` is a cycle detector for the
  baremetal `@safe` rules R1/R2 (header, lines 1-14): it finds recursion, not
  "who calls this declaration". It is not a general edge store and is keyed by
  nothing stable. It may inform the walker; it is not a base for the index.

### 3.2 Producer and storage

The producer is the frontend, after name resolution, never text:

- Per file, emit resolved declarations `{key, kind, line, col, end_line}` and
  resolved call edges `{caller_key, callee_key, site_line, site_col}` where
  `callee_key` is the key of the declaration the resolver bound the call to.
  Calls the resolver cannot bind (dynamic dispatch, unresolved import, error
  recovery) are recorded as unresolved sites with no `callee_key`; never guessed.
- Store as a content-keyed sidecar, one per source blob:
  `<index_root>/<blob_id>.sidx` (SDN, sealed with the repo's CRC32 header like
  other `*.sdn` artifacts). The cache key is the file's `blob_id`, so the index
  is valid exactly for those bytes and needs no invalidation protocol; a changed
  file has a different blob and a missing sidecar.
- Cross-file edges: the caller blob's sidecar stores the module-path-qualified
  `callee_key`, so a lookup never needs the callee file's sidecar to say
  `exact`. Resolving `callee_key` to a definition line reads the callee file's
  sidecar; if that is stale, `def_line` comes from the textual declaration scan
  (open question 1).

### 3.3 API

Unchanged: `lsp_call_edges_resolution_for_hits_v1(hits)` stays textual-only with
its three outputs. New, beside it in `lsp_call_edges.spl`:

    pub fn lsp_call_edges_resolution_from_index_v1(
        index: LspResolvedIndexV1?, caller_key: text, callee_key: text,
        site_line: i64, blob_id: text, textual: text) -> text

Returns `"exact"` only when all hold: `index` is present, `index.blob_id ==
blob_id` (the blob the engine actually read), the index is `complete`
(section 6), and it contains an edge for (`caller_key`, `callee_key`,
`site_line`). Otherwise it returns `textual` unchanged. It never returns a label
weaker than the textual one and never invents `bounded_set` or `unknown`.

Engine wiring (`query_call_edges.spl`): `_resolve_callee` and `_collect_sites`
look up the sidecar for the file they just read via `query_file_read_rich`, hash
that exact content to obtain `blob_id`, and pass the result in. The index is an
optional engine argument; absent index is the default and today's code path.

### 3.4 Staged rollout

1. Index absent (today, default): every edge keeps its textual label; nothing is
   `exact`. Existing specs and goldens stay valid.
2. Index present but `blob_id` differs from the file as read: treated as absent
   for that file; labels stay textual. A stale index never promotes.
3. Index present and matching, edge found: `exact`. Edge not found in a matching
   complete index: keep the textual label (the textual engine may see a call the
   resolver lost); do not demote to `unknown`, since absence from the index is
   not evidence of absence.
4. Later, out of scope: a matching complete index suppresses textual false
   positives, only behind an explicit flag, since it changes result sets rather
   than labels.

## 4. L6 Trace-service sharing

The traceability query service is owned by another lane. The LSP consumes it and
never edits it.

Entry points (read-only):

- `trace_query_build_snapshot_v1(options)` builds the snapshot/graph
  (`src/app/traceability/query_main.spl:4,36`).
- `query_trace_references_v1(graph, TraceReferenceQueryV1{snapshot_id, kind,
  selected_id, limit, cursor})` returns a `TraceReferencePageV1` with
  `references`, `total_count`, `next_cursor`, `complete`, `locators`,
  `diagnostics` (`src/lib/common/traceability/query_refs_v1.spl:12-50`).
- The CLI shape (`simple trace ... refs`; exit 0 complete, 1 incomplete, 2
  error; `query_main.spl:41-75`) is the process-level contract if the LSP must
  shell out instead of linking the library.

Mapping an LSP location to a `TraceLocator`:

    LspSymbolLocatorV1.path      -> TraceLocator.path
    "line"                       -> TraceLocator.locator_kind
    str(LspSymbolLocatorV1.line) -> TraceLocator.locator
    LspSymbolLocatorV1.blob_id   -> TraceLocator.blob_id
    (resolved entity)            -> TraceLocator.entity_id

The match is on (`path`, `locator_kind == "line"`, `blob_id`); a locator whose
`blob_id` differs from the file's current blob is stale and ignored (same rule
as 2.2). `LspSymbolLocatorV1.snapshot_id` must equal
`graph.subject.snapshot_id`.

Honest gap: `TraceNode`s are features, requirements, tests and similar
(`TraceNode{id, kind, title}`, `model.spl:98-101`; `TraceTestDefinition`
carries test node ids), not code symbols. `TraceLocator.entity_id` points at a
trace entity, so a code location only maps to a trace node when something
declares that edge. Two ways, neither existing yet:

1. Declaration-level `@req` / `@trace` tags that the trace capture lane extracts
   as claims with `locator_kind: "line"` on the tagged declaration; the LSP then
   joins by (`path`, `line`, `blob_id`).
2. The L5 index: join `symbolKey` to trace claims by key, which also survives
   line moves. This needs the trace lane to accept a `symbolKey` locator kind;
   that is a request to that lane, not an LSP change.

Until one lands, the LSP surfaces only what the trace graph already says about a
file path (tests and requirements located in that file) and labels nothing as
symbol-level.

Rules for the LSP side:

- No graph traversal in the LSP (the traceability design keeps traversal inside
  the query service). It calls `query_trace_references_v1` for the selected id
  and renders the page; further pages use `next_cursor` (limit 1..200,
  `query_refs_v1.spl:44-47`).
- `complete == false` on the snapshot (`TraceGraph.complete`, `model.spl:145`;
  CLI exit 1) or on the page (`TraceReferencePageV1.complete`) is a partial
  result and surfaces through the section 6 marker, never as a full list.
- Trace results are structural and unverified in the default worktree preview
  (`query_main.spl:68-70`); the LSP must not present them as admitted evidence.

## 5. L7 Parity spec

One test, one fixture, four views of the same answer.

Location: `test/01_unit/app/lsp/parity_spec.spl`, beside the existing
`call_hierarchy_spec.spl`.

Fixture: three `.spl` files under the spec's temp dir:

- `a.spl`: `fn caller()` calling `callee()` twice (two sites) and a name that is
  declared in two other files (yields `bounded_set`).
- `b.spl`: `fn callee()` and `fn dup()`.
- `c.spl`: a second `fn dup()` and a call with no declaration (`unknown`).

Assertions, for outgoing and incoming on `caller` and `callee`:

1. Engine: `engine_call_hierarchy_lines(file, symbol, direction)` lines
   (`query_call_edges.spl:118`).
2. One-shot child: stdout of the `call-hierarchy` query child, byte-identical to
   (1) joined with `\n`. This is the contract `query_call_edges.spl:3-5` already
   states: each `engine_*_lines` returns its lines so the in-process MCP adapter
   and the one-shot child print byte-identical text.
3. In-process MCP adapter text: byte-identical to (1).
4. LSP handler JSON: decode the `callHierarchy/*Calls` response and map each
   `from`/`to` item plus `fromRanges[0].start` back to (`file` from `uri`,
   `line = start.line + 1`, `col = start.character + 1`, `resolution` from the
   `detail` text after `"resolution: "`); compare as a sorted tuple set against
   `lsp_call_edges_parse_output_v1(text)`. The decode inverts
   `lsp_call_hierarchy_calls_json_v1` (`lsp_call_hierarchy.spl:55-70`); edges
   with `def_line == 0` compare on the site tuple only, matching the builder's
   clamp to line 0.

v2 additions: when `key` is populated the tuple gains `key`, read on the LSP
side from `item.data.symbolKey`. A v1-only fixture variant asserts 6-field
output is unchanged (no trailing `|`).

Binary dependence: views 1, 3 and 4 run in-process and need no binary. View 2
(child stdout) and any stdio MCP round trip need a built binary and are gated on
`SIMPLE_LSP_MCP_TEST_BINARY`; when unset those examples are reported skipped
with that reason, never passed. A missing binary must not silently shrink the
parity claim; the spec prints which views ran.

The spec also pins the section 6 contract with a fixture whose bounded search is
forced to truncate via a tiny budget, asserting the note line in the text views
and the sentinel entry in the JSON view.

## 6. Truncation and partial-result contract

Today the textual engine reports incompleteness as a trailing note line in the
text output: `[search truncated: <reason> after ...]` or `[more than N matches
...]`, from `lsp_bounded_search_truncation_note_v1`
(`src/lib/nogc_sync_mut/lsp/lsp_bounded_search.spl:297-300`), appended by
`engine_incoming_calls_lines` (`query_call_edges.spl:92-96`). That line is not a
parseable edge: `lsp_call_edge_parse_v1` returns nil for it and
`lsp_call_edges_parse_output_v1` silently drops it, so an LSP client sees a
truncated list as complete.

Contract (shared by textual, index and trace paths):

- Text surfaces (engine, child, MCP adapter) keep the note line verbatim, last
  in the output. It remains the human-readable form and the parity anchor.
- LSP surfaces represent partiality with a sentinel
  `CallHierarchyIncomingCall` / `OutgoingCall` entry whose item has
  `name: "[partial result]"`, the note text in `detail`, the request item's
  `uri` with a zero range, and `fromRanges: []`. It is the last element. It is
  not a real symbol: its `data` is `{"partial": true}` with no `symbolKey`, and
  clients and the parity decoder filter it out of symbol comparisons.
- This is being implemented in a sibling code PR; this document fixes the names
  and shape so the index and trace paths reuse them.
- The index path sets the same marker when the index itself is incomplete: a
  sidecar missing for a file the textual walk visited (note:
  `index: N of M files covered`), a sidecar with `complete=false`, or a
  budget-truncated walk. Individual matching edges may still be `exact`, but the
  result carries the marker so a partial index never yields a bare list that
  looks complete.
- Trace results set the marker when `TraceGraph.complete` or
  `TraceReferencePageV1.complete` is false, or `next_cursor` is non-empty and
  the LSP chose not to page further; the note names which.
- The trace CLI returns 1 for "rendered but incomplete" (`query_main.spl:56,74`);
  the LSP maps that to the marker, not to an error.

## 7. Risks, non-goals, open questions

Risks:

- Parser widening (6 or 7 fields) touches every consumer. Mitigation: the key is
  the last field, 6-field output is unchanged when no key exists, and the strict
  resolution whitelist check stays.
- Key collisions: two declarations with the same kind, module and qualified name
  (overloads, conditional declarations) are separated only by the signature
  digest; identical signatures collide and are reported as `bounded_set` by the
  index, never merged.
- Index cost and freshness: per-blob sidecars multiply with history and need a
  bounded cache with eviction. Not designed here.
- `exact` for cross-file edges whose callee sidecar is stale (open question 1).
- Trace-lane coupling: both mapping options in section 4 need the trace lane to
  add something; if it declines, L6 degrades to path-level results only.

Non-goals:

- No rename/move tracking, no fuzzy re-matching of keys across edits.
- No change to the trace query service, its SDN formats or its CLI.
- No promotion of `query_sem_query.spl` `calls` or `call_graph.spl` into the
  index (section 3.1).
- No demotion of textual results when an index is present (stage 4).
- No type-based dispatch resolution beyond what the frontend resolver binds.

Open questions:

1. Is an edge `exact` when the caller blob matches but the callee file's sidecar
   is stale or absent? Proposed: yes for identity, with the partial marker set
   and `def_line` taken from the textual scan.
2. Where does the index live and who builds it: a frontend pass during `check`,
   a lazy build on first LSP query, or a watcher? The sidecar path convention
   depends on this.
3. `blob_id` for dirty worktree files: git blob id of the unsaved content, or a
   sha256 of editor buffer bytes? The prefix rule in 2.2 allows both, but the
   trace lane's snapshot mode must agree.
4. Should `signature_digest` be mandatory for kind `fn` to avoid later key churn
   when an overload appears? A mandatory digest makes every signature edit a key
   change.
5. Does the LSP take `snapshot_id` from the trace lane's snapshot builder or
   mint its own for non-git workspaces?
