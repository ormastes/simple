# Traceability SDN structural command

Status: implementation in progress; command acceptance and broad verification unqualified. All 20 REQ-TRC / 40 AC-TRC / WP0–WP7 remain required. Dependencies are the reviewed strict/typed shared owners in PR #2959; release admission remains a separate unresolved gate.

The production main entry parses TraceCliOptionsV1 completely before capture. Default and explicit output are one canonical simple.trace.qualification summary v1 SDN document with one LF. Help is text. JSON, unknown options, malformed/missing values and unsupported scopes/formats return usage exit 2 with stderr and empty stdout. UTF-8, NUL, argument count, per-argument bytes and total argument bytes are checked before spawning or reading. Quiet preserves the document and suppresses progress regardless of flag order. Human progress uses the canonical stderr owner. CLI process status uses its exit facade.

TraceCaptureLimitsV1 / TraceCapturedInputsV1 / TraceCaptureIssueV1 and trace_capture_worktree_v1 own checked bounded worktree materialization. Selectors remain authored in the report; normalized repository-relative source/test/doc identities are retained in capture. Parent traversal/outside roots, missing inputs, unsupported selected files and observed symlinks are refused. Existing dirs must be observed real dirs before an empty enumeration can succeed. Supported files use no-follow bounded reads; every observed ancestor is checked separately. UTF-8 is validated before parsing exact captured contents.

A successful find argv call provides NUL-delimited paths. No shell command text is interpolated; relative roots are prefixed ./ and NUL is rejected in supplied arguments. The existing bounded native provider can retain child exit 0 on output truncation. Acceptance therefore requires status 0, empty stderr, byte length within cap, valid UTF-8 and complete nonempty NUL records with the expected relative-path framing. Its truncation marker adds bytes beyond its retained cap; its incomplete marker lacks terminal NUL. Filenames resembling marker text are legitimate and are not banned. Real provider overflow controls are required. Platforms lacking find produce explicit infrastructure failure; this is not proof of the remaining supported-platform contract.

Checked one-level enumeration distinguishes authorized configuration absence from unreadable/provider failures. Configuration/default policy, exact config digest and parsed semantic fields participate in identity; traceability_config_from_captured_text_v1 performs no reread. Files are sorted/deduplicated while selector order/provenance is retained. A streaming SHA-256 hashes canonical versioned header and each sorted path/length/exact-content-digest record, each LF-framed. The header includes cwd, scope, selectors, configuration/default policy and the capture/classifier/rule policy version. Both warning evaluation and rendering consume captured values without filesystem rereads.

Sequential no-follow checks and reads do not establish atomic repository coherence or descriptor-based confinement. The native reader protects only its final component; observed ancestor checks do not close replacement races. snapshot.complete means this materialization completed, not that Git/index/worktree coherence or admission was established. qualification remains incomplete at completed structural exit 0 or 1. Missing input/capture errors use incomplete snapshot/evaluation exit 2; evaluation/report-budget failures retain an already materialized snapshot but mark evaluation incomplete. Infrastructure reports contain a diagnostic reason. Full WP4 snapshot/lifecycle/admission and exact immutable receipt contracts remain open.

Captured file count/bytes, per-file bytes, enumeration bytes/entries/process count and capture checkpoints/process deadlines are bounded. In-process native reads are not preemptible; no hard whole-operation deadline is claimed. The legacy parser operates on bounded captured buffers. Before warning-producing helpers, analyze_virtual_files_bounded_v1 computes the reviewed bound B = 6F + 2L + I + T, counting files, four companion-link arrays, requirement/NFR identifiers and raw-test paths including duplicates. Remaining-budget arithmetic avoids overflow. Header/link/config paths have separate byte bounds. Rejecting the bound is incomplete evaluation, never a completed violation. The shared parsed analyzer retains all files and links; output cardinality must satisfy both B and the configured diagnostic cap. This does not qualify worst-case analysis time or RSS.

The typed summary owner validates producer output. Its effective 1 MiB cap includes LF. Arguments total at most 64 KiB, leaving space for an infrastructure summary if full diagnostic serialization refuses; no partial document is written. Diagnostics retain code, observed path identity, snapshot, rule/version, origin and repair. The legacy checker has no exact column, so span availability is false and coordinates zero. These lexical observed-path subjects are not claimed as the full extracted graph/declaration entities. Full extraction, qualification major 2 and other families remain required.

TDD baseline: after narrowing unrelated hub imports, the actual old production command constructed 53 modules without fallback. The native seven-case SSpec observed four failed scenarios, then the missing-option scenario started a full-repository scan and the 30-second harness timed out before completion. The incomplete run is retained as such; no seven-case RED summary is fabricated. Its verified orphan was terminated. This is a concrete option-validation/performance failure addressed before capture. Final command and resource/producer boundary tests are still pending.

## Final scoped status (2026-10-11)

Configuration reads are capped at1MiB, with <=4096 warning-root members, <=4KiB
per member and <=64KiB aggregate checked before manifest allocation. Public
options/limits/cwd are checked before attempt allocation. Early capture refusals
use reserved worktree-attempt:unavailable, complete=false, with no captured
identity claim. NUL records are scanned by byte offsets; exact selected-root
observation is required for unfiltered walks. These changes are source-reviewed.

The earlier CLI stage passed7/0; final capture controls remain6/1 after three
cycles (Unicode/NUL positive control). Final command construction succeeded;
full acceptance is not claimed. See traceability_cli_tdd_2026-10-11.md report.

## Fixture transport / actual provider evidence update

The prior6/1 positive control was malformed: nil-coalescing Result does not
extract a text payload. The corrected helper explicitly matches Ok and asserts
len1/bytes[0]. No original capped suite was rerun or retroactively validated.
New native fixture regression3/0 and actual provider legacy6/5 -> current6/0
qualify concrete worktree-provider properties. See the CLI TDD report for
source-stage boundaries, owned inputs and P2 oracle limitations. Direct Unicode
selection is proven; find transport of that filename remains open. All20REQ/40AC
remain required; no full runtime or protected admission PASS is claimed.

## Query entry and harness surface increment — 2026-11-06 (slice 1)

Scope statement: slice 1 ("P0 query usable on seed") changes **no module or
layer boundary, no data model, no graph schema and no SDN document shape**.
`std.common.traceability` stays the pure owner; app adapters keep snapshots,
processes and rendering. The increment adds one entry route, one harness knob
and one input-tolerance rule, each listed here so later slices align to it.

1. **Direct program entry for the query CLI.** `src/app/traceability/query_main.spl`
   exposes `fn main() -> i64` that forwards `get_cli_args()` to
   `run_trace_query_v1` and exits with its status. `<simple> run
   src/app/traceability/query_main.spl <args>` therefore has exactly the argv
   contract and exit codes of `simple trace <args>` (0 help/complete, 1
   rendered-but-unverified or `TRACE-QUERY-NOT-FOUND`, 2 error). Rationale: no
   admitted Stage4 CLI dispatches `trace`, and the Rust seed dispatches none of
   the pure-Simple commands; program-run is the delivery route on any binary
   that can `run`. The `simple trace` registration (command_registry) is
   unchanged and remains the eventual surface; `main` is additive. The
   traceability-check entry (`main.spl`) already follows this shape.

2. **Harness contract.** `trace_query_p0_spec` accepts
   `SIMPLE_TRACE_QUERY_TEST_COMMAND` -- a whitespace-split command prefix that
   already routes to the query entry (the spec appends only query args) -- as an
   alternative to `SIMPLE_TRACE_QUERY_TEST_BINARY` (`<binary> trace <args>`).
   Neither set is still an explicit failure; no fallback process result exists.
   `scripts/check/check-trace-query-p0.shs` is the single owner of the
   alternate-index fixture (`build/test-artifacts/trace_query_p0/index`, built
   with `git read-tree HEAD` + one `update-index --cacheinfo` of a modified
   declaration blob; never the real index or worktree) and exports
   `GIT_INDEX_FILE` only for the spec process.

3. **Declaration input tolerance.** Registered declaration files
   (`doc/08_tracking/trace/features/*.sdn`) may begin with `#` comment lines.
   This is satisfied in the shared SDN parser (`std.common.sdn.parser.parse`
   skips leading full-line comments before every top-level shape dispatch,
   matching what the block-mapping route already did), not in the trace codec;
   `decode_trace_declarations` and the `simple.trace.declarations/1` schema are
   unchanged.

4. **Snapshot adapter tiers (stated, not changed).** `worktree_preview` reads
   files in-process and runs on the interpreter. `git_commit` and `git_index`
   go through `OwnedProcessLease` (owned-process v3), which the Rust seed
   interpreter deliberately reports as unavailable (`rt_process_owned_v3_adapter_unavailable`);
   those two routes and the mislabeled-tree rejection verify only on a native
   runtime provider (self-hosted/native `bin/simple`). Specs that need them are
   therefore Phase-3 verification, not seed-fixable defects.

Next slices (reverse references: which specs cover a requirement, bug <->
file links) touch the query model (`TraceNodeQueryV1`/page result) and will
get their own increment in this document before code lands.

## Reverse references increment — 2026-11-06 (slice 2)

No WP0-WP7 item names a reverse lookup on the query CLI (the architecture
document's "reverse references" are file-dependency edges for invalidation).
This increment defines one; it serves REQ-TRC-015 (details/source inspection
over the shared graph) and reuses the REQ-TRC-021/023 query contract.

**Honest data statement.** The registered declaration today carries 101
authored `add` claims over `specifies` (20), `decomposes_to` (73),
`implemented_by` (4), `described_by` (2) and `motivated_by` (2); it has no
`verified_by`/`accepted_by` claims and 1 test definition, and every claim
raised `TRACE-AUTHORITY-CONFLICT` until 2026-11-06 (query policy had `authorities: []`; now the policy-owned `trace_query_registered_authorities_v1` admits them as registered edges). "Which specs verify
requirement X" is therefore **not** answerable from this data; "which feature
specifies X", "what X decomposes to", and what a node is `implemented_by` /
`described_by` are. `implemented_by`/`described_by` targets
(`source:trace-cli`, `design:traceability`, ...) are not in the declaration's
`nodes` list, but the snapshot pipeline materializes them as `source_file` /
document nodes from their locators, so they render with a kind and title. The
row model still tolerates an endpoint with no node (kind and title rendered
empty, never invented). Because the declaration locates documents and sources,
not requirements, the other endpoint's declared paths are the usable
requirement <-> file link and travel with each row as `other_paths`.

1. **CLI surface.** `refs <kind> <id>` with exactly `show`'s argv shape
   (singular kind accepted, `--limit 1..200`, `--format table|sdn`,
   `--snapshot`, `--declaration`, `--path`; `--prefix` rejected; `--cursor`
   only as a continuation). Exit codes as for `show`: 1 rendered-unverified or
   `TRACE-QUERY-NOT-FOUND` (selected id absent or wrong kind), 2 invalid.
   `trace --help`, the command registry usage string and this document are
   updated together.

2. **Library owner.** New pure module `std.common.traceability.query_refs_v1`
   with `TraceReferenceQueryV1` (snapshot_id, kind, selected_id, limit, cursor)
   and `TraceReferenceV1 {claim_id, direction: "outgoing"|"incoming",
   relation, from_id, to_id, other_id, other_kind, other_title, operation,
   origin_id, authority, other_paths: [text] (sorted declared locator paths of
   the other endpoint)}` plus `TraceReferencePageV1 {snapshot_id,
   references, total_count, next_cursor, complete, locators, diagnostics}`.
   `query_nodes_v1` is unchanged except that its validator keeps rejecting
   `refs` (the reference validator is a sibling, not an extension, so existing
   one-hop pages keep their contract). Rows are every non-`suppress` claim
   whose `from_id` or `to_id` equals the selected id, sorted by canonical claim
   id, paged with the existing cursor scheme under a distinct schema string
   `simple.trace.reference-cursor/v1` that also binds the selected id.
   `authority` is `registered-edge` when a `graph.edges` row with the same
   from/relation/to exists, else `authored-claim`. `locators` are the selected
   node's own locator rows (where it is declared).

3. **Rendering.** Table: the node-page header, one `Selected: <kind> <id>
   <title>` line, `DIRECTION\tRELATION\tID\tKIND\tTITLE\tAUTHORITY\tPATHS` rows,
   `Total references: N`, optional `Next cursor:`, `LOCATOR\tPATH` rows, then
   diagnostics (same 200 cap). SDN: the node-page envelope keys plus
   `operation: refs`, `selected: {id, kind, title}`, `references: [...]`,
   `reference_count`, `locators`. Projection label stays "not a graph export".

4. **Verification tiers.** Worktree preview runs on the seed; git/index routes
   as in slice 1. Unit spec over a synthetic graph (both directions, suppress
   excluded, non-node endpoint, registered-edge vs authored-claim, paging);
   one system scenario through the direct entry on the worktree preview.

Slice-1 wording fix: item 2 above should read "If neither variable is set the
spec still fails explicitly; no fallback process result exists."

## Legacy bug-DB sidecar increment — 2026-11-06 (slice 3)

Problem: `trace list bugs` answers `Total selected: 0` because the registered
declaration declares no bug and `doc/08_tracking/bug/bug_db.sdn` is not
ingested. Agents need "which bugs touch file X" and "which bugs are open in
area Y" from the same query entry, read-only.

**Measured constraints that fix the shape.** (a) `bug_db.sdn` is 3.67 MB;
the capture adapters admit <=1 MiB per file and <=2 MiB per closure
(`worktree_query_v1`, `GitSnapshotRequest`), so it can never be a
`SnapshotArtifact` without changing every snapshot route. (b) The graph
schema requires a locator to be pinned (`blob_id != ""`) to a captured
artifact and `extract_snapshot_trace_facts` marks any locator path outside
the inventory `TRACE-MISSING-ENDPOINT` + incomplete; the bug `file` column
names hundreds of files that are not (and cannot be, see a) in the closure.
(c) Every graph claim without a registered authority raises
`TRACE-AUTHORITY-CONFLICT` (101 today); ~2,700 bug rows as claims would make
the diagnostics stream useless. (d) `TraceNode` carries id/kind/title only;
status/severity have no graph slot. (e) The database has two overlapping
tables: `bugs_active` 1,292 rows, `bugs` 1,741 rows, 982 active ids absent
from `bugs`, 310 ids in both, 0 duplicates inside `bugs`. (f) Reading it
through the std text codecs costs ~21 s on the seed (the UTF-8 validator is
an interpreted per-byte loop; measured `read_ms=21532`); the no-follow byte
reader plus the runtime-backed `string_from_byte_array` +
`text_validate_utf8` costs 0.28 s, and the row parser 0.7 s.

**Decision: a read-only sidecar, bound by identity, not a graph source.**

1. **Library owner.** New pure module `std.common.traceability.legacy_bugs_v1`:
   `LegacyBugRowV1 {id ("bug:" + db id), db_id, table, severity, status,
   title, file, line, reproducible_by, created_at, updated_at, valid}`,
   `LegacyBugSourceV1 {path, content_sha256, rows, diagnostics}`,
   `parse_legacy_bug_db_v1(content, path, sha)` (line scanner over exactly the
   `bugs_active` and `bugs` table sections; quoted fields unescape `\" \\ \$`;
   never the full SDN document parser), `legacy_bug_nodes_v1`,
   `legacy_bug_row_matches_v1(row, status, severity, file_prefix)`. Rules:
   `bugs_active` wins over `bugs` for a shared id; a second row with the same
   id inside `bugs_active` is reported (`TRACE-LEGACY-ROW`, severity
   `warning`) and the first kept; a row whose field count is not 10 or whose
   id is not a canonical identity is reported and skipped; a `file` or
   `reproducible_by` value that fails `trace_path_valid` is dropped to `""`
   (the row stays, the link is never invented); `valid=false` rows are kept
   with `valid: false` so they are visible and filterable; a 40,000-row
   budget ends the scan with a diagnostic. The module never writes.
   New pure module `std.common.traceability.sidecar_v1`:
   `TraceSidecarReferenceV1 {source_kind, from_id, relation, path, locator,
   authority}` and `TraceSidecarSourceV1 {kind, path, content_sha256,
   row_count}`. Legacy rows yield sidecar references `located_in` (the
   `file` column, locator `line:N`, authority `legacy-row`) and
   `reproducible_by` (same authority). The `file` column is often the bug's
   own `.md` record rather than a source file; the reference reports what
   the row says and labels it `legacy-row`, nothing more.

2. **What enters the graph.** Only bug *nodes* (`TraceNode {id, Bug,
   title}`), appended to the extracted facts before `resolve_trace_graph`,
   so node-identity validation, the 40,000-node budget and `list/show/refs`
   paging apply unchanged. A bug already declared by a registered
   declaration keeps the declaration's node; the legacy row still attaches
   its attributes. No claim, edge, locator or origin is synthesized from the
   database (constraints b, c). Legacy diagnostics are appended with
   severity `warning` and do not change `graph.complete`.

3. **Identity.** `build_snapshot_trace_graph` gains a sibling
   `build_snapshot_trace_graph_with_sidecar_v1(snapshot, policy,
   declarations, scope, sources: [TraceSidecarSourceV1], nodes)`; the old
   entry calls it with none. When `sources` is empty the input manifest is
   byte-identical to today's (the key is absent); otherwise
   `inputs["sidecar_sources"] = [{kind, path, content_sha256, row_count}]`
   sorted by path, so generation ids and every cursor invalidate when the
   database changes. `TraceSnapshotBuild` gains `legacy_bugs:
   [LegacyBugRowV1]`, `sidecar_references: [TraceSidecarReferenceV1]` and
   `sidecar_sources` (defaults empty).

4. **Capture.** Worktree preview only in this increment: the app reads the
   database with the existing no-follow bounded byte reader (<=16 MiB) after
   the snapshot capture, decodes with the runtime-backed converter and
   validates UTF-8 (constraint f), hashes it, parses. `--bug-db=<path>`
   selects the file (`trace_path_valid`), `--bug-db=none` disables; the
   default is `doc/08_tracking/bug/bug_db.sdn` *when it exists*, otherwise
   nothing is ingested and output is unchanged. An explicit path that cannot
   be read is `TRACE-LEGACY-CAPTURE` (exit 2). `git:`/`index` snapshots do
   not ingest (the git provider's blob cap is 1 MiB and the worktree file
   is not the committed one); they report
   `legacy_database_ingestion: unavailable-for-snapshot-kind`. Default-on is
   justified by the measurement: ~1 s on the seed.

5. **Filters for `list bugs`.** `--status=<text>`, `--severity=<text>`,
   `--file-prefix=<path-prefix>` (each once, only with `list bugs`, exact
   match on the row attribute / `starts_with` on `file`). They apply before
   paging: the app queries a graph copy whose bug nodes are those whose row
   matches, and folds the filter into `TraceNodeQueryV1.visibility_context`
   (`local-selected-content/v1;status=..;severity=..;file=..`), which is
   already part of the cursor prefix, so a cursor from a filtered page is
   rejected unfiltered and vice versa. `query_nodes_v1` is unchanged.

6. **Rendering.** Header line becomes `Ingestion: registered declarations +
   sidecar bug-db/v1 <path> rows=<n> sha256:<hex>` when a source was
   ingested (unchanged text otherwise). Bug rows get three appended columns
   `STATUS\tSEVERITY\tLOCATION` (`file:line`, empty when no safe file); the
   header row for `bugs` is `KIND\tID\tTITLE\tSTATUS\tSEVERITY\tLOCATION`,
   other kinds keep `KIND\tID\tTITLE`. SDN: `legacy_database_ingestion`
   becomes `"bug-db/v1"`, `sidecar_sources: [{kind, path, sha256, rows}]`,
   each bug node gains `legacy: {table, status, severity, file, line,
   reproducible_by, valid, created_at, updated_at}`. `refs bug <id>` adds
   `SIDECAR\t<relation>\t<path>\t<locator>\t<authority>` rows after the
   `LOCATOR` rows (SDN `sidecar_references`), still `Total references: 0`
   for a bug with no authored claims -- that number counts graph claims only.
   String consumers updated together: `trace_query_p0_spec` (1 assertion on
   the ingestion line) and `query_render_refs_v1` (2).

7. **Verification.** Unit spec on a synthetic database text (both tables,
   overlap precedence, 11-field row, unsafe path, `valid=false`, quoted
   commas and escapes) and on the filter/visibility fold; system scenario
   through the direct entry on the worktree preview: BEFORE `Total
   selected: 0` -> AFTER `Total selected: N>0`, plus `show bug` and
   `--status=open`. Runs on the seed.

## Annotation coverage increment — 2026-11-06 (slice 4, design only)

"Which spec verifies requirement X." The registered declaration has no
`verified_by` claims; the test tree carries `# @req REQ-XXX-NNN ...` header
lines in 7,041 `*_spec.spl` files (`@cover` lines are file-coverage
percentages, not requirement links, and are ignored). Scanning 7k files per
query is not viable on the seed, so the scan is **opt-in and bounded**:
`--spec-root=<dir>` (repeatable, <=8, `trace_path_valid`, real non-symlink
directory). The app enumerates `*_spec.spl` under each root (recursive,
<=4,096 files total, sorted), reads each file's first 8 KiB with the
no-follow bounded byte reader, and takes `# @req` lines from the leading
comment block only. Each id becomes a sidecar reference
`req:<ID> verified_by <path>` (authority `annotation-claim`, source kind
`annotation-req/v1`); one `TraceSidecarSourceV1` per root whose
`content_sha256` hashes the sorted `(path, header_sha256)` list, so the
manifest and cursors bind the scanned headers. No graph claim is created
(constraint c above); `refs requirement <id>` renders them as `SIDECAR`
rows, `refs file <path>` lists the requirements a spec claims. Authority
wording stays "declared by the spec header", never "verified".

## File-centred summary increment — 2026-11-06 (slice 5, design only)

`refs file <path>`: the selected identity is a repository-relative path.
The page lists (1) graph claims whose endpoint is the captured artifact node
of that path (`artifact:<hex>`), rendered exactly as `refs` rows; (2)
`LOCATOR` rows for every entity declared at that path; (3) `SIDECAR` rows
for every sidecar reference whose `path` equals it (bugs `located_in` /
`reproducible_by`, requirements `verified_by`). A path that is neither
captured nor referenced is `TRACE-QUERY-NOT-FOUND`. `--limit`/`--cursor`
page the union in a fixed order (claims, locators, sidecar) under schema
`simple.trace.file-refs-cursor/v1`. "Bugs open in area Y" stays
`list bugs --status=open --file-prefix=<dir>/`.

Slice-4 amendments at implementation (2026-11-06): (1) the header is the
leading `#` comment block *or* a leading `"""` docstring followed by comment
lines (`trace_node_query_spec.spl` has that shape); (2) the bounded reader
refuses, rather than truncates, an over-bound file, so each spec is read whole
(<=1 MiB, larger files skipped with `TRACE-ANNOTATION-SCAN`); (3) an id that
no declaration registers but that owns sidecar rows renders a sidecar-only
`refs` page labeled `(undeclared; sidecar references only)` with
`total_count: 0`, exit 1 -- no node or claim is invented, and without sidecar
rows the answer stays `TRACE-QUERY-NOT-FOUND`.

Slice-5 amendments at implementation (2026-11-06): no cursor in this cut
(`--limit` caps claim rows, `complete=false` when capped) instead of the
union cursor schema; the selected node is the declared file node when one
exists, else the captured artifact node, else a labeled placeholder
`(not captured; sidecar references only)`; `LOCATOR` rows gain the entity id
and `SIDECAR` rows the referring id (table trailing columns, SDN `from`), so
the file page is readable without a second query.
