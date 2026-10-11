# Traceability implementation contract v1

Status: frozen naming/ownership for parallel implementation; behavior remains
unverified until actual production-path tests pass. 2026-10-03.

## Shared package and records

Package: `std.common.traceability`. Files: `model.spl`, `schema.spl`,
`sdn_codec.spl`, `resolve.spl`, `conventions.spl`, `obligations.spl`,
`evidence.spl`, `incremental.spl`, `query.spl`, `markdown.spl`.

Use closed enums for node kinds, relation kinds, claim operations, execution
outcomes, validity, applicability and qualification. Identifiers are validated
text, not row/line numbers. All boundary failures carry diagnostic records.

| Record | Required fields |
|---|---|
| SnapshotSubject | repository_id, snapshot_id, kind, revision_id, tree_id, object_format |
| SnapshotArtifact | path, blob_id, content, visibility |
| SnapshotInput | subject, artifacts, complete |
| TraceNode | id, kind, title |
| TraceOrigin | id, kind, owner_path, locator, rule_version |
| TraceClaim | id, from_id, relation, to_id, origin_id, operation, rule_id, scope_id |
| TraceEdge | id, from_id, relation, to_id |
| TraceEdgeOrigin | edge_id, origin_id |
| TraceLocator | entity_id, path, locator_kind, locator, blob_id |
| TraceDiagnostic | code, subject_id, rule_id, entity_id, origin_id, message, severity |
| TraceGraph | subject, input_manifest_id, nodes, test_definitions, claims, edges, edge_origins, origins, locators, diagnostics, generation_id, complete |
| TraceTestDefinition | node_id, kind, definition_id, parameter_digest, definition_digest |
| TraceQuery | snapshot_id, selected_id, direction, limit, cursor |
| TraceQueryResult | snapshot_id, nodes, edges, total_count, next_cursor, complete, diagnostics |
| SourceSlice | snapshot_id, blob_id, path, start_line, end_line, content |

Lists default empty only when empty is a valid fact, never to hide failed input.
Test-kind facets are graph-defined (acceptance/unit/integration/component/system/
performance), so an obligation cannot classify its own case. Parameterized
instances retain their base definition and parameter-set digest. Multiple roles
share one node identity and actual observation, not duplicate executions.
Graph completeness is separate from qualification. Query completeness refers
to a page; graph completeness remains visible independently. A stale cursor
or snapshot mismatch returns a diagnostic and no mixed-generation result.

## Entry points

- `decode_trace_document(text) -> Result<TraceDocument, [TraceDiagnostic]>`
- `encode_trace_document(TraceDocument) -> Result<text, [TraceDiagnostic]>`
- `extract_trace_facts(SnapshotInput, TracePolicy) -> TraceFacts`
- `resolve_trace_graph(TraceFacts, TracePolicy) -> TraceGraph`
- `update_trace_graph(TraceIndex, SnapshotDelta, TracePolicy) -> TraceUpdate`
- `evaluate_obligations(TraceGraph, [TraceObligation], TraceRun, AdmissionContext) -> TraceQualification`
- `project_trace_markdown(TraceGraph, TraceQualification) -> [TraceOutput]`
- `query_trace_graph(TraceGraph, TraceQuery) -> TraceQueryResult`

Record details may grow with explicit review; shared names cannot diverge
between implementation lanes. No app defines its own resolver or eligibility.

## Serialization

Use `std.common.sdn.parser.parse_with_spans_and_issues` and
`std.common.sdn.encode.sdn_encode_canonical`; reject reported duplicate keys.
Validate schema family/version, exact required fields, enums, integer bounds,
ID uniqueness and reference closure before constructing typed records.
Canonical machine envelope is Dict with arrays of Dict records. Never nest
SdnValue.Table in this encoding; current writer cannot round-trip that shape.
Never use legacy `std.sdn.render_value` (table loss/escaping limitations).
Stable ordering is explicit; all quoting/escaping remains shared-codec-owned.

## Resolution and incremental index

Extraction yields claims and provenance, not unearned semantic edges. SSpec
association comes from parsed supported metadata or an owned SDN sidecar.
Quoted REQ examples are not claims. Resolve authority and endpoints before
targeted replace/suppress; add explicit claims then coalesce equal edges while
retaining every origin. Reject conflicts, stale overrides and forbidden cycles.

Index records file facts, positive/negative lookups and membership queries.
Replace/delete removes prior facts; new duplicates invalidate uniqueness;
policy/extractor/schema changes invalidate the full affected partition or all.
Publish only a complete validated generation. Missing closure is incomplete.

## Observation and qualification contracts

`TraceRun` binds run/attempt identity, planned case IDs, exact definition/input
manifests, effective configuration, lane, binary/build identity, expectations,
observations and terminal completion. `TraceObservation` preserves all attempts,
actual outcome and artifact identities. `TraceObligation` binds requirement,
criterion, test kind/cases, applicability, configuration and all/alternative
satisfaction policy. `TraceQualification` records each obligation's status,
selected observations and rejection reasons with separate structural/execution
numerators and denominators.

`AdmissionContext` is constructed by the admitted owner from independently
validated artifact bytes, producer provenance and input/build equivalence. A
caller-authored flag inside a run is never proof. Kernel unit tests may supply
typed verified-fact fixtures but cannot stand in for adapter provenance tests.
No observed case, unfinished shards, skipped/lower-layer not-run and stale
evidence cannot satisfy required obligations. Feature lifecycle is separately
authored through an authorized transaction.

## Runner and publication transactions

Extend RunnerTestDb; it remains the only observation writer. Freeze plan and
inputs before execution; finalize exact shard set after completion, including
failure/interruption. Automatic feature-run SDN+Markdown is mandatory; renderer
failure preserves saved observations and adds an infrastructure result.
Graph store writes a temporary generation then publishes a validated manifest.
No test run silently edits tracked feature declarations or all stable manuals.

## App adapters and UI

Snapshot providers read index/tree/SJ bytes with batched Git object access;
worktree preview is labeled. Gate adapters preserve existing dispatcher and
security checks, exact multiref subjects and local offline budgets. Existing
CLI accepts SDN only after callers migrate; obsolete formats fail actionably.

Slop uses the query types above (TraceQueryResult, not a second TraceProjection
authority) and exact SourceSlice from snapshot owner. Layered geometry is a
view transform; edges are only actual typed edges. Native renderer needs real
event/focus tests, text and GUI captures. No JSON access serializer or diagram
parser may become a hidden trace database.

## SSpec vocabulary and evidence

Shared helpers: `trc_fixture_create`, `trc_invoke_candidate`,
`trc_read_run_artifacts`, `trc_assert_subject`, `trc_assert_obligation`,
`trc_capture_result`. Primary visible steps: Prepare the isolated candidate;
Declare the requirement and acceptance obligation; Run the production
traceability command; Inspect the retained SDN result and Markdown report;
Verify the exact subject and obligation state.

Use real typed evidence and independent expectations; hidden reusable setup
uses `@inline`/`@prev`, advanced cases fold, manuals mirror executable paths.
Missing fixtures fail explicitly and never become placeholder passes. A
definition inventory is not an executable acceptance result.

## Execution admission and delivery

No admitted Stage 4 runtime is identified in this lane yet. Do not use the
Windows wrapper's Rust fallback or infer build provenance from an executable
name. Retain this prerequisite separately from authored source progress.
All ACs remain active until run with appropriate exact binary/source lineage.
Tests execute serially under root ownership. Three repair cycles maximum per
failure; preserve results without repeating unchanged green commands.


## Coordinated evidence model ownership

Structural records remain in `std.common.traceability.model` (kernel lane).
Evidence and obligation records share `evidence_model.spl` (evidence lane):
TraceOutcome, TraceCompletion, TraceTestKind, TraceApplicability,
TraceSatisfactionPolicy, TraceQualificationStatus, TraceObservation, TraceRun,
AdmissionContext, TraceObligation, TraceObligationResult, TraceQualification,
and TraceOutput. `evidence.spl`, `obligations.spl`, and `markdown.spl` import
these records; apps never redefine them. Qualification.subject_id is the
SnapshotSubject.snapshot_id. AdmissionContext includes exact independently
admitted observation copies and eligible previous observations whose producer,
complete run and input equivalence the owner validated. Candidate-supplied
observation IDs or trust booleans alone are not admission.


## Evidence lane source checkpoint and pending production adapter

The callback transport is named `.trace-events.sdnstream`, deliberately not
`.sdn`: LF frames one canonical `simple.trace.case-event/v1` SDN dictionary
per event. It is diagnostic transport, not a standalone SDN document or an
admitted run receipt. `collect_trace_event_documents` turns frames into an
array; `decode_trace_case_events` invokes the shared parser and rejects bad
schemas, duplicate fields and truncated records. Do not feed the entire stream
to single-document readers. Admitted `encode_trace_run` output is one canonical
`simple.trace.run/v1` SDN dictionary; never use generic JSON worker data as the
trace evidence transport.

The opt-in framework callback records started/finished outcomes before output
formatting. `TestFileResult.trace_case_events_sdn` carries the canonical array
inside the owner process; the JSON worker format remains unchanged. Dedicated
worker/daemon SDN sidecar admission, attempt/parameter identity mapping, and
retained artifact digests remain pending. Missing transport cannot qualify.

RunnerTestDb owns `persist_trace_plan`, `record_trace_case_events`, and
`persist_trace_final` through its existing unified SDN database. Plan/final
APIs enforce one frozen plan and unchanged immutable bindings. The live CLI's
post-run summary persistence now precedes SPipe docgen, and docgen failure
retains infrastructure exit status and original observations. The current
live CLI has NOT yet been connected to the before-dispatch plan/final APIs:
it needs the semantic extractor's supported case plan and admitted snapshot
and binary identity. These APIs alone do not close AC-TRC-021/022/027.

All new tests are tagged in-development and remain NOT RUN while the user
waits for an admitted Stage 4 runtime. The evidence kernel unit spec proves
only its typed contracts when executed. It does not claim complete production
extractor/runner/reporting SSpec, remote provenance admission, DB crash safety,
performance budgets, or host qualification. Automatic feature SDN/Markdown,
runner recovery, native end-to-end manuals and release readiness stay active.
