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

## Phase 3 corrective interfaces — 2026-10-11

This appendix corrects the recovered-source checkpoint at
`cabd1dd91f42ecd6e0a5daa2abac8937aebb03e2`. Earlier claims that plan/final APIs
already exist and that persistence precedes docgen are not true on this
baseline. The existing common model/resolver names remain authoritative.
The following additions are implementation contracts, not claims that their
code or acceptance evidence already exists. The merge owner freezes any final
spelling before dependent lanes consume it. Runtime qualification requires the
user-requested admitted, source-matched Phase 3 compiler.

### Snapshot-to-graph composition

Root owns `app.traceability.extract.snapshot_pipeline::build_snapshot_trace_graph`.
Its inputs are `SnapshotInput`, `TracePolicy`, registered declaration paths,
extractor version, and an explicit selected-scope descriptor. A minimal
`TraceSnapshotScope` contains `selected_roots`, `authority_id`, `closure_kind`.
The first supported closure kind is `selected_scope`; `policy_closure` requires
independent policy-owner admission, never a candidate-supplied boolean or ID.
Authority identity identifies provenance but cannot authenticate itself.

Roots must be nonempty, normalized, unique repository-relative files/directories.
Every artifact and registered declaration must belong to the declared scope;
the snapshot adapter must establish that its inventory covers those roots.
Empty/unknown scope, unsupported closure or missing inventory yields an explicit
incomplete diagnostic. Graph `complete` means complete within that retained
scope; it must not imply repository-wide coverage or admission eligibility.
Preview callers can use unauthenticated selected scope but cannot grant admission.

Canonical structural input identity binds sorted path/blob/visibility records,
scope, all policy/convention/authority records, declaration registration,
schema identity and extractor version. Reject duplicate or contradictory
inputs before hashing. Revision/tree identity belongs to generation and exact
subject, not the stable structural digest; generated outputs are excluded only
by named policy so regeneration can stabilize without a self-hash loop.
An arbitrary caller-provided digest is not accepted as computed identity.

### Case planning and execution bindings

The shared kernel owns a pure `build_trace_case_plan` operation and a pure
`reconcile_trace_case_events` operation; final signatures and record spelling
belong to the assigned run-plan lane. A plan binds graph-defined case identity,
definition and parameter digests, pinned test file, runner selector, shard and
attempt. It also binds the immutable run inputs already present in `TraceRun`.
Plan construction must validate graph/definition closure and unique selectors.
Until semantic extraction proves the selector corresponds to a discovered case,
an owned SDN declaration remains an authored plan, not an execution observation.

Current v1 events are untrusted transport. They may map to a plan only when the
owner independently binds file, shard and attempt and the case name is unique
within that binding. Unknown/duplicate/ambiguous, finish-without-start,
conflicting outcome or truncated events are diagnostics; missing expected
cases/shards leave the run incomplete. Retrying requires an explicit new
attempt; two indistinguishable events cannot be guessed into two attempts.
Parameterized cases require a unique planned selector and parameter digest.
These pure operations never construct `AdmissionContext` from event claims.

### Durable runner owner and publication

Preserve `test_db_lane_main.spl` and `RunnerTestDb` as the sole database owner.
Proposed owner methods are `persist_trace_plan(run: TraceRun) -> Result<(), text>`
and `persist_trace_final(run: TraceRun) -> Result<(), text>`; they are absent at
this baseline. The first freezes immutable bindings before dispatch and persists
an incomplete run with planned cases/shards. The second preserves those bindings,
retains attempts, validates expected shard closure and writes terminal state.
Repeated identical finalization is idempotent; conflicting finalization fails.
Recovery finalizes an orphaned admitted plan as incomplete/crashed, never passed.
One final call alone does not prove durable crash recovery or concurrency safety.

The live app must receive an error result from DB-lane persistence and retain
an infrastructure failure exit. Persistence precedes docgen and reporting;
report failure cannot discard observations. Automatic run-scoped SDN+Markdown
includes failures and zero-discovery against a nonempty plan. Durable plan/final
protocol, artifact/provenance verification and recovery remain separate gates.
No new graph-owned writer or direct database import into the live runner is
introduced merely to bypass the existing child-owner boundary.

### Incremental implementation boundary

Keep `plan_trace_invalidation` as the planner rather than relabeling it an
implemented update API. The next store layer must retain per-file facts,
extractor/schema/policy identities and positive, missing, unique and membership
dependencies. It applies deletions/replacements, resolves the full resulting
fact universe and publishes a validated generation atomically. Incomplete
dependency inventory forces full rebuild; budget exhaustion is incomplete.
Only independent cold-rebuild equality fixtures can qualify incremental results.

All forty original ACs remain active. Source-authored scenarios, documentation
and declaration ledgers establish implementation progress only; production
execution, manual quality, cross-host/UI/gate evidence and release admission
remain separately unverified until their real receipts exist.
