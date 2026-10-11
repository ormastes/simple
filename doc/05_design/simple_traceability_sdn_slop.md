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

### 2026-10-11 owner preparation implementation checkpoint

The current source adds `TestDatabaseExtended.record_trace_run_plan`,
`get_trace_run_plan` and `validate_trace_run_active`. The plan table uses an
explicit storage schema and reversible UTF-8 hex scalars because the legacy
DB row codec cannot safely preserve nested SDN quotes. The logical payload is
canonical `simple.trace.run-plan/v1` SDN. Every read validates the table,
decoded identities, duplicate rows, canonical payload and unverified validity.
Recording requires exactly one valid running run and precedes observations.

`RunnerTestDb.prepare_trace_run` saves before exposing prepared state. A failed
save poisons that wrapper; the caller must discard and reload it. Static
`resume_trace_run` loads persisted state afresh and validates the run and plan.
Neither operation grants a concurrent writer lease or admits test evidence.
The v1 plan still lacks the full input, shard and attempt provenance contract;
these APIs do not implement the proposed full TraceRun finalization protocol.

The live runner still requires pre-dispatch planning and child-protocol wiring.
Observation storage migration must use an explicit row version, decode keys
before filtering/replay checks and keep surviving historical rows unverified.
No lost legacy row can be reconstructed from a passing aggregate counter.
Actual native execution, disk reload/crash recovery, lease contention and
failure-path acceptance remain required; authored fixtures are not receipts.

### Predispatch selection boundary review (Astra, 2026-10-11)

`run_tests` currently performs discovery, coverage admission, daemon/parallel
routing and sequential execution together. Freezing a file list outside that
function is insufficient: late single-file checks still decide feature skips,
effective backend and timeout. Split preparation from execution. A frozen
selection must retain selected cases, omission reasons, effective lane/options
and exact source/definition identities. Every dispatch route consumes the same
selection without rediscovering or silently changing those decisions.

The initial owner protocol accepts a distinct `simple.trace.run-request/v1`
SDN document without a run ID. The existing DB child allocates the identity,
materializes a validated plan, saves it and returns an SDN acknowledgement
binding request digest, persisted plan digest and allocated identity. Missing or
invalid acknowledgement prevents dispatch. Post-run submission uses that exact
identity. A request is execution intent; it cannot authenticate its own inputs.
Full provenance still requires versioned input closure, shard and attempt data
beyond the current v1 plan.

Current snapshot extraction supports registered SDN declarations and artifact
locators, not an authoritative static case inventory. The test manifest is
file-level metadata. Runtime enumeration suppresses case bodies but executes
user describe/context callbacks and lacks exact selector/requirement data;
it is unsuitable as a trusted static extractor. An owned SDN case inventory
can support the initial path, with source bindings validated independently.
It does not replace the required automatic semantic extraction in the final
feature. Unsupported dynamic or parameterized discovery must stay explicit.

### 2026-10-11 static SSpec extraction interface review

The production compiler parser and AST are present in the tracked tree under
`src/compiler/10.frontend/core`. `parser.spl` parses source into the arena AST
owned by `ast_expr.spl`, `ast_stmt.spl` and `_Ast/decl_nodes.spl`. Nodes retain
source-span IDs; the span pool exposes byte start/end and line/column accessors.
The parser module has `parse_module(source, path)`,
`parse_module_silent_checked(source, path) -> bool`, and
`parse_module_file(source, path)` entrypoints. They are module-level functions
used by internal compiler modules; the checked entrypoint returns a reliable
parse-failure boolean but populates module-global parser/AST state rather than
returning an isolated syntax-tree value. The grammar frontend is therefore
available, but not yet exposed as a safe immutable-source extraction API. A
separate `std.gc_async_mut.pure.parser` also exists; it is a small experimental
parser and should not replace the production grammar.

The production `compiler.frontend.parser.test_analyzer` defines `TestMeta`,
`TestGroupMeta` and `FileTestMeta`, but its `extract_tests_from_source` and
`extract_file_test_meta` functions are private line-by-line scanners, not AST
walks. The live runner's `list_tests_static` is another line scanner: it
recognizes a few test-call prefixes and returns file/name strings. Neither
extractor provides spans, exact selectors or dynamic-construction
diagnostics. The gap is not a missing compiler parser; it is a missing public,
isolated AST parse result and a sound AST-based SSpec extractor.

The SSpec API itself is executable registration code. `describe(name, block)`
and `context(name, block)` invoke user callbacks. The opt-in aggregate registry
in `std.nogc_sync_mut.spec` declares cases while the module runs: IDs hash the
owner path, source hash, current suite/context names, case name, kind, and
ordinal. Enumeration avoids the case body but still imports/evaluates the
candidate module and invokes describe/context callbacks. Thus it is not an
immutable-source static inventory and its digest-derived IDs are ordering and
source sensitive. Current `TestManifestEntry` records paths, level, tags,
platform and a few file classifications; it has no case names or stable
case-level metadata. In-development is currently read as a whole-file source
classification after execution, not attached to each declared case.

The narrow extraction API should expose the production parser through an
isolated service that returns a syntax tree with byte spans and explicit parse
diagnostics for the exact immutable source bytes, without leaking or reusing
mutable global parser state across files. Its output should be a typed
`TraceCaseDefinition` containing exact source path and span, ordered literal
suite/context components, literal case name, declaration kind, source digest,
and an optional explicit stable-case key. A separate selector value should
retain the exact path plus suite/context/name and, when available, the stable
key. No adapter should import a candidate module or call its describe/context
functions to produce these values.

The first supported grammar slice can recognize direct SSpec calls with
literal text arguments and statically nested `describe`/`context` blocks. A
callback's body may be traversed only as syntax; arbitrary callback execution
is forbidden. Static `it`, `test`, `example`, `specify`, `slow_it`, and
`skip_it` declarations can be emitted with distinct kinds. Calls whose name or
block is computed, declarations produced by loops/helpers/macros, parameterized
case generators, malformed syntax, unresolved aliases, and unsupported
conditional registration must return an explicit unsupported/incomplete
diagnostic. They must never be guessed from regex matches or silently omitted.
Feature gates and environment selectors need typed dispositions that bind the
selected environment/options; absent that contract, mark the inventory
incomplete instead of treating a declaration as selected or excluded.

Case identity should bind the immutable source blob, exact source span, typed
selector and declaration kind. An explicit stable-case key may replace the
span-derived portion only after the parser can validate uniqueness and bind
the key to that same source declaration. The current tree has no such
case-level stable metadata syntax or parser support, so the initial design
must not claim reorder-stable identity. A source insertion/reorder may change
the identity and must produce a new plan. Dynamic or parameterized cases stay
unsupported until their expansion inputs and deterministic ordering are
captured in the plan.

Implementation prerequisite: expose the existing production parser as a
read-only library API over caller-supplied immutable source bytes, returning
source spans, parse errors and access to the corresponding AST generation.
Add an AST-based SSpec extractor with fixtures for nested literal declarations, escaped and
Unicode names, aliases, conditional and dynamic declarations, parameterized
cases, and syntax errors before wiring it to `TraceRunRequest`. Until that API
and its fixtures exist, `validate_trace_request_selection` checks only exact
file-path set equality; its success is not proof that planned cases exhaust the
selected files.

Legacy runner JSON worker producers and consumers must be inventoried and
migrated to native SDN for this feature's full interchange contract. Neither
new SDN sidecars nor passing ordinary worker execution prove that migration.

### Frozen execution binding after the literal AST slice

The authored `extract_sspec_inventory_single_owner` now uses the resetting
production parser entry and returns copied literal definitions with UTF-8 byte
spans. It requires exclusive frontend ownership. This source implementation is
not the isolated concurrent parser API above and remains native-unverified.
The sequential-snapshot fixture checks both removal of prior declarations and
preservation of previously returned values; it must execute on Phase 3 before
that behavior is accepted.

Run preparation must freeze more than a selected path list. The runner shall
capture one selection generation after discovery and coverage admission and
reuse it for every worker route. Its manifest binds exact source bytes, case
definitions, effective backend/mode, timeout policy, slow-case disposition,
feature gates, shard membership, execution lane, fixtures and configuration.
An opaque configuration ID supplied by a caller is intent until its relation
to these values is validated. Inventory hashes similarly prove byte equality,
not the source's membership in an authenticated candidate snapshot.

Separate the operations into selection/preparation and execution. Preparation
must not dispatch candidate callbacks. Execution must consume the frozen
selection without rediscovery and either read immutable staged inputs or
validate the exact frozen bytes before dispatch under a binding that prevents
subsequent mutation. A check followed by an unrestricted mutable file read is
insufficient. Per-file directives currently applied during execution belong
in preparation; unsupported directives or worker modes must return an explicit
incomplete error before allocating or executing a trace run.

The initial planner envelope can retain declaration kind, source digest and
span alongside the existing v1 planned-case projection. These values require
durable storage and child verification before full provenance admission; they
cannot be discarded at the database request boundary. Complete import/input
closure, dynamic registration and parameter expansion remain separate required
contracts, not implied by the literal grammar slice.

### Worker result framing

The legacy worker writes progress and its final structured result to the same
stdout stream. Selecting the last nonempty line is not the target SDN protocol.
Public structured execution shall use a parent-owned result-file boundary:
the private worker writes one canonical `simple.test-runner.output/v1` SDN
document to an exclusively reserved result path in a private directory, while
its stdout/stderr contain diagnostics only. The parent captures both streams
with bounded process ownership, routes diagnostics to stderr, and reads the
result using a bounded regular-file, no-follow facade after terminal cleanup.
It validates the complete document before emitting it as the public stdout
message. Missing files, output limits, timeout, cleanup failure, malformed SDN,
and exit/result disagreement produce explicit non-green failure messages.

The result path is a transport capability, not a free-form candidate output
attribute. Directory ownership and exclusive reservation must prevent another
writer replacing it; a random-looking filename alone does not establish that
boundary. Only owned files are removed during cleanup. Authentication markers
and recursion guards must be child-scoped process settings, not leaked global
environment state. The wrapper executes an admitted cached binary rather than
compiling a source entrypoint as part of the operation.

The v1 producer and consumer share a 1 MiB document limit, matching the bounded
SDN parser contract. Larger observations require an explicit shard/artifact
contract or a separately verified larger parser policy. They are never silently
truncated, converted to JSON, or treated as a successful partial result.

### Native worker retirement prerequisite (audit 2026-10-11)

The SDN wrapper must remain fail-closed until its process owner can prove the
whole worker scope retired. The current Process Observation V4 Linux ABI has
exact environment, pinned executable and cwd, exec confirmation, pidfd, bounded
capture, and two-phase collect/ack. Its native capabilities advertise
`POV4_CAP_LEADER_ONLY`; request decoding rejects any descendant policy other
than leader-only. Frozen snapshots deliberately set `tree_empty=0` and
`tree_empty_ns=-1`. V4 creates a process group, but deadline/cancel signaling
uses the leader pidfd, so neither group signaling nor group emptiness is proved.
The Windows V4 implementation reports unavailable.

The V3 owned-process path is not a safe bridge. It creates a POSIX process
group, can signal that group on timeout/cancel, and samples group members for
resource telemetry. Its `tree_empty_ns` is assigned from the leader's wait
timestamp, without a group-empty observation; a descendant can outlive the
leader or escape the process group. V3 also does not accept the exact scoped
environment carried by V4. Combining a V3 kill with a V4 receipt would split
process authority across unrelated leases and would not repair those missing
proofs.

There is an existing Linux cgroup-v2 owner that is a credible implementation
reference: `runtime_linux_group_owner_impl.h` pins and hashes the executable
then executes through the same fd, passes an explicit environment, pins cwd,
places the worker into its cgroup with `clone3(CLONE_INTO_CGROUP | CLONE_PIDFD)`,
uses `cgroup.kill`, and reports empty only after the leader is reaped and
`cgroup.events` reports the group unpopulated. Its `linux_process_owner` facade
and durable `group_process_owner` protocol are separate from V4, write output
to owned files, and require delegated cgroup-v2 memory controls plus
`clone3`/pidfd/`execveat`. They do not supply the V4 ticket, stream, or frozen
receipt contract directly. Reuse therefore means extending the V4 owner around
this stronger scope or explicitly migrating the wrapper to that owner; it does
not mean accepting V3's leader timestamp as tree proof.

The next Linux owner change needs a truthful descendant-scope capability and
request policy, atomic placement before worker execution, scope-wide cancel
and deadline enforcement, leader reap followed by bounded wait for the scope
to become empty, and a frozen receipt that records the observed empty state
and time. Cgroup cleanup failure or cleanup-budget expiry stays incomplete and
must retain cleanup authority. V4 capabilities are advertised only where this
full contract is implemented. Native tests should hold a grandchild alive
after the leader exits, exercise timeout/cancel and cleanup expiry, attempt
session/process-group escape, assert no terminal success before the cgroup is
empty, and verify unsupported hosts reject admission before spawning.

Windows needs a distinct V4 provider using the existing Job Object owner
patterns: create suspended, assign to a kill-on-close job before resume, pass
the exact environment block, then require leader reap and zero active job
processes before freezing. Current `windows_process_owner` has related job
accounting but is not wired into V4's capability/receipt ABI. Its tests must
cover leader-exits-first descendants, forced cancellation, active-process
drain, and job cleanup uncertainty. Until the platform provider is implemented
and its native tests pass, SDN worker wrapping remains explicitly unavailable
on that platform.
