> Merge candidate status (2026-10-11): **UNRUN**. This resolution combines local
> `ddff8671e8348a89ab2eed285311a3ffc1809358` and remote
> `3aa33b9f8de7897fcf4e83c42bc3c44d28782cef`. All counts and PASS statements below
> retain their historical component/source-stage scope. They are not execution,
> semantic verification, or admission evidence for this combined source.

# Shared traceability architecture

Status: implementation design; not deployed. Authority: final report sections
5–13 and REQ-TRC-001–020. Astra review is required before implementation.

## Ownership and layers

`std.common.traceability` owns value contracts, graph invariants, resolution,
evidence eligibility and qualification. It consumes explicit immutable facts;
it performs no filesystem/process/UI operations. Infrastructure adapters own
snapshot IO and persistence. CLI, tracking, reporting and Slop consume the same
graph/evaluator and cannot independently promote evidence to verified status.

Freeze these names: `SnapshotProvider`, `TraceGraph`, `TraceClaim`,
`TraceOrigin`, `TraceDiagnostic`, `TraceObligation`, `RunManifest`,
`CaseObservation`, `EvidenceEligibility`, `TraceQualification`,
`TraceProjection`. Public consumers see canonical IDs/values and read-only
queries; adapter-private indexes and UI state remain private. Component/layer
views refer to canonical IDs rather than copying nodes. New syntax is optional
sugar over supported SSpec/SDN metadata, never a first-release dependency.

## Data flow

Exact snapshot + trusted policy → parsed owned facts → identity registry and
claim resolution → complete graph generation → obligation/evidence evaluator
→ shared projection → SDN CLI / stable Markdown / run Markdown / HTML / Slop.
Graph cache is derived and disposable. Readers publish only complete immutable
generations; old-generation UI remains explicitly last-valid on failure.

`RunnerTestDb` remains the sole observation writer and DB migration boundary.
Runner adapters record the planned execution set before execution, retain all
attempts, finalize incomplete runs, and emit immutable artifacts even on failure.
Feature lifecycle is authored; qualification is computed. A passed acceptance
suite cannot imply unit/integration/component execution or authorize done.

## Trust and invalidation

Commit checks use the index, push checks all supplied ref updates, remote checks
the exact event candidate. Candidate code/policy cannot select its own trusted
admission authority. Existing gate registry/dispatcher retains safety checks.
Missing runtime, invalid schema, reads, deadlines, provenance or incomplete
closure yield exit 2/incomplete, never clean. Hooks are bounded/read-only/offline.

Facts bind parser/rule/schema version and source bytes. Invalidation includes
negative lookups, collection membership, ID conflicts, aliases, deletion and
rename reverse references. Unsupported dependency scope escalates explicitly
to full audit. Incremental/full equality is an acceptance gate, not an assumption.

## Startup and resources

Default checker closure excludes viewer, compiler codegen, GPU and test runner.
Snapshot adapters batch object reads; hot requests use generation indexes and
reverse dependencies. No per-request full scan/process-per-file/retry sleep.
Measure cold/warm startup, actual closure, cache hit rate, latency and max RSS
under [the selected NFRs](../../02_requirements/nfr/traceability_sdn_slop.md).
Slop uses bounded neighborhoods and cancellable asynchronous source/layout;
hidden counts do not alter graph qualification.

## Delivery and proof

All WP0–WP7 remain in the [plan](../../03_plan/agent_tasks/traceability_sdn_slop.md).
Modern SSpec acceptance must traverse real CLI/extractor/runner/reporting paths.
Pure fixtures verify rules but cannot prove hook, deployed binary, remote gate,
viewer, supported-host performance, or full feature completion.
# Graph codec owner update — 2026-10-11

The pure common domain now includes graph_types_v1, graph_fields_v1,
graph_budget_v1, graph_schema_v1, graph_decode_v1, graph_encode_v1 and
graph_wire_v1 behind graph_v1. These owners import no app IO, process, clock,
network, compiler or test runner. The graph stores six named collections and
external provenance-record identities with explicit path/span availability.
Data consistency/reference closure remains separate from snapshot capture,
claim resolution, policy, visibility, execution eligibility and authentication.
Graph alias declarations preserve endpoints; this codec never folds them into
canonical self-edges. Detailed contract and scoped14/0 evidence live in
doc/05_design/infra/traceability_graph_codec_v1.md. Generic family dispatch and
other required families remain pending; no whole WP1 or admission claim follows.

## Common document owners — 2026-10-11

The shared domain now owns envelope types, primitive validation, text budgets and
stable byte order separately from family carriers. The legacy types barrel
reexports existing names; internal modules import their actual owner. Generic
dispatch supports three real families with explicit document quotas and one
strict source parse. Public family-from-value operations perform an independently
bounded O(nodes) structural walk before schema/preflight. This extra walk is
required because callers can construct values without the strict parser; source
byte/location evidence cannot be inferred from such values.

Authored declarations preserve conflicting claims and aliases for the resolver.
Exception review-state is untrusted data; calendar validation does not establish
current policy validity. Common owners import no application IO or clock. See
doc/05_design/infra/traceability_document_declarations_v1.md for table contracts.
Remaining families, startup/latency/RSS qualification and full scope stay open.

Review-derived raw-boundary repair adds verified dictionary cardinality before
keys and source-less cumulative key/header/string byte limits. Earlier12/0
acceptance and regressions remain pre-repair evidence; final raw controls5/0,
acceptance13/0 and affected graph14/0, qualification15/0, budget/order11/0
match the changed source. No whole AC, broad runtime or admission PASS follows.

## Targeted operation contract increment — 2026-10-11

Full20REQ/40AC/WP0–WP7 are unchanged. Root owns implementation/merge; sidecarsN/A;
Astra is final reviewer. Declarations major2 supplies explicit add/replace/suppress
without reinterpreting major1. Desired replacement and exact original tuple are
separate, and provenance/applicability references remain untrusted data. Native
strict-valid baseline3/3 -> initial typed3/0 and broader12/0 are distinct stages.
Actual policy authorization/stale-rule resolution AC006 remains required.
See doc/05_design/infra/traceability_link_operations_v2.md and its TDD report.

The unpublished work branch was rebased onto releasee2d56c2 with all89 prior
owned product files byte-identical (AstraPASS P0=0/P1=0). New canonical Stage2
qualification stopped before compilation at its10GB disk-space guard. Logs are
retained; no admission was emitted. Continue implementation independently while
build storage is unavailable; broad runtime and protected admission remain open.

## Conventional association kernel increment — 2026-10-11

Full20REQ/40AC/WP0–WP7 remain unchanged. Root owns implementation and merge;
sidecarsN/A; Astra is final reviewer. New pure-Simple convention owners validate
bounded supplied graph/policy facts and resolve exact registered unit, integration,
component and manual associations. They preserve corroborating origins, roles,
parameter identities, explicit exclusions and positive/negative membership.
Generator-manifest bindings are required before manual candidate recognition;
source-kind/group indexes and every node/group traversal are charged. Structural
association confers no requirement satisfaction, execution proof or eligibility.

Construction RED is an actual missing-module failure with zero executed examples.
Initial native6/0 was followed by Astra causal RED8/2 and grouped cycle2 GREEN26/0.
Astra final component/source/oracle/evidence review PASS P0=0/P1=0; no unchanged
green tests were rerun after convergence. See the conventions design, executable
modern SSpec, its host-extracted manual and TDD report. Ambiguous-input permutation
coverage validates diagnostics/lookups, not claim or generator/exclusion ordering.

Next WP2 work: actual graph extraction/byte binding, complete policy ownership,
explicit operation precedence/authority/stale rules and CLI integration. WP3
incremental/full equivalence must consume both positive and negative dependencies.
All execution evidence, qualifications, Slop surfaces and remaining plan gates
continue separately. Coverage/NFR/full core/MCP/LSP checks and admitted SPipe
manual generation remain open; no full AC/REQ done mark or runtime admission.

## Combined-source public codec boundary (unrun)

The compatibility `types_v1` barrel retains the qualification carrier and factory
names through their defining envelope/qualification modules. Dedicated
`trace_qualification_decode_v1` and `trace_qualification_encode_v1` keep
`TraceQualificationCodecLimitsV1`. Generic `trace_document_decode_v1` and
`trace_document_encode_v1` now require `TraceDocumentCodecLimitsV1`, including
bounded graph/declarations tables. This is an explicit source signature migration;
existing callers of generic APIs must use the document limits factory. Public
names remain, but old generic argument compatibility is not claimed.
Qualification consistency, strict schema refusal, canonical encoding and explicit
unsupported family/version refusal remain required. The merged spec adds a real
comparison of invalid-scope refusal through the dedicated and generic encoders.
This combined API, source and spec have not executed; historical evidence above
must not be promoted into a combined-source PASS.
