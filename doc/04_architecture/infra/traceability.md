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
