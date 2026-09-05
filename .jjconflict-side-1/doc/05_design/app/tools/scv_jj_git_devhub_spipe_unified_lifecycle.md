<!-- codex-design -->
# Unified SCV/JJ/Git/DevHub/Spipe lifecycle design

**Status:** Design for staged implementation  
**Research:** `doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_2026-08-25.md`

## Design goals

- Make lifecycle identity and evidence durable and locally usable.
- Preserve JJ editing and Git/forge compatibility during migration.
- Permit exactly one policy-checked mutation path for protected state.
- Make local review, remote review, integration, and product release distinct.
- Introduce functionality incrementally without rewriting existing SCV,
  DevHub, SJ, or Spipe surfaces.

## Ownership and dependency direction

```text
Human / LLM / IDE
        |
      Spipe                 policy/orchestration only
        |
      DevHub                typed lifecycle/provider API
      /    \
    SCV     SJ              durable graph / serialized mutations
             \
             JJ + Git       editing backend / public transport
```

SCV lifecycle modules must not depend on provider implementations. DevHub
domain objects depend on lifecycle interfaces; provider adapters implement
capability traits. SJ consumes typed requests and policy decisions but does not
own review/task/wiki business logic. Spipe consumes versioned JSON results.

## Core identifiers and records

Introduce opaque IDs for Change, Revision, Review, ReviewRun, Finding,
Approval, GateRun, GateBundle, Feature, Task, ReleaseLine, ReleaseCandidate,
Release, RemoteBinding, SyncConflict, and Publication.

`ChangeId` remains stable across rewrites. `RevisionId` is derived from the
immutable tree, parents, and policy-required metadata. JJ change/commit IDs,
Git OIDs, and provider patchsets are verified aliases, never canonical IDs.

Approvals and findings contain the exact RevisionId and evidence/policy
digests. Findings use semantic anchors (path, parser, symbol, syntax-node and
token fingerprints, entity ID) with line/column only as fallback.

## SCV lifecycle capsules

Suggested module roots:

```text
src/lib/scv/lifecycle/
  identity.spl        ChangeId/RevisionId and aliases
  review.spl          sessions, runs, approvals, findings
  evidence.spl        gates and bundles
  release.spl         lines, candidates, releases, provenance links
  work.spl            features, tasks, relations
  binding.spl         remote bindings, sync bases, conflicts
  store.spl           persistence facade and operation links
```

Each capsule exposes value-semantic records and a narrow store trait. Object
encoding and migration remain behind `store.spl`; provider formats do not enter
these modules. Cross-cutting audit/provenance is emitted as lifecycle operation
records rather than hidden callbacks.

The base codec uses schema `scv-lifecycle/1`, a canonical ordered field vector,
field count, and SHA-256 digest. Records live under
`.scv/lifecycle/<kind>/<entity-id>.scvl`; unsafe path/delimiter input and digest
or field-count mismatch fail before admission.

## Typed SJ transaction boundary

Replace mutation string translation progressively with a `VcsOperation` sum:
observe, snapshot, create change, rewrite stack, fetch, rebase, publish review
ref, integrate, backport, create release tag, publish release refs, recover, and
raw break-glass. Compatibility parsing may construct this AST.

`IntegrateRequest` contains exact candidate/base/expected-remote revisions,
target ref, policy digest, required gate profile, approvals, actor authority,
and dry-run/explain flags.

Integration state machine:

```text
resolve -> lease -> fetch/CAS-check -> refresh candidate
        -> invalidate stale review -> execute pinned gates
        -> verify SCV/JJ/Git trees -> CAS integration/main
        -> export/publish -> verify remote -> audit complete
```

Any mismatch aborts before publication. Gate correctness does not depend on
hooks. CI/rulesets independently repeat protected checks.

## DevHub typed domain/provider layer

Add domain commands for change, review, integrate, feature, task, release, and
sync while retaining compatibility commands. Providers advertise nested source,
review, task, knowledge, release, identity, and automation capabilities.

Every command supports versioned JSON, idempotency keys, dry-run, and explain.
Unsupported semantics fail explicitly. A local blocking verdict must not be
silently projected as a non-blocking provider comment.

`RemoteBinding` stores local entity identity, provider instance/kind/ID,
remote revision or ETag, authority policy, last pull/push digests, sync base,
and state. Synchronization computes a field-level three-way plan and persists
conflicts. Webhooks use a durable idempotent CloudEvents-compatible outbox.

## Review engine

Review lifecycle:

```text
draft -> evidence_collecting -> reviewing
      -> changes_requested | approved | abstained
      -> revision_updated -> revalidation_required -> approved -> integrated
```

Profiles are quick, standard, architecture, security, concurrency, performance,
release, and mission-critical. Routing combines deterministic evidence, risk
ownership tags, reviewer disagreement, missing evidence, analysis coverage, and
calibrated historical outcomes. It does not approve from self-confidence alone.

Default escalation constraints: depth 3, children 2, normalized-question cycle
detection, no same-reviewer repeated question, explicit missing-evidence
statement, and human disposition for unresolved high/critical findings.

## Version and release design

Use `release/version.sdn` as the product/version and compatibility-axis source.
Declared projections replace hard-coded release edits. `devhub version render`,
`check`, and `explain` manage and validate mirrors.

Release state:

```text
planned -> candidate_created -> source_frozen -> verified -> reviewed
        -> tagged_staging -> artifacts_staged -> publication_ready
        -> published -> verified_remote -> closed
```

Before publication a candidate can be abandoned. After publication it can only
be withdrawn and superseded. SJ creates the signed annotated Git tag, records
the tag object/signature/commit/SCV revision mapping, publishes with CAS, and
DevHub verifies remote artifacts and attestations.

## Feature/task/document projection

Durable feature manifests live under
`doc/08_tracking/feature/<FeatureId>/feature.sdn` and link substantive research,
plan, architecture, design, and spec documents in their existing layer trees.
Runtime state remains under `.spipe/run/<run-id>/state.sdn`.

Wiki synchronization uses managed regions plus a sync base so remote-maintained
content is preserved. Task and feature mutations always target an explicit
binding or displayed sync plan.

## Policy compilation

`.spipe/policy/*.sdn` is normative. `spipe policy check/compile/explain/audit`
generates or verifies human/agent rules, skill contracts, guide tables, and gate
entries. It fails closed on missing commands/gates, drift, contradictory field
authority, or protected paths lacking independent enforcement.

## Failure and recovery behavior

- Persist an operation after every durable boundary.
- Make provider requests idempotent and remote writes optimistic-concurrency
  checked.
- Retain recovery refs for partial publication.
- Report backend alias/tree drift through SCV doctor.
- A break-glass request requires authority, reason, expiry, audit event, and a
  reconciliation incident; it can never manufacture valid release evidence.

## Performance and observability

Protected integration may scan only policy-declared changed scope unless a
profile explicitly requires full-tree evidence. Cache gate results solely by
exact revision, tool, policy, and environment digests. Record phase timing,
cache hit/miss, gate counts, CAS conflicts, provider retries, and max RSS.

Initial budgets are measurement gates, not guessed hard failures: record warm
DevHub command latency, review-open latency, SJ dry-run planning latency, and
integration overhead on realistic repository fixtures before setting release
thresholds.

## Security boundaries

Credential handling stays in provider transports and must never enter SCV
objects, command JSON, audit payloads, or remote URLs. Protected mutations need
explicit authority. Release publication requires a complete exact-revision gate
bundle, independent approval policy, deterministic identities, CAS, and no
unresolved critical finding.

## Compatibility strategy

Existing commands remain wrappers until parity tests prove typed equivalents.
Observe/shadow modes precede mutation authority. The initial implementation
does not change content authority, public refs, release publication, or provider
behavior by default.
