# Feature: Simple Distributed Textual Databases

## Raw Request

`$sp_dev research more and design and plan with astra and go pherallel Simple distributed textual databases: SCV + jj + GitHub`

## Task Type

feature

## Refined Goal

Define a research-backed, implementation-ready architecture and phased delivery plan for a local-first SCV semantic database protocol in which GitHub/Git settles shared bytes, jj manages local revisions, compact sequential aliases preserve distributed identity, and configuration-aware test and provider synchronization remain correct without an always-on database service.

## Acceptance Criteria

- AC-1: Local research identifies the current SCV identity, metadata DB, lifecycle synchronization, single-writer, test-runner compatibility, Git/jj integration, GitHub adapter, retention, and relevant knowledge-routing surfaces with exact source paths and explicit verified-versus-inferred labels.
- AC-2: Domain research verifies current primary-source behavior for Git fast-forward settlement and retention, jj Git compatibility, GitHub Actions/webhooks/artifacts/tokens, generic Git-server atomic reference updates, representative CI-server ingestion APIs, typed changeset conflict handling, temporary/distributed identity, and configuration-dependent test expectations; citations record access date and do not overstate precedent.
- AC-3: Feature and NFR requirement option documents provide 2–4 independently selectable choices with description, pros, cons, effort, dependencies, and measurable acceptance targets; final requirements are written only after explicit user selection and unchosen option artifacts are removed.
- AC-4: Every selectable requirement set preserves the non-negotiable protocol invariants: offline creation, permanent provisional-alias resolution, non-reused compact settled integers within an admitted authority namespace/epoch, typed semantic patches, deterministic conflict behavior for an accepted ordered log, immutable configuration/reproduction references, observation/expectation/classification separation, idempotent CI/provider ingestion, provider-neutral CI-server and Git-server interfaces, honest evidence availability, and bounded replay/retention semantics; selections vary deployment breadth, failover policy, scale, and retention placement only.
- AC-5: Architecture evaluates at least centralized settlement, multi-authority namespaces, storage/checkpoint layout, reducer and schema versioning, writer ownership, CI-server and Git-server adapter boundaries/capabilities, security boundaries, reconciliation, and failure recovery; it explicitly documents startup paths, hot paths, index/cache strategy, invalidation, batching, backpressure, latency/RSS/pack-growth targets, and MDSOC applicability.
- AC-6: Detail design specifies stable interfaces named `EntityRef`, `IdentityMap`, `DbPatch`, `MergePolicy`, `SettlementCandidate`, `ConfigRevision`, `ReproductionRevision`, `Observation`, `ExpectationRule`, `ProviderBinding`, `BridgeDelivery`, and `RetentionCatalog`, including ownership, state transitions, canonical serialization, error handling, transaction boundaries, and migration compatibility.
- AC-7: The system-test plan traces every selected `REQ-NNN` and `NFR-NNN` to executable SPipe scenarios covering racing integrators, lost acknowledgements, crash recovery, alias/tombstone replay, semantic conflicts, configuration-aware classifications, incomplete and duplicate CI ingestion from push- and pull-capable CI servers, GitHub and non-GitHub Git-server settlement, bridge uncertainty/reconciliation, privilege separation, and retention/resnapshot behavior, using built-in matchers and fail-fast placeholders only.
- AC-8: The mirrored manual design exposes the primary flows through `step("Create offline semantic changes")`, `step("Settle compact identifiers")`, `step("Classify configuration-bound evidence")`, `step("Reconcile provider changes")`, and `step("Retain exact or aggregated history")`; reusable setup/checker helpers use `setup_*`/`check_*`, scaffolds use `assert(false)` or `fail(...)`, and no executable `.spl` is placed under `doc/06_spec`.
- AC-9: The implementation plan splits dependency-ordered lanes for identity/storage, semantic reducer/merge, Git settlement, configuration/reproduction, CI ingestion, provider bridges, retention/migration, and fault-injection/performance evidence; each lane names inputs, outputs, dependencies, acceptance gates, sidecar ownership, merge owner, and final reviewer.
- AC-10: Knowledge routing is refreshed for affected `doc/` research/requirements/architecture/design/plan artifacts, a reachable-capability-focused `doc/07_guide/` entry, `doc/00_llm_process/feature_expert/simple_distributed_textual_databases/skill.md`, and relevant layer-expert links; unfixed gaps receive `doc/08_tracking/bug/` records with file:line and unblock conditions, and must-check ledger v3 rows name an owner and actionable unblock (`none` for PASS). Workflow/tooling instruction trees are N/A unless this design changes SPipe behavior rather than merely consuming it.
- AC-11: Research and design explicitly preserve the existing single-writer mutation boundary, avoid per-OS app duplication, keep provider/network I/O outside the pure reducer, and prohibit an implicit Rust-seed or raw-runtime fallback.
- AC-12: A highest-capability Astra review checks the merged research/options/design/plan for contradictions, unsupported claims, requirement traceability, generated-manual usability, scope exclusions, and unresolved safety/performance gaps before the phase can be called design-complete.

## Scope Exclusions

- Production implementation, migration, deployment, release, or provider credential use in this research/design/plan phase.
- A new always-on database server, automatic expectation approval from observations, arbitrary Git text merge as semantic settlement, or deletion of aliases still within the supported replay horizon.
- Claims of benchmarked performance or live bidirectional bridge completion without retained executable evidence.

## Cooperative Review

- Parallel Astra sidecars: current source/ownership research; existing documentation and knowledge-route research; external protocol/prior-art verification; identity/settlement architecture; test evidence/configuration design; CI/provider/retention threat and failure analysis.
- Merge owner: primary Codex agent (`/root`).
- Final reviewer: a fresh highest-capability Astra sidecar reviewing the merged artifacts after primary integration.
- Shared interfaces: `EntityRef`, `IdentityMap`, `DbPatch`, `MergePolicy`, `SettlementCandidate`, `ConfigRevision`, `ReproductionRevision`, `Observation`, `ExpectationRule`, `ProviderBinding`, `BridgeDelivery`, `RetentionCatalog`.
- Manual flow helpers: `step("Create offline semantic changes")`, `step("Settle compact identifiers")`, `step("Classify configuration-bound evidence")`, `step("Reconcile provider changes")`, `step("Retain exact or aggregated history")`.
- Setup/checker helpers: `setup_replica_fixture`, `setup_settlement_fixture`, `setup_test_evidence_fixture`, `setup_bridge_fixture`, `setup_retention_fixture`, and corresponding `check_*` helpers.
- Fail-fast placeholder policy: unfinished executable scaffolds must call `assert(false)` or `fail(...)`; placeholder passes and empty bodies are forbidden.
- Generated-manual review owner: final Astra reviewer, with primary Codex merge owner responsible for fixes.

## Phase

design-done

## Log

- dev: Created the state file with 12 acceptance criteria (type: feature) and established the parallel Astra review contract.
- research: Six parallel Astra lanes inspected source ownership, knowledge routing, Git/CI protocols, identity settlement, evidence/bridges/retention, and adversarial threats.
- research-review: Initial Astra review found five P1 gaps; the option set and research were corrected and re-reviewed. Final result: READY with zero P0/P1 findings.
- research-extension: Parallel Astra lanes added Gitea/Forgejo, Buildkite, Azure Pipelines, and Azure Repos capability evidence. The provider-neutral contracts now cover hosted, self-hosted, webhook, polling, bundle-only, and exact-ref-CAS variants; requirement selection remains pending.
- requirements: User selected A/A/B/A. Final feature and NFR requirements were written and unchosen option documents were removed.
- design: Parallel Astra lanes produced architecture, detail design, 51-contract/153-scenario system-test design, generated manual, implementation plan, guide, and feature-expert routing.
- design-review-1: Astra reported zero P0 and four P1 findings: non-cyclic receipt binding, typed immutable revision references, missing `BridgeDelivery`/`RetentionCatalog`, and stale tracking/state evidence. Fixes are in progress; duplicate manual removed and tracking/route evidence refreshed.
- tooling: SPipe command routing check passed. Docgen produced one complete manual with 0 stubs, but the available `bin/simple` identified itself as a Rust bootstrap seed; this is structural design evidence only and not production acceptance evidence.
- design-review-2: Astra cleared the original P1s and identified a hosted-GitHub trust-boundary ambiguity; the design now makes the trusted SCV/GitHub App worker the semantic verifier and GitHub only the protected-ref/CAS authority.
- design-review-3: Astra identified one remaining architecture/detail mismatch over prepared receipt publication; both now use local journal-before-settlement and one complete receipt-index entry after accepted-head read-back.
- final-review: DESIGN PASS with zero P0/P1. The remaining editorial sequencing P2 was corrected by constructing and journaling `P` before publishing the journaled candidate.
