<!-- codex-design -->
# Agent task plan: Simple distributed textual databases

**Date:** 2026-09-13  
**Selection:** Authority A / Adapters A / Operating B / Retention A  
**Status:** Implementation handoff plan  
**Merge owner:** primary implementation agent  
**Final reviewer:** Astra at highest available reasoning effort

## 1. Delivery rule

Implement the selected requirements in dependency order while allowing independent lanes to proceed in parallel. Git establishes shared bytes, jj manages local revisions, SCV supplies semantic identity and validation, and every local mutation passes through the existing SJ writer boundary. No lane may introduce an always-on database server, a second checkout writer, or provider/network I/O in the pure reducer.

The merge owner owns shared contracts and integrates all lanes. Sidecars may draft bounded slices, fixtures, or reviews, but they do not redefine shared interfaces. Astra performs the final architecture, security, traceability, and generated-manual review after the merge owner has assembled one candidate.

## 2. Frozen shared contracts (Wave 0)

Before any sidecar starts, the merge owner shall publish compiling fail-fast shells for these names. A contract change after Wave 0 requires notification to every dependent lane and re-running its contract tests.

### 2.1 Interface and model names

- `EntityUid`, `SettledAlias`, `EntityRef`, `ActorIncarnation`
- `IdentityMap`, `AllocatorState`, `SettlementReceipt`, `AcceptedBatch`
- `DbPatch`, `DbOperation`, `PatchPrecondition`, `CanonicalPatchCodec`
- `SchemaRevision`, `ReducerRevision`, `MergePolicy`, `SemanticReducer`
- `GitSettlementCapabilities`, `GitSettlementTransport`, `SettlementCoordinator`
- `TestDefinitionRevision`, `ConfigRevision`, `ConfigSetRevision`
- `ReproductionRevision`, `RunManifest`, `Observation`, `ExpectationRevision`
- `ExpectationRule`, `OutcomeEvaluation`, `BugOccurrence`
- `CiObservationCapabilities`, `CiObservationSource`, `NormalizedRunEnvelope`
- `ProviderBinding`, `BridgeIntent`, `BridgeDeliveryState`, `BridgeAdapter`
- `EvidenceManifest`, `EvidenceStore`, `RetentionPolicy`, `ResolutionQuality`
- typed errors `AdmissionError`, `SettlementError`, `IngestError`, `BridgeError`, `RetentionError`, and `ResnapshotRequired`

The exact type parameters and module placement are fixed by the architecture/detail-design owner, but names and responsibilities above are the cross-lane vocabulary. Pure types must not depend on Git, jj, `gh`, provider SDKs, processes, network, OS APIs, or credentials.

### 2.2 Scenario vocabulary

Executable system specs shall use these primary manual steps verbatim where applicable:

- `step("Create related entities while replicas are offline")`
- `step("Exchange immutable semantic batches")`
- `step("Settle aliases against the protected Git head")`
- `step("Verify accepted aliases and references on every replica")`
- `step("Publish a completed CI run manifest")`
- `step("Classify observations against a pinned expectation revision")`
- `step("Reconcile an uncertain provider delivery")`
- `step("Compact retained evidence without overstating resolution")`
- `step("Resnapshot stale work without resurrecting tombstones")`

Shared setup/checker helpers:

- `given_isolated_textual_db_replicas`
- `given_fenced_settlement_remote`
- `given_reference_operating_b_fixture`
- `given_github_contract_fixture`
- `given_non_github_git_contract_fixture`
- `given_ci_source_contract_fixture`
- `when_batches_are_exchanged`
- `when_settlement_races`
- `when_provider_ack_is_lost`
- `check_alias_bijection_and_high_water`
- `check_reference_closure`
- `check_materialization_digest`
- `check_observation_classification`
- `check_no_missing_result_became_pass`
- `check_delivery_reconciled_once`
- `check_retention_resolution_quality`
- `check_no_network_wait_under_sj_lease`

Any unavailable helper must initially fail fast with `assert(false)` or `fail("not implemented: <helper>")`. `pass_todo`, empty bodies, constant success, and `expect(true).to_equal(true)` are forbidden.

### 2.3 Transaction and lease invariant

The only permitted network workflow is:

1. Under the SJ lease, persist immutable intent and the local state needed for retry.
2. Release the SJ lease.
3. Perform Git/provider/CAS network work with bounded timeout and cancellation.
4. Reacquire the SJ lease and reconcile a typed result in a new transaction.

No network or provider wait may occur under the SJ lease. Tests must instrument lease ownership and network entry, fail at the boundary, and cover timeout, cancellation, crash, and uncertain acknowledgement.

## 3. Parallel wave graph

```text
Wave 0: L0 trust, authority, capability, schema and test contracts
                      |
          +-----------+-----------+
          |                       |
Wave 1: L1 identity/storage   L2 reducer/codec
          |                       |
          +-----------+-----------+
                      |
          +-----------+-----------+
          |           |           |
Wave 2: L3 Git     L4 evidence   L8 security/fault harness
          |           |           |
          +-----+-----+-----------+
                |
        +-------+-------+----------------+
        |               |                |
Wave 3: L5 bridge   L6 GitHub/CI     L7 retention/CAS
        |               |                |
        +-------+-------+----------------+
                |
Wave 4: L9 migration and compatibility
                |
Wave 5: L10 performance, system evidence, manuals and docs
                |
Wave 6: merge-owner verification -> final Astra review
```

L8 begins its harness in Wave 2 and continues adversarial review through Wave 5. L10 may prepare fixtures early but records acceptance evidence only against the integrated candidate.

## 4. Lane assignments

### L0 — Trust, authority, capability, and contract freeze

**Inputs:** selected feature/NFR requirements, research receipt, SCV lifecycle/write-lane design, deployed Git/jj/gh capabilities.  
**Outputs:** signed-operation trust model; ACL and key lifecycle; namespace/epoch fencing rules; schema/reducer compatibility matrix; Git/CI/provider/CAS capability traits; common errors; canonical scenario skeletons.  
**Dependencies:** none. Blocks all implementation lanes.  
**Likely paths:** `src/lib/scv/`, shared identity/codec/capability modules, `test/01_unit/lib/scv/`, architecture and detail-design documents.  
**Acceptance gates:** compile-only contract target; negative authorization fixtures; capability downgrade fails closed; key rotation/revocation and cross-domain replay cases defined; no transport identity is treated as operation authorization; all REQ-001..036 and NFR-001..015 have an owning lane and test ID.  
**Sidecar owner:** N/A; primary/highest-capability agent owns contract judgment.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L1 — Identity map and batched textual storage

**Inputs:** L0 contracts and canonical encoding boundary.  
**Outputs:** provisional identities; contextual settled aliases; forward/reverse maps; allocator high-water marks; accepted-batch registry; tombstone/merge/split knowledge; batched SDN mutation and rebuildable dense indexes.  
**Dependencies:** L0; coordinate canonical bytes with L2.  
**Likely paths:** `src/lib/scv/metadata_db.spl`, new focused modules under `src/lib/scv/`, unit/integration fixtures under `test/01_unit/lib/scv/` and `test/02_integration/lib/scv/`.  
**Acceptance gates:** offline collision/clone rollback tests; atomic forward/reverse closure; accepted numbers never reused; canonical SCV Change/Revision identities unchanged; bare context-free integers rejected; batch insert avoids whole-database copy per observation; crash boundary yields old-complete or new-complete view.  
**Sidecar owner:** Codex Spark for storage inventory and benchmark fixture drafting only.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L2 — Canonical codec, typed patches, reducer, and merge policy

**Inputs:** L0 schema/trust contract and L1 identity shapes.  
**Outputs:** domain-separated canonical codec; typed patch/preconditions; pure deterministic reducer; causal ordering; explicit conflicts; compatibility and replay registry; full/incremental materializers.  
**Dependencies:** L0; shared identity types from L1.  
**Likely paths:** new codec/reducer/policy modules under `src/lib/scv/`, unit/property specs under `test/01_unit/lib/scv/`.  
**Acceptance gates:** golden bytes across supported hosts; malformed framing/normalization rejected; batch ID plus different bytes quarantined; replay idempotent; different-field merge and same-field/delete-update conflict cases; authorization invoked before planning; equivalent accepted logs give identical digests; full and incremental output equal; pure-core dependency scan finds no provider/process/network/raw-runtime use.  
**Sidecar owner:** Claude Sonnet for independent merge-table and golden-vector review.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L3 — Fenced Git settlement and jj/SJ orchestration

**Inputs:** L0 Git capability contract, L1 allocator/map, L2 reducer/codec.  
**Outputs:** exact-head fetch; one-parent candidate construction; protected expected-old-OID publication; stale-head replan; uncertain-outcome read-back; signed hash-chained receipt validation; jj workspace integration through SJ.  
**Dependencies:** L0-L2.  
**Likely paths:** SCV settlement/transport modules under `src/lib/scv/`, app orchestration under the existing SCV tool path, fake Git remote fixtures under `test/02_integration/`.  
**Acceptance gates:** two integrators racing the same sequence accept no collision; successful-push/lost-ack retry does not reallocate; sole-parent and expected-old-head asserted; non-force/read-back/protection capabilities required; ancestry/epoch/high-water regression blocks allocation; network-under-SJ instrumentation remains zero; no Git attributes, hook, submodule, or unsupported jj behavior is assumed.  
**Sidecar owner:** Codex Spark for Git fixture construction; no authority-algorithm decisions.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L4 — Configuration-aware evidence model and runner compatibility

**Inputs:** L0 contracts, L1 references, L2 semantic operations, existing `RunnerTestDb`.  
**Outputs:** immutable revision entities; observation identity/dedup; expectation/evaluation separation; terminal coverage manifest; exact config and reproduction references; compatibility views for existing test-tracking readers.  
**Dependencies:** L0-L2; may proceed in parallel with L3.  
**Likely paths:** `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`, evidence/config modules under `src/lib/scv/` or the architecture-selected shared library, runner integration/system tests.  
**Acceptance gates:** A pass/B fail/custom-C fail coexist; custom failure has exact config and reproduction closure; PASS/XFAIL/XPASS/signature mismatch/infrastructure/NOT_RUN/INCOMPLETE/UNCLASSIFIED remain distinct; missing shards never imply PASS; same identity/digest deduplicates and changed digest quarantines; CI role cannot edit expectations, bugs, config promotion, or release qualification.  
**Sidecar owner:** Claude Sonnet for classification matrix and compatibility-reader review.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L5 — Durable provider-neutral bridge and lifecycle integration

**Inputs:** L0 provider contract, L2 patch protocol, existing lifecycle sync/outbox, L3 transaction pattern.  
**Outputs:** canonical committed intent; local lease/retry state; complete delivery state machine; last-common provider state; causation-loop prevention; uncertain-effect read-back; permission/deletion distinction.  
**Dependencies:** L0, L2, L3; uses evidence links from L4 where present.  
**Likely paths:** `src/lib/scv/lifecycle/sync.spl` and its model/store/codec neighbors; bridge contract fixtures.  
**Acceptance gates:** intent and semantic edit commit together; retries are idempotent; create-success/lost-ack does not blindly duplicate; scalar conflicts surface; comments/events deduplicate; permission loss is not deletion; unsupported remote fields are preserved or explicitly rejected; no network wait occurs under SJ lease.  
**Sidecar owner:** Claude Sonnet for state-machine fault table and loop analysis.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L6 — GitHub live adapter, CI ingestion, and non-Git fixtures

**Inputs:** L0 capabilities, L3 Git transport, L4 evidence envelopes, L5 delivery protocol.  
**Outputs:** GitHub Git settlement adapter; GitHub Actions bundle/event/poll ingestion; authenticated `gh` boundary; durable discovery/cursors; non-GitHub Git authority fixture; GitLab-CI and Jenkins-class event/poll/bundle fixtures.  
**Dependencies:** L3-L5.  
**Likely paths:** provider/app adapters under existing SCV application/HAL paths; integration/system fixtures; no provider SDK in pure core.  
**Acceptance gates:** real GitHub round trip in a controlled test repository; webhook loss repaired by overlapping poll; cursor advances only after durable normalization and canonical acceptance; reordered/replayed inputs preserve counts; malicious archive quotas/path/link/device/decompression cases fail before checkout; reproduction content never executes; scoped publisher credential is separated from untrusted jobs; every non-Git fixture satisfies the same capability contract.  
**Sidecar owner:** Codex Spark for fixture matrices; live credentialed evidence remains merge-owner controlled.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L7 — Retention, controlled evidence CAS, rollups, and hydration

**Inputs:** L0 storage/security contracts, L2 reducer versioning, L4 evidence model.  
**Outputs:** content-addressed quarantine and retained CAS; manifests/availability; 28-day class policy; evidence pins and closure; versioned mergeable rollups; exact/aggregated/restricted/unavailable queries; resnapshot catalog and stale-operation rebase.  
**Dependencies:** L0, L2, L4; bridge/CI artifacts integrate after L5/L6.  
**Likely paths:** retention/evidence catalog modules under `src/lib/scv/`, app commands, integration/performance fixtures.  
**Acceptance gates:** digest-verified closure for unresolved/release pins; manifest never substitutes for bytes; late input revises provenance; stable identities prevent count inflation; percentiles use mergeable sketches rather than averaged daily p95; pending work is never age-pruned; stale delete/update returns `ResnapshotRequired` without resurrection; deletion report accurately describes immutable Git limits; hydration and repository-growth NFRs measured.  
**Sidecar owner:** Codex Spark for fixture generation and storage accounting.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L8 — Security, fault injection, and invariant verification

**Inputs:** L0 threat/trust model and every lane's public boundary.  
**Outputs:** adversarial corpus; crash/fault scheduler; quota and canonicalization attacks; signature/replay/rollback tests; lease/network probe; credential-boundary audit; integrity property suite.  
**Dependencies:** begins after L0, integrates continuously.  
**Likely paths:** unit/integration/system security specs, test-only fake clocks/remotes/providers/CAS, audit scripts only where existing policy permits. Production implementation remains `.spl`.  
**Acceptance gates:** all NFR-010 zero-tolerance invariants hold; unknown versions and capability loss fail closed; no secret/PII-bearing field reaches Git under default policy; cross-repository/namespace/epoch/provider replay rejected; process crash at each durability boundary recovers; bounded queues exert backpressure without dropping oldest semantic work; audit proves no network call begins while SJ lease is held.  
**Sidecar owner:** Claude Sonnet as independent adversarial reviewer.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L9 — Migration, shadow export, reader compatibility, and rollback

**Inputs:** integrated L1-L7 candidate, inventory/baseline from L0, existing canonical reader paths.  
**Outputs:** versioned migration; shadow export and differential checker; ownership cutover; resumable checkpoints; rollback/recovery runbook; one-app-path compatibility adapters.  
**Dependencies:** L1-L7 and applicable L8 fault cases.  
**Likely paths:** SCV migration modules, existing test DB compatibility boundary, app command wiring, migration system specs and operator guide.  
**Acceptance gates:** no missing/duplicated entities or evidence; identity aliases and canonical Change/Revision IDs preserved; source and data publication remain independently operable; interrupted migration resumes idempotently; rollback restores a consistent old or new state; all OS/provider differences stay behind capability/HAL interfaces; no per-OS sibling or raw-runtime fallback.  
**Sidecar owner:** Codex Spark for inventory/differential fixtures.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

### L10 — Operating-B performance evidence, manuals, and documentation

**Inputs:** integrated implementation, Phase 0 baseline, frozen system-test plan and all NFRs.  
**Outputs:** reproducible million-row fixture/receipt; latency/RSS/recovery/repository-growth results; executable SPipe scenarios; generated manual; operator, security, migration, adapter, and troubleshooting documentation.  
**Dependencies:** prepares fixtures after L0; final measurement after L9.  
**Likely paths:** performance/system tests, `test/03_system/app/scv/feature/simple_distributed_textual_databases_spec.spl`, mirrored `doc/06_spec/03_system/app/scv/feature/simple_distributed_textual_databases_spec.md`, `doc/07_guide/`, and benchmark evidence paths selected by the test plan.  
**Acceptance gates:** NFR-001 receipt complete; ≥1M aliases and observations with 10k import; three recorded reference-machine runs; query/import/maintenance/RSS/RTO/hydration targets pass; ten-year-equivalent canonical Git pack and clone each ≤2 GiB; generated manual explains primary flows without raw test mechanics and reports zero stubs; `find doc/06_spec -name '*_spec.spl' | wc -l` is `0`.  
**Sidecar owner:** Codex Spark for fixture generation and raw-result collation; it may not waive thresholds or approve manual quality.  
**Merge owner:** primary implementation agent.  
**Final reviewer:** Astra.

## 5. Integration checkpoints

| Checkpoint | Required evidence before merge |
|---|---|
| C0 contracts | Shared names compile; ownership/traceability matrix complete; fail-fast scenario shells present |
| C1 semantic core | L1/L2 unit, property, golden-codec, purity, and crash-atomicity gates pass |
| C2 settlement/evidence | L3/L4 integration gates pass, including races, uncertain push, config matrix, and incomplete coverage |
| C3 adapters/retention | L5-L7 contract and fault fixtures pass; GitHub live evidence is distinct from non-Git fixtures |
| C4 migration | Shadow/differential/cutover/rollback and stale-client cases pass |
| C5 production candidate | L8 integrity suite and L10 SPipe/manual/NFR evidence pass; docs match implementation |

Each checkpoint is merged by the merge owner only after reviewing sidecar output against the frozen contracts. Generated output, broad exclusions, and any claimed `N/A` require normal/highest-capability review.

## 6. Requirement ownership and proof map

| Lane | Requirements primarily proved |
|---|---|
| L0 | REQ-005, REQ-006, REQ-011, REQ-022, NFR-011..015 |
| L1 | REQ-001..004, REQ-007, REQ-034 |
| L2 | REQ-010..015 |
| L3 | REQ-005..009, REQ-022, REQ-029 |
| L4 | REQ-016..021 |
| L5 | REQ-027..029 |
| L6 | REQ-023..026, NFR-012..013 |
| L7 | REQ-030..035, NFR-007..010 |
| L8 | Cross-cutting negative/fault evidence for REQ-001..036 and NFR-010..015 |
| L9 | REQ-003, REQ-015, REQ-034, REQ-036 |
| L10 | NFR-001..010 plus generated system evidence for REQ-001..036 |

Shared requirements require evidence from every listed owner; one narrow test cannot prove the broader requirement.

## 7. Cycle limits and escalation

- Maximum three verify/fix cycles per lane and three integrated verify/fix cycles for the feature.
- Run each acceptance command at most once after its relevant change in a cycle. Do not rerun an unchanged green check.
- An identical failure after the third cycle is reported with command, evidence path, suspected owner, and unblock condition; do not loop.
- Performance target failure produces a reviewed requirements change or a tracked performance bug with owner and evidence. It is never silently waived.
- Contract conflicts, authority ambiguity, unsupported Git protection/read-back, or evidence of namespace/high-water rollback stop settlement work immediately and fail closed.

## 8. Implementation-to-verify handoff

The merge owner hands off one immutable candidate revision plus:

1. Requirement-to-test matrix for every REQ and NFR.
2. Commands and receipts for unit, integration, property, system, fault, security, migration, and performance evidence.
3. GitHub live round-trip receipt and clearly labelled non-Git fixture results.
4. Phase 0 baseline and three-run Operating-B benchmark receipts.
5. Generated SPipe manual with zero stubs and its executable source path.
6. Capability matrix, threat model, key/credential inventory, and no-network-under-SJ-lease evidence.
7. Migration/rollback/resnapshot runbooks and exact known limitations.
8. Dirty-worktree ownership report separating unrelated concurrent-agent changes.

Verification then runs the repository `/verify` workflow once per criterion, including direct-env runtime guards and all compiler/lib/MCP/LSP checks triggered by the actual change scope. Verify must independently inspect placeholder/stub absence, requirement coverage, NFR evidence, architecture/design freshness, provider credential isolation, generated-manual quality, and the `doc/06_spec` layout invariant. A release handoff is forbidden until verification reports `STATUS: PASS`.

## 9. Final Astra review

Astra reviews the integrated candidate rather than isolated lane claims. The review must explicitly decide:

- whether fixed Authority A is actually fenced at the Git settlement boundary;
- whether canonical IDs, compact aliases, causality, and tombstones remain correct across crash, race, resnapshot, and migration;
- whether reducer purity and SJ single-writer ownership are mechanically enforced;
- whether GitHub-first live behavior and non-Git provider fixtures share honest capability contracts;
- whether observations can ever mutate expectations or turn missing evidence into PASS;
- whether raw evidence placement, deletion language, resolution quality, and CAS closure are honest;
- whether every Operating-B target has reproducible evidence rather than an assumption;
- whether the generated manual is usable and every REQ/NFR has direct proof.

Any P0/P1 finding returns the candidate to its owning lane within the remaining three-cycle cap. Final acceptance requires zero unresolved P0/P1 findings and a repository verification result of `STATUS: PASS`.
