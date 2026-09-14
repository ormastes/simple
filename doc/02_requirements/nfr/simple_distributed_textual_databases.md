# NFR requirements: Simple distributed textual databases

**Date:** 2026-09-13  
**Selection:** Operating B + Retention A  
**Status:** Selected requirements; targets require Phase 0 baseline evidence

## Reproducible measurement contract

- **NFR-001 — Fixture receipt:** Every performance claim shall record dataset generator and digest, machine/OS/filesystem/tool versions, Git/jj/object format, cold/warm definition, warm-up and sample counts, percentile method, command, timeout, and raw evidence path.
- **NFR-002 — Scale:** The required corpus shall contain at least 1,000,000 aliases and 1,000,000 retained observations, with a 10,000-observation import batch and representative conflicts, tombstones, provider identities, artifacts, and rollup cohorts.
- **NFR-003 — Query latency:** On the selected reference machine and warm indexed state, alias resolution and current-status query p95 shall each be ≤100 ms; deduplication lookup p95 shall be ≤250 ms. Report p50/p95/p99.
- **NFR-004 — Import resources:** A 10,000-observation validated import shall complete in ≤5 s with maximum RSS ≤256 MiB, excluding provider network transfer but including decode, authorization, reference validation, deduplication, and patch construction.
- **NFR-005 — Maintenance resources:** A 1,000,000-row compaction dry-run shall complete in ≤10 s and ≤512 MiB RSS. A 10,000-operation resnapshot/rebase shall complete in ≤60 s.
- **NFR-006 — Recovery:** Settlement service recovery after process crash or canonical-remote restoration shall have RTO <10 minutes once dependencies are reachable. Outage spooling shall be bounded with explicit backpressure and shall never discard the oldest pending semantic work.

## Retention and integrity

- **NFR-007 — Exact window:** Routine raw observations shall remain exactly retrievable for at least 28 days. Daily summaries shall state reducer/aggregation version and provenance.
- **NFR-008 — Archive closure:** Every unresolved-failure or release-pinned evidence set shall have 100% digest-verified dependency closure in controlled CAS before provider expiry; hydration of a 100 MiB retained bundle shall complete in ≤5 s on the reference machine excluding remote transfer.
- **NFR-009 — Semantic repository growth:** A reproducible ten-year-equivalent workload at the selected Operating B tier shall keep the canonical semantic repository's packed objects and full-clone transfer each ≤2 GiB; external raw CAS bytes are reported separately.
- **NFR-010 — Integrity:** Verification shall demonstrate zero accepted-ID reuse, reference resurrection, count inflation, lost acknowledged batches, observation-to-expectation privilege escalation, or unauthorized secret-bearing fields, and 100% accepted reference/receipt/archive digest closure.

## Security and compatibility

- **NFR-011 — Cryptography agility:** Patch signatures and digests shall record algorithm and version, use domain separation, support key rotation/revocation, and prevent replay across repository, namespace, epoch, and provider domains. No single algorithm is permanently hard-coded into the schema.
- **NFR-012 — Least privilege:** Settlement and CI publisher credentials shall be repository/project scoped and inaccessible to untrusted build steps. Authenticated transport identity shall not substitute for operation authorization or content attestation.
- **NFR-013 — Fail closed:** Unsupported Git protection/CAS/read-back capabilities, unknown schema/reducer versions, high-water/ancestry regression, malformed canonical encoding, quota violations, and ambiguous remote effects shall return typed errors and shall not publish settled identity.
- **NFR-014 — Determinism:** Given identical schema/reducer versions and the same accepted ordered batch log, full and incremental materialization shall produce identical canonical state/tree digests on every supported host.
- **NFR-015 — Portability:** The pure semantic core shall contain no provider SDK, subprocess, network, OS-specific, or raw runtime dependency. Git/CI/provider adapters shall satisfy the same fixtures through capability interfaces.

## Baseline and acceptance protocol

Phase 0 shall measure current metadata load/insert/save behavior, Git pack/clone size, and existing runner query/update behavior before implementation. Selected thresholds are not relaxed silently: failure produces a reviewed NFR change or a tracked performance bug with owner, evidence, and unblock condition. Acceptance requires three recorded runs on the declared reference machine and retention of the raw receipts.

