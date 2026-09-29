<!-- codex-design -->
# Simple Unified Debugging and Evidence — NFRs

**Status:** Approved for design
**Date:** 2026-08-14

- **NFR-001 Security:** deny by default when policy, privilege, build identity,
  or adapter identity cannot be established. No raw secrets, SQL bind values,
  browser credentials, mobile identifiers, or arbitrary memory enter normalized
  evidence without explicit policy.
- **NFR-002 Truthfulness:** support and verification are orthogonal. Blocked and
  unavailable rows remain visible and never count as pass.
- **NFR-003 Evidence integrity:** manifests bind raw and normalized artifacts to
  cryptographic digests, build/symbol identity, capture time, adapter version,
  policy and receipts. Raw artifacts remain immutable after capture.
- **NFR-004 Availability/isolation:** an adapter crash or timeout shall not crash
  `DebugServiceV1` or corrupt other sessions. External adapters default to
  isolated processes with bounded messages and deadlines.
- **NFR-005 Performance:** warm local service startup p95 ≤ 250 ms; session lookup
  p95 ≤ 1 ms; passive event ingestion p95 ≤ 5 ms/event at 10k events/s; doctor
  p95 ≤ 2 s excluding explicitly reported external-tool/device waits. No hot
  request may perform a full-tree scan, repeated source read, or unbounded
  subprocess spawn.
- **NFR-006 Resource bounds:** queues, rings, payloads, artifacts, subprocesses,
  and sessions have configured bounds and observable drop/eviction counters.
  Default passive instrumentation adds ≤ 2% CPU and ≤ 3% RSS on the declared
  representative fixture.
- **NFR-007 Determinism:** normalized ordering, IDs derived from stable inputs,
  redaction, and offline inspection shall be deterministic for identical input
  bundles. Replay must label nondeterministic and unavailable inputs.
- **NFR-008 Compatibility:** additive minor-version wire changes preserve older
  readers; major mismatch fails clearly. DAP compatibility and existing
  `DebugTarget`/`ProfileTarget` behavior remain covered during migration.
- **NFR-009 Portability:** unsupported host/device facilities produce truthful
  blocked evidence, not build failure for unrelated adapters.
- **NFR-010 Testability:** every feature requirement maps to at least one
  executable system/integration/unit, evidence-fixture, or physical-target
  scenario. Live claims require live evidence; parser fixtures prove only
  fixture behavior.
- **NFR-011 Auditability:** all control and mutation decisions have receipts;
  cleanup is idempotent and auditable; temporary probes expire even if a client
  disconnects.
- **NFR-012 Maintainability:** shared contracts have one owning module and one
  merge owner. Adapters depend inward on contracts; domain-specific payloads use
  registered extensions rather than edits to the root service.
- **NFR-013 Cost learning:** token accounting shall not guess missing values.
  Comparable averages use a documented cohort and exclude unavailable samples;
  the closure gate and knowledge link are machine-checkable.
