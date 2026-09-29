# Feature Expert: Simple distributed textual databases

## Role

Own process knowledge for the proposed SCV + jj + Git textual-database
protocol: offline semantic patches, centrally settled compact aliases,
configuration-bound CI evidence, provider bridges, and retention through
canonical semantic Git plus an external evidence CAS.

This feature extends SCV; it does not introduce an always-on database server.
Git establishes shared bytes, jj manages local revision work, SCV owns semantic
identity/validation/reduction, and SJ remains the only local mutation owner.

## Selected scope and status

The user selected **A/A/B/A** on 2026-09-13:

- fixed single settlement authority;
- GitHub Git + GitHub Actions as the first live adapters;
- the one-million-alias / one-million-observation operating tier;
- canonical semantic Git with raw evidence in a controlled external CAS.

**Status: design only.** Research, selected requirements, architecture, detail
design, system-test design, a parallel agent plan, and a generated/manual spec
exist. Production protocol modules and fixtures do not. The executable system
spec deliberately fails through named `UNIMPLEMENTED` helpers and is not PASS
evidence.

## Canonical feature artifacts

- Research:
  [local](../../../01_research/local/simple_distributed_textual_databases.md),
  [domain](../../../01_research/domain/simple_distributed_textual_databases.md),
  and the [original SCV + jj + GitHub proposal](../../../01_research/app/tools/scv/simple_distributed_textual_databases_scv_jj_github_2026-09-13.md)
- Requirements:
  [feature](../../../02_requirements/feature/simple_distributed_textual_databases.md)
  and [NFR](../../../02_requirements/nfr/simple_distributed_textual_databases.md)
- Architecture:
  [distributed textual database architecture](../../../04_architecture/simple_distributed_textual_databases.md)
- Detail design:
  [distributed textual database design](../../../05_design/simple_distributed_textual_databases.md)
- Plans:
  [system-test plan](../../../03_plan/sys_test/simple_distributed_textual_databases.md)
  and [parallel agent task plan](../../../03_plan/agent_tasks/simple_distributed_textual_databases.md)
- Executable specification:
  [SSpec source](../../../../test/03_system/app/scv/feature/simple_distributed_textual_databases_spec.spl)
  and [generated/manual specification](../../../06_spec/03_system/app/scv/feature/simple_distributed_textual_databases_spec.md)
- Guide:
  [operator and integration guide](../../../07_guide/app/tools/simple_distributed_textual_databases.md).
  Its commands remain proposed until the corresponding implementation lands.

## Required related experts

Read these before changing the corresponding boundary:

- [SCV feature expert](../scv/skill.md) — SCV identities, stores, Git/jj
  interop, integrity, and known implementation defects.
- [SCV migration expert](../scv_migration/skill.md) — migration sequencing,
  shadowing, compatibility, and rollout gates.
- [Database/SQL feature expert](../database_sql/skill.md) — `SdnDatabase`, WAL,
  batching/durability constraints, and pure-Simple database ownership.
- [Secure pure-Simple servers expert](../secure_pure_simple_servers/skill.md) —
  server-facing capability and security boundaries.
- [Test-runner layer expert](../../layer_expert/test_runner/skill.md) — immutable
  configuration/reproduction evidence and runner compatibility work.
- [Server transport/security layer expert](../../layer_expert/server_transport_security/skill.md)
  — credentials, untrusted ingestion, provider transport, and fail-closed I/O.
- [Async-runtime layer expert](../../layer_expert/async_runtime/skill.md) —
  bounded queues, cancellation, backpressure, and network waits outside leases.
- [Data-storage layer base](../../layer_base/data_storage/skill.md) — persistent
  formats, WAL/checkpoint, CAS, and retention ownership.

## Non-negotiable design contracts

- All local mutation crosses the existing SJ lease/capsule. Never add an
  independent Git, jj, CI, IDE, or provider writer.
- Never perform network/provider waits while holding the SJ/DB lease: persist
  intent, release, perform bounded I/O, then reacquire and reconcile.
- Settlement is a protected expected-old-head publication followed by read-back
  verification. Stale or uncertain outcomes re-check accepted history before
  any allocation is retried.
- Accepted numeric aliases are never reused, derived from row count, or treated
  as canonical replacements for existing SCV identities.
- Authorization precedes pure merge/reduction. Provider, Git, jj, process,
  network, clock, credential, and OS concerns remain outside the semantic core.
- Observations, expectations, and evaluations remain separate immutable facts.
  Missing or incomplete CI evidence never implies PASS.
- Webhooks are latency hints, not a durable queue. CI and issue bridges require
  durable discovery, idempotent ingestion, persisted cursors, and reconciliation.
- Canonical Git stores semantic state and evidence manifests; large raw evidence
  lives in controlled CAS. Queries report `exact`, `aggregated`, `restricted`,
  or `unavailable` honestly.

## Implementation gaps / handoff

The implementation plan remains wholly open. In particular, the repository
does not yet provide:

- compiling shared identity, patch, schema, reducer, receipt, capability, and
  typed-error contracts;
- batched metadata mutation suitable for the selected scale (the existing SCV
  metadata insert copies the database and allocates from row count);
- durable settlement transport through the admitted SJ/jj/Git path;
- immutable configuration, reproduction, observation, expectation, and
  evaluation entities at the test-runner compatibility boundary;
- trusted bounded CI quarantine/ingestion or live GitHub Actions ingestion;
- durable provider outbox state and a live GitHub Issues bridge;
- external evidence-CAS, retention/rollup, resnapshot, or hydration support;
- real system fixtures, requirement-covering PASS evidence, Operating-B
  benchmarks, security/fault injection, or migration evidence.

Start with Wave 0 in the agent plan. Freeze the shared contracts and keep every
test helper fail-fast until it observes production behavior. Do not convert the
current design-only SSpec into a passing placeholder.

## Verification state

There is intentionally no verification command that can establish feature
completion yet. The current executable spec is expected to fail. Once
implemented, verify all REQ-001..REQ-036 and NFR-001..NFR-015 using the
authoritative fixtures and evidence described by the system-test plan, then run
the repository's normal SCV/core, direct-env-runtime, generated-manual, and
production-readiness gates exactly once per acceptance criterion.

## Registry routing

`doc/00_llm_process/knowledge_registry.sdn` contains the narrow exact-feature
route to the `developer_tooling` group and this expert. The retained
longest-prefix feature/layer receipt is
`.spipe/simple_distributed_textual_databases/knowledge_selection.sdn`.

## Update rule

When this feature's research, requirements, architecture, design, plans,
specification, implementation, verification, or guide changes, update this
expert's links, status, and implementation gaps in the same change.
