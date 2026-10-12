# Distributed build and Caret control: selected feature requirements

Selection: user explicitly requested “impl all and land on the branch” on 2026-10-12. All F01–F16 and DBC-001–024 are selected, including M8 platform and transport work. Preserve MDSOC++ MD-01–07. This selection does not imply runtime qualification or authorize external host enrollment/signing publication.

## 4. Non-negotiable requirements

Requirement IDs below are proposed additions, to be connected to existing ORCH/build/Caret requirements rather than replacing them.

| ID | Requirement |
|---|---|
| DBC-001 | Caret controls sessions and presents approvals; the remote service independently enforces authorization |
| DBC-002 | Session host, build execution environment, target platform and test runtime are explicitly separate |
| DBC-003 | Unknown host, changed host identity, missing policy, unsupported isolation, or unmatched exact environment fails closed |
| DBC-004 | Native LLM CLI/provider authentication and permission interfaces remain authoritative; no automatic approval of provider prompts |
| DBC-005 | SSH credentials, node TLS identity, LLM provider credentials, receipt signer and release/deployment signer have separate scopes |
| DBC-006 | Human approval is an authenticated event bound to an immutable request, not an LLM-supplied `confirm: true` |
| DBC-007 | Every job uses a content-identified snapshot, toolchain and effective environment; no mutable branch alias remains at execution |
| DBC-008 | Existing build manager owns compilation dependencies and output admission; common job service owns placement/resource admission |
| DBC-009 | Each execution has owned process-tree identity, attempt root, limits, cancellation and terminal settlement |
| DBC-010 | Only immutable caches are shared across independent jobs; mutable state is attempt- or explicitly qualified group-owned |
| DBC-011 | Native-container requests never silently downgrade to a process, sandbox, WSL or VM |
| DBC-012 | SHS authoring and direct SDN produce the same validated, digest-bound deployment/build plan |
| DBC-013 | GitHub evidence reuse is check-specific, source/environment/policy-bound and enforced by protected verifier code |
| DBC-014 | Repository updates do not mutate active snapshots; retry scratch cleanup does not remove user edits |
| DBC-015 | Node health, capability discovery, compilation and real execution are separately evidenced |
| DBC-016 | Quotas cover local and remote cache bytes, disk reserve, pinned objects, temporary transfers and retention |
| DBC-017 | Session detach, LLM-turn cancellation, job cancellation, session termination and history deletion are distinct operations |
| DBC-018 | Native control/configuration is SDN or bounded binary; required external formats stay at adapters |
| DBC-019 | A compromised build/session cannot obtain an infrastructure signer or broaden its own authorization |
| DBC-020 | Revocation and stale-generation checks apply to existing sessions, new input, submissions and publication |
| DBC-021 | A transport timeout never proves process death or permits blind duplicate execution |
| DBC-022 | Implementations report PASS, FAIL, BLOCKED, UNSUPPORTED, NOT_RUN, CANCELLED and unknown ownership distinctly |
| DBC-023 | Shared ownership and platform variance use existing SOSIX/MDSOC++ conventions without parallel registries |
| DBC-024 | SSH-first delivery remains possible without waiting for pure-Simple TLS, a new orchestrator, or RDMA |

---

