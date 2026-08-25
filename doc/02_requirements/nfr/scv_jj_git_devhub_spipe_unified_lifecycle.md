# Unified lifecycle non-functional requirements

- NFR-001 Safety: malformed identities, stale CAS state, stale approvals, incomplete/vacuous evidence, unknown policy, and semantic projection gaps fail closed.
- NFR-002 Portability: DevHub and SJ app logic use one codebase; host/provider variation stays behind typed facades and adapters.
- NFR-003 Auditability: every protected plan names actor, authority, exact revisions, policy/gate evidence, backend equivalence, CAS, verification, and audit steps.
- NFR-004 Recovery: every durable boundary is idempotent or operation-linked; partial remote work is explainable and reconcilable.
- NFR-005 Performance: no full-tree scan, repeated reread, or subprocess occurs on a hot request path without explicit policy; cache keys bind revision/tool/policy/environment digests.
- NFR-006 Security: credentials never enter lifecycle objects, JSON results, audit payloads, or remote URLs.
- NFR-007 Compatibility: public Git transport and signed annotated tags remain authoritative during migration; SCV content authority waits for S0-S6 proof.
- NFR-008 Quality: new pure-Simple code targets 80% branch coverage, canonical SSpec matchers, non-vacuous evidence, files below 800 lines, and zero stubs.

