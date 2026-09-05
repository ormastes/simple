<!-- codex-research -->

# Release Process Hardening NFRs

**Status:** Selected
**Selection source:** User-supplied research document and its “Executive decision”

- **NFR-001 — Fail-closed safety:** Missing, malformed, stale, ambiguous, unsupported, unsigned, unreviewed, or unadmitted input shall produce a non-success result. No warning/fallback path may satisfy a required release gate.
- **NFR-002 — Determinism:** Identical canonical version/policy/candidate inputs shall render byte-identical normalized manifests and promotion plans. Timestamps and host paths shall not affect identity-bearing digests.
- **NFR-003 — Auditability:** Every mutation/admission decision shall name session, actor/authority, exact input SHAs/digests, operation, outcome, and evidence identity. No secret or token shall enter manifests, logs, tag messages, or generated manuals.
- **NFR-004 — Idempotency:** Repeating a read/check/dry-run operation with unchanged inputs shall return the same semantic result. Publication retry shall reuse the same artifact digest set and never overwrite an existing different identity.
- **NFR-005 — Concurrency safety:** Concurrent sessions shall not share mutable branches, worktrees, output directories, or writable caches. Protected-target integration and candidate/tag creation shall use CAS/create-once semantics.
- **NFR-006 — Maintainability:** Policy and release modules shall remain below 800 lines per file, avoid duplicated SemVer/policy parsing, use typed results, and meet the repository token-duplication gate for the owned directory.
- **NFR-007 — Portability:** Release planning and verification logic shall be pure Simple and host-neutral. OS/provider differences shall remain behind existing filesystem, process, VCS, signing, and hosting facades; no per-OS app siblings or app-layer target branches shall be added.
- **NFR-008 — Performance:** Version, policy, backport, candidate, and promotion-plan checks shall use caller-provided or once-loaded manifests and shall not perform repeated full-tree scans or per-request network calls. Representative local checks target under 250 ms warm latency on the repository fixture, excluding an explicitly requested projection render or external live-policy query.
- **NFR-009 — Security:** Release tools shall not accept tokens on printed command plans, construct credential-bearing URLs, expose arbitrary VCS mutation, or allow the initiating build identity to self-approve protected promotion. Path/ref/version inputs shall be validated before process or provider invocation.
- **NFR-010 — Evidence quality:** Every REQ shall have a real assertion and at least one relevant rejection path. Scenario manuals shall show the primary operator flow and typed evidence without relying on placeholder passes, raw test mechanics, or hand-written claims that the executable spec cannot prove.
- **NFR-011 — Compatibility:** The new Spipe plugin workflow uses an explicit pre-1.0 compatibility bump and schema versions. Legacy published tags remain readable/auditable but never become valid templates for new identity creation.
- **NFR-013 — Bounded convergence discovery:** Main/release discovery shall be read-only, explicitly scheduled or operator-triggered, rate-limited to its configured cadence, and based on one fetched snapshot per run. It shall emit no mutation credentials and shall not repeatedly poll GitHub from bootstrap hot paths.
- **NFR-012 — Bounded verification:** Each acceptance command runs once after unchanged PASS. One lane permits at most three distinct fix/verify cycles and stops on repeated identical failure/no-progress rather than looping.
- **NFR-014 — Self-review authority separation:** The checked-in tree may contain evaluator, projection, workflow, tests, and guidance, but no operator records or provider credential. The pure evaluator emits a plan only; the protected-environment default-branch workflow publishes a short-lived exact-state check. Generic Actions App trust is explicitly user-accepted and not independent security; release environments remain separate.
