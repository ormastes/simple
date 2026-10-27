# SCV GitHub topic writer v1 test plan

The canonical executable scenarios are in
`test/03_system/app/scv/feature/scv_gateway_github_topic_v1_spec.spl`.
They exercise the actual candidate-owner Git command only against isolated
local bare repositories. GitHub read behavior is represented by raw injected
JSON passed through the strict decoder; no live GitHub write is part of testing.

| Requirement | Scenario coverage |
|---|---|
| TOPIC-001: derive and write only one generated topic ref | Absent ref creation; reject protected, malformed, and arbitrary refs; preserve base ref. |
| TOPIC-002: reject a competing destination | Existing ancestor ref is not advanced; preflight/readback reports conflict. |
| TOPIC-003: reconcile ambiguous outcomes | Lost acknowledgement followed by exact ref/OID readback; same request retry is idempotent without a second push. |
| TOPIC-004: fail closed on missing authority/state | Missing durable outbox, disabled host topic capability, and unauthenticated HTTP request cause no Git write. |
| TOPIC-005: keep topic publication distinct from acceptance | Results say `not_acceptance`; exact OID is required before `topic_branch_published`. |
| LANDING-001: read only configured repository/head/base authority | Raw provider checks numeric repository identity before/after, exact generated head/base, current protected ref, and complete bounded pagination. |
| LANDING-002: distinguish PR lifecycle without false acceptance | Open, closed-unmerged, merged-needs-validation, absent, ambiguous, and unknown responses are asserted; merged observations remain `not_acceptance`. |
| LANDING-003: durable retry and scope | Digest-derived immutable observations distinguish open-to-merged changes and replay identical results; read and observation-write capabilities deny before provider access. |

Required check verification, merge-commit tree authentication, protected-ref
ancestry proof, and native accepted-result import remain out of scope until
their owning interfaces are admitted. No test may claim these as verified.

## Run evidence

The native Simple runner is not admitted in this worktree. Simple/SPipe
execution and doc generation are **NOT_RUN**. A separate temporary local Git
transport check may prove empty-expected lease behavior, but cannot substitute
for the Simple BDD or qualify the HTTP credentials, host, or server.
