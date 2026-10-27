# SCV GitHub topic writer v1 test plan

The canonical executable scenarios are in
`test/03_system/app/scv/feature/scv_gateway_github_topic_v1_spec.spl`.
They exercise the actual candidate-owner Git command only against isolated
local bare repositories. GitHub read behavior is represented by an injected
typed port in the BDDs; no live GitHub write is part of testing.

| Requirement | Scenario coverage |
|---|---|
| TOPIC-001: derive and write only one generated topic ref | Absent ref creation; reject protected, malformed, and arbitrary refs; preserve base ref. |
| TOPIC-002: reject a competing destination | Existing ancestor ref is not advanced; preflight/readback reports conflict. |
| TOPIC-003: reconcile ambiguous outcomes | Lost acknowledgement followed by exact ref/OID readback; same request retry is idempotent without a second push. |
| TOPIC-004: fail closed on missing authority/state | Missing durable outbox, disabled host topic capability, and unauthenticated HTTP request cause no Git write. |
| TOPIC-005: keep topic publication distinct from acceptance | Results say `not_acceptance`; exact OID is required before `topic_branch_published`. |

## Run evidence

The native Simple runner is not admitted in this worktree. Simple/SPipe
execution and doc generation are **NOT_RUN**. A separate temporary local Git
transport check may prove empty-expected lease behavior, but cannot substitute
for the Simple BDD or qualify the HTTP credentials, host, or server.
