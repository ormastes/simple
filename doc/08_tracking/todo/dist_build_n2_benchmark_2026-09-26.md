# Distributed build: N2 fast-feedback benchmark admission

Status: OPEN

The user selected N2. A numeric-only nearest-rank P95 helper exists, but there is no admitted benchmark fixture set or raw-sample evidence for the complete staged hook, one-ref pre-push gate, or eligible warm ordinary-change preflight. The existing twelve Clang archive probes and one synthetic push sample do not prove P95.

On 2026-09-26, the current `check-pr-fast.shs --selftest` completed 27/27 fixture scenarios, including docs-only PASS, whitespace FAIL, unsupported-path ERROR and receipt rejection cases. This checks the hook's fixture behavior only; it supplies no full-invocation P95 samples or signed-input snapshot proof and does not satisfy N2.
The current `check-push-must-pass.shs --self-test` also completed 24/24 ledger, budget and dispatcher fixtures on this host. Its 500 ms budget-overrun fixture correctly returned an unknown verdict rather than a pass. This is failure-behavior evidence, not a timed one-ref pre-push run or an N2 result.

Acceptance: create pinned fixtures and a pure-Simple measurement owner that retains at least 20 independent full invocations per row, raw durations and outcomes, exact source/ref/toolchain/policy/runtime identity, executed mandatory gate receipts, cache state, cold/multi-ref separation and memory/transfer costs. Require staged-hook P95 ≤5 s, one-ref pre-push P95 <10 s, and eligible warm preflight P95 <60 s using nearest rank. Any incomplete gate or unsupported host prevents PASS. Run once on an admitted self-hosted Simple runtime after the runner is repaired; preserve the session verification cap.

Astra's V4 review found three additional live-runner blockers: the current observation provider reports RSS/cgroup metrics rather than private/unique/PSS; its native backend does not prove descendant containment or `tree_empty` for a whole hook; and it supplies `/dev/null` on stdin, so a pre-push run needs an exact retained one-ref input fixture through a qualified wrapper. The [N2 evidence contract](../../03_plan/agent_tasks/dist_build_n2_evidence_2026-09-26.md) now rejects incomplete copied samples, mixed source/ref identities, and non-push fixtures carrying outgoing refs; its focused spec remains unrun. It is not an execution collector or a live N2 receipt. The collector must prove fixture-field binding and independent runs; mixed memory metrics must keep their labels and measurement methods.

Owner handoff: [distributed-build local handoff](../../03_plan/agent_tasks/dist_build_local_handoff_2026-09-26.md) and [N2 requirements](../../02_requirements/nfr/dist_build_scheduler.md).

The copied-sample checker now binds runtime, toolchain, policy, host and
warm-state fields per sample. Its focused spec adds changed-runtime,
changed-host and changed-warmth rejection cases; they remain unrun under this
session's self-hosted verification cap. Live collector provenance, full
invocation capture and raw samples are still required.
