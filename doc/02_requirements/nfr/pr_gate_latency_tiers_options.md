<!-- codex-research -->
# PR gate nonfunctional options

## N1. End-to-end under ten minutes (requested)

Description: from PR head update to required status success, target p95 under 10 minutes, including runner queue. Pros: user-visible fast landing. Cons: impossible to guarantee with the observed 500-plus hosted-runner queue and no self-hosted runners; requires fanout reduction and/or capacity, then measurement. Effort: XL, repo-wide workflow audit and capacity changes.

## N2. Execution under ten minutes, queue tracked separately

Description: required job runtime p95 under 10 minutes after runner allocation; report queue p95 separately and never call this an end-to-end pass. Pros: achievable by workflow reduction without pretending the hosted queue is solved. Cons: PRs can still wait hours to merge. Effort: M, a focused workflow plus timing evidence.

## N3. Best effort with fail-closed tiers

Description: reduce work by path class, preserve one mandatory status, and publish queue/runtime metrics without a fixed SLA. Pros: low risk and incremental. Cons: no latency guarantee. Effort: M, roughly 3–6 files.

User direction selects N1 as the target. Acceptance is contingent on measured p95 end-to-end evidence; a job-time-only result is not a pass.
