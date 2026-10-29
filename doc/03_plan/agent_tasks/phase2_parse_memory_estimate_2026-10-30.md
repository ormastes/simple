# Phase2 Linux parse worker memory estimate — 2026-10-30

Owner: /root/build. Worktree: /tmp/simple-phase2-parse-memory-estimate-20261030.
Branch: work/phase2-parse-memory-estimate-20261030. Target: release/1.0.0.
Base: 8e98695970a813def06ed8ea57fc2276bd20e27c.

Scope: retain Attempt 6 Linux per-process RSS evidence, price only Linux parse
fanout conservatively, preserve 48 GiB hard enforcement, requested 20 build
threads, 9,000,000 KiB HIR estimate, Windows policy and other platform estimates.
Do not run a full Phase2 build in this lane. The initial policy regression must
pass and receive focused review before source can be integrated/frozen.

Evidence owner: `/tmp/simple-release-1.0.0-phase2-combined-build-attempt6-20261029`
and `/tmp/simple-release-1.0.0-phase2-attempt6-vmm-mono-evidence-20261029` are
immutable prior attempts; this worktree does not own or modify them.

Related evidence and tradeoff: `doc/08_tracking/bug/phase2_linux_parse_worker_estimate_2026-10-30.md`.

Integration evidence: attempt 7 stayed below the enforced tree cap but failed
on an unrelated HIR symbol. The guide lane handles narrow release-based landing;
full compiler qualification remains with the parent build lane. See the linked
bug record for exact receipts and limitations.
