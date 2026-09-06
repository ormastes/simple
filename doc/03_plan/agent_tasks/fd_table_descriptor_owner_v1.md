# FD Table Descriptor Owner V1 — Agent Tasks

- Implementation lane: Codex phase-B descriptor transaction capsule.
- Sidecar lanes: N/A; the state owner is one tightly coupled mutation domain.
- Merge owner: root agent.
- Final reviewer: independent normal/highest-capability static reviewer.
- Runtime verification: explicitly deferred by user instruction for this wave.

## Owner API gap phase

- Lifecycle key, snapshots, flags/status, lowest-free reservation, close
  reservation, context destruction receipts, and close finalization are owned.
- Legacy fd-table, syscall, scheduler, and backend wiring remains out of scope.
- Next merge owner must first supply scheduler pre-publication fork rollback
  and generational backend bindings.
- This phase is intentionally unverified.
