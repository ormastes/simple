# Bootstrap frontend budget pins one HIR worker

Status: FIXED on fanout hosts; Windows one-worker pin is by design.

## Premise triage 2026-11-05 (mirp2-F, origin/release/1.0.0)
Original premise: the bootstrap frontend policy pinned
`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=3000000`, admitting one HIR worker.

`scripts/bootstrap/lib/product-frontend-policy.shs` on release/1.0.0 now sets,
on every fanout host (all non-Windows), the default share to the enforced cap
itself, `product_policy_max` to the resolved ceiling, and prices a HIR worker at
9000000 KiB (parse at 3800000, Linux 25165824) so the cap decides worker
count (header comment lines 1-10: "A separate 3000000 KiB share pinned one HIR
worker at any --threads" — the fixed behaviour). The 3000000 pin remains only in
the Windows branch, where `command-snapshot.shs` pins one frontend by design.
CLOSE as fixed; Windows fanout would be a new feature row, not this bug.
