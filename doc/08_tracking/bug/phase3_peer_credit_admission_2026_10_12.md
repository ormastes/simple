# Phase 3 peer CPU credit admission

Bug: `phase3_peer_credit_admission_2026_10_12`.
Canonical bug DB reconciliation is pending.

## Proven defect

The diagnostic B11 coordinator computes a peer worker ceiling as
`peer_budget // (6 GiB)` and subtracts it from 80. B10 also permits
512 MiB and 2 GiB reservations. Dividing the memory budget by 6 GiB therefore
does not bound the peer's configured CPU concurrency. Separate per-entry
exclusive claims prevent duplicate builds but do not enforce a global CPU
credit ceiling.

This defect belongs to the private bootstrap diagnostic coordinator; no
equivalent defect in the production Simple build runner is asserted.
The old aggregate-at-most-80 admission claim is withdrawn. Observed workers
were below 80; the defect is an invalid bound, not evidence of an actual
80-worker overrun or memory corruption.

## Containment and repair owner

On 2026-10-12 root and the Phase 3 Astra build owner wrote B11's supported
`STOP_DISPATCH` signal. Already-running jobs drain normally; outputs,
receipts, and caches are retained. No live source was edited and no worker
was killed. B10 continues its admitted queue.

After both existing cohorts are terminal, successor coordinators must use
explicit disjoint 40-job CPU allocations, at most 80 in aggregate, plus
independent host-memory fit admission. Do not derive CPU credits from a
memory reservation estimate. Remaining untried entries stay available;
completed and interrupted entries are not replayed.

The Astra Phase 3 build owner ran a mixed-reservation model regression once.
The old calculation permitted 121 workers (77 plus 44) for 512 MiB entries
under the recorded budgets. The explicit-credit model passed four checks:
reject 40 beside a 77-credit peer; admit 40 plus 40 with mixed reservations;
skip non-fitting heavy work and release its exact reservation on completion;
and admit 40 after the peer becomes terminal.

Evidence: `build/native_probe/phase3-worker-credit-repair-20261012-astra/RESULT.md`.
Result SHA-256:
`84f0b53400e09e3780707431c6c4660f72a68af8c195b8dd9de6179be9a36ffa`.
Policy SHA-256:
`0fb1e4dd4516f1a22b25ad9625d5512f6674bea92a414e9894c0fb06400d8a93`.
These are model checks, not qualification of a live successor coordinator.
Successor implementation and runtime admission remain pending.

## Scheduling finding

The live queue already scans past non-fitting tasks. A snapshot had roughly
4.47 GiB reservation space left, with only 6 GiB and 16 GiB unclaimed tasks
remaining. That snapshot did not demonstrate head-of-line blocking.
Higher utilization requires smaller compilation closures/header-based
primary builds; it cannot safely be obtained by disregarding memory tails.
