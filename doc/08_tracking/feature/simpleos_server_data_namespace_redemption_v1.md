# SimpleOS server-data namespace redemption V1

## Status

- [x] Authenticated `/SERVERS.ELF` launch installs a bounded scheduler grant
  before task publication.
- [x] Current-TCB-derived, opaque two-phase redemption protocol exists:
  `Installed -> Redeeming -> Redeemed`, with exact rollback to `Installed`.
- [x] Exit/reap/exec lifecycle revocation covers every live protocol state.
- [x] Ambiguous redemption can tombstone the exact `Redeeming` or `Redeemed`
  row as `Quarantined`; exhausted generations retire rather than wrap.
- [ ] VFS owner mints and revalidates an opaque, generational DBFS root seal.
- [ ] Namespace owner prepares a task/lifecycle-bound capability and publishes
  it only after launch-ticket commit.
- [ ] Live C-ABI file syscall leaves enforce the namespace capability and its
  exact path/open-description policy.

## Phase-1 non-authority invariant

`ServerDataLaunchRedemptionTicketV1`, `Redeeming`, and `Redeemed` are scheduler
protocol coordinates only. They contain no DBFS handle, VFS namespace, file
descriptor, or filesystem permission. No public scalar-ID begin function is
provided; begin derives identity from the scheduler's canonical current TCB.

## Deferred ownership boundary

MountTable and VFS changes are intentionally outside phase 1. The later owner
must use unpublished preparation plus exact ticket commit, then publish its own
authority. It must rollback the ticket if preparation fails and quarantine the
exact ticket on an indeterminate pre- or post-commit cross-owner outcome.

The focused phase-1 spec covers the public pure transition graph. Exact ticket
matching, current-TCB derivation, checked-mutex failure, duplicate blocking,
and generation/nonce retirement remain registry-integration acceptance work;
they are not claimed as covered by the pure spec.
