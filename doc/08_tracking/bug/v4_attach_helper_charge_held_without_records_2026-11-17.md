# V4 agent attach: helper charge held with no settle or cancel record (2026-11-17)

- id: `v4_attach_helper_charge_held_without_records_2026_11_17`
- severity: P2
- status: open (accepted fail-closed behaviour; operator reconciliation is the only exit)
- design: `.spipe/simple_orchestrator/continuation_20261116/milestone_0022_native_attach/DESIGN.md`
  sections 14.3 (P2-D), 15.6 and 16 (P3-2, final list); milestone_0021 DESIGN 13.3/13.4/14A F4/F6.

## What happens
A V4 Linux service attach helper (`attach-broker`) can reach a state where its Host
reservation row is charged and there is no record that lets anything release it:
no native record to settle (S/F/B need `native_recover`, which needs `broker.claim`),
and no journal refusal R to authorize `host_helper_cancel_unconsumed_v1`. The row
stays `Uncertain`/charged in `host_capacity_projection_v1`. There is no deadline
recovery for it.

## Charged-forever states (final list, milestone_0022 16 P3-2)
1. `{}`: helper begin committed, the open core never ran (crash between begin and the
   first core call).
2. `{PA}` alone: the consume record was published, the spawn outcome is unknown.
3. Any failed open after `action_begin_v2` (including transient IO errors from
   `workload_publish_v3`): provider custody advanced, no R.
4. A crash between a `NoCustody`/`SpawnRejectedRetired` detection and the journal R write.
5. A post-consume R publish failure (`{PA}`, spawn provably dead).
6. `{R}`/`{R,X}` with an invalid or unreadable helper store.
7. A mirror R or X that differs from its journal copy (permanent Err).
8. A permanent failure of the X settle.
Also charged forever on the agent side: helper begin committed an executing owner but
returned no lease (`begin_attempted`, milestone_0021 14A F6).

## Behaviour (fail closed, never a silent release)
- Agent: the attachment is `failed`; the release port classifies the state up front as
  typed non-retryable, so the attachment goes to `release-blocked` and the agent to
  `wedged` in the same call (14A F4). Destroy is skipped; close reports
  `attachment-release-blocked`; `request_cancel` returns the wedged error.
- Service: close keeps the capacity owner and the journal open while the attachment is
  live. At the next start `host_linux_service_drain_v4` refuses the flip
  (`linux-service-drain-quarantined`): the whole service stays quarantined.
- The agent never starts a second attach in the same incarnation (`attachment_consumed`).

## Operator path
Reconcile the helper row by hand (inspect the journal row, the helper store markers and
the native group), then settle or cancel it through an operator-signed path. No such
operator command exists yet.

## Next step
Design an operator-signed helper settlement for these rows, or a native proof of absence
that can authorize a cancel without R.

## Update 2026-11-17 (milestone_0026): spawn-carrier charge is no longer in this class
Release sequences F (spawn only) and B (session and spawn) previously answered Blocked
(`...-fallback-release-unbound`) because `quiesce_fallback_core_v3` / `settle_retired_core_v3`
did not exist. Both cores now exist and are called by the release port, so a held spawn
carrier is classified as releasable (not charged forever) and released through the container-side
retirement and settle_retired (NOT_RUN: no runnable binary; never compiled). The eight no-record states above are unchanged and this row stays open; only a
`Rejected` spawn (no owner, absence unprovable) still ends Blocked.
