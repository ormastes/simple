# V4 agent attach: helper charge held with no settle or cancel record (2026-11-17)

- id: `v4_attach_helper_charge_held_without_records_2026_11_17`
- severity: P2
- status: partially fixed 2026-11-19 (milestone_0036: deadline reap + controller-signed `helper-abandon`; source-authored, NOT_RUN, see `## Update 2026-11-19` for what stays held)
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

## Update 2026-11-19 (milestone_0036): deadline reap and signed operator abandon (source-authored, NOT_RUN)
Owner decision: both. Design: `.spipe/simple_orchestrator/continuation_20261116/milestone_0036_attach_charge_recovery/DESIGN.md`.
- Deadline reap (service start, before the flip): releases `{}` (state 1, agent F6 service row) and `{PA}` (states 2-5) when the
  controller-signed begin deadline (`host-helper-deadlines/`, attach-broker only) is strictly past, policy generation/revision/epoch
  match, and the spawn is proven dead (no PA; PA with an absent `broker.claim`; PA with the matching broker's terminal or unlaunched receipt).
  It writes R through the single journal writer and the existing cancel releases the charge. Proof only; a possibly live group stays held.
- Controller-signed `helper-abandon` (operation kind `helper-abandon`, route `host-helper-abandon`): releases any live attach-broker helper row
  incl. states 6 and 7 (journal-only evidence arm, store and mirrors never read) and 8 when the cause is the X evidence.
- Still held: rows begun before this change (no deadline record) until an operator abandon; `{PA}` whose group may still live; `{PA,N}`; a
  permanent capacity settle failure (state 8 root cause); the agent's in-memory `release-blocked`/`wedged` attachment (capacity is freed,
  the attachment object is not un-wedged). All specs NOT_RUN (no runnable binary).

## Update 2026-11-19 (milestone_0043, Opus re-review B fixes; source-authored, NOT_RUN)
- P1 fixed: "never consumed" is now a journal fact, not the absence of a store file. The agent publishes a reap marker
  (`host-helper-reap-markers/<sha(op)>.sdn`) through the capacity journal BEFORE begin, and the open core publishes a consume
  intent (`host-helper-consume-intents/<sha(op)>.sdn`, sha256 of the exact PA bytes) BEFORE the PA publish; an intent
  error writes the pre-consume R (PA was not published). The reap reaps `{}` only with no intent and `{PA}` only with an
  intent whose digest matches the PA bytes it puts into R. A store whose PA was deleted in place, restored from an older
  backup or removed and re-created keeps the intent, so the row is held (no R, no release, no quarantine). A first store
  identity design (inode+device+nonce) was dropped in review: it did not cover in-place restores and `st_dev` is not stable
  across reboots. Rows without the reap marker (begun before this change) are never reaped (operator abandon only).
  Residual: a crash between the intent and the PA publish holds that row for the operator abandon.
- A recorded abandon is re-verified at restart (issuer, signatures, expiry, generation, revocation epoch, session, host)
  before its settle. If that fails, or the marker is unreadable, the row stays charged and the reason is the startup
  quarantine text (`helper-abandon-recorded-unverified:<reason>` / `helper-abandon-marker-unreadable:<reason>`). Every
  charged unresolved helper row quarantines through the reconcile drain anyway; a "held but serving" outcome would be a
  reconcile design change (owner decision). Recovery: a fresh signed abandon (settles in-incarnation, still accepted while
  quarantined) and a restart. There is no signed withdraw of a recorded abandon.
- A freshly signed abandon for the same helper binding finishes on the recorded marker in-incarnation. Residual: the
  durable marker still names the original proof, so a later restart re-verifies that one (and holds again if it expired).
- Abandon refusals echo expected beside given for the request/receipt digests and the observed marker text (`|` separates
  the observed pair), after the signed command verified; no secrets.
- Reap errors never quarantine startup (DESIGN Revision 3); the reap gates on `helper_kind == "attach-broker"` explicitly;
  the unreachable `helper-deadline-expiry-mismatch` branch in begin was deleted.
- Still open: a controller-side command that authors, signs and sends `helper-abandon` (owner decision: no controller
  transport carries host-service domain actions, and `controller_authority_issue_v1` signs only the remote-build task
  class, so it needs new signing authority; same gap as `service-handoff-abandon`).
