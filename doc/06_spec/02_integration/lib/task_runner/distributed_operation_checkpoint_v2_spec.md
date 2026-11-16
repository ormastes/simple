# Owned operation checkpoint — authored manual

Status: **SOURCE_REVIEW_PENDING / NOT_RUN / NOT_GENERATED / NOT_QUALIFIED**, 2026-11-15.

Source: [distributed_operation_checkpoint_v2_spec.spl](../../../../../test/02_integration/lib/task_runner/distributed_operation_checkpoint_v2_spec.spl).
These scenarios open actual private filesystem journals through the typed owned
adapter. They contain real owner/WAL/state assertions. No execution, generated
manual review, runtime case count, coverage or performance result is claimed.
The canonical `bin/release` runtime is absent; exhausted build campaigns were
not restarted and no Rust seed was used.

The first flow uses the agreed steps: **Open the actual owned journal**,
**Commit representative V2 operation states**, **Capture canonical history and
pinned evidence**, **Publish the checkpoint through CURRENT**, and **Reopen and
compare retained identities**. Failure coverage uses **Reject corrupt or
exhausted storage before effects**. These are authored step labels, not executed
captures. The pinned-evidence comparison checks operation envelopes/outcomes and
all original revision endpoints; it does not execute Host receipt validation.

| Scenario | Required observation | Evidence |
| --- | --- | --- |
| Complete projection | Admitted, executing, outcome-unknown, completed, failed, cancelled and admitted-to-cancelled rows preserve envelopes, outcomes, admission/edge sequences and all endpoints; only the control endpoint is added | NOT_RUN |
| Separate budgets | Checkpoint resets tail budget only; global sequence continues; lifetime-full journal stays full after reopen | NOT_RUN |
| Exact reopen profile | Missing/changed profile rejects and CURRENT stays unchanged | NOT_RUN |
| Legacy profile absence | Existing admission remains valid, checkpoint requires opt-in, lifetime cap stays unchanged | NOT_RUN |
| Invalid configuration | Unsupported profile rejects before lease/CURRENT publication; empty journal checkpoint rejects | NOT_RUN |
| Corrupt current manifest | Duplicate/new admission, begin and reopen reject while corrupt bytes and CURRENT are preserved | NOT_RUN |
| Bounded suffix | Delete one historical revision only inside the fixture; checkpoint plus event suffix still restores full state/endpoints and can checkpoint again | NOT_RUN |
| First opt-in | Legacy noncheckpointed history exceeding the newly chosen tail remains readable; checkpoint permits a bounded next event | NOT_RUN |
| Publication prefixes | Publish each page, manifest and orphan control without CURRENT, close/reopen each prefix, observe original complete state, then publish CURRENT normally | NOT_RUN |
| Stale compare | An intervening actual event defeats stale checkpoint CAS; newer executing state survives reopen | NOT_RUN |
| Damaged unreachable winner | Existing wrong bytes at a predicted page digest fail publication without changing CURRENT; original journal remains readable | NOT_RUN |
| Sticky quarantine | Detect a corrupt historical page, restore its bytes, attempt terminal commit through an earlier owner copy; commit must reject with the first exact page digest and CURRENT must remain unchanged until actual close/reopen | NOT_RUN |
| Ordinary refusals | Stale revision and missing operation reject without poisoning the canonical owner; a valid terminal transition still commits | NOT_RUN |
| Busy ticket | Hold the actual production ticket; every owner read/history/checkpoint/recover/publish/consume path and typed close refuses without changing CURRENT or writing records; releasing the ticket restores access | NOT_RUN |
| Health identity | Missing and foreign logical IDs fail closed without changing either actual owner | NOT_RUN |
| Old cleanup | Close and reacquire a root, then try the old copied cleanup; the fresh generation and its lease remain usable | NOT_RUN |
| Reservation bound | Exhaust actual production opening reservations, observe the fixed bound, then cancel only reservations without native resources | NOT_RUN |
| Root and cleanup identity | Two real roots share authority/nonce; redirected owner I/O and altered cleanup root/authority/lease reject before touching either actual owner | NOT_RUN |
| Unreadable committed page | Replace a referenced page with more than 1 MiB, fail actual history validation, restore bytes, and refuse copied completion with the first exact page digest | NOT_RUN |
| Required CURRENT | Delete CURRENT for an already admitted nonempty owner, detect disappearance, restore exact bytes, and keep copied completion quarantined | NOT_RUN |
| Unreadable lease | Oversize the actual parent lease, fail a lookup, restore its exact bytes, and refuse copied completion with the retained lease digest until actual close/reopen | NOT_RUN |
| Lease cleanup | A failed authoritative lease read keeps actual cleanup and poisons the generation; restoring bytes permits exact typed cleanup, while copied completion remains refused | NOT_RUN |

The previous source lacked shared quarantine. The current source uses one
process-lifetime mutex, bounded native-generation registrations and operation
tickets. The sticky regression exercises the actual journal and production
health helpers; none of these assertions has been executed or marked passing.
See the [source handoff and ownership contract](../../../../03_plan/agent_tasks/daemon_operation_retention_owner_health_v2.md).

Publication prefixes model reachable store states, not actual process-kill,
disk-full, crash-recovery, multi-process locking or power-loss tests. Fixture
deletion is deliberate sabotage to establish the intended replay boundary; the
production implementation never deletes historical objects. Windows native
publication and nine-export admission, actual Windows duplicate-store fixtures,
Host receipt continuity, native retained/unknown close faults, gate failure,
real concurrent copied-owner scheduling, physical disk growth, generated-manual
checks and performance remain **NOT_COVERED / NOT_RUN**. Post-effect gate-error
cleanup progress is source-reviewed only: native closed/state and actual updated
cleanup must survive, while `health_pending_id` reports separate metadata debt.
Busy ticket assertions
are deterministic production-helper coverage, not a real thread/fault campaign.
Full DAE-05 expiry, tombstones, pin release,
rollback reconciliation and physical reclamation remain outside Slice A and open.
