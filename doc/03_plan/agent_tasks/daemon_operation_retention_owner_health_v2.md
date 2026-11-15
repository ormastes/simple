# DAE-05 Slice A owner health — R4 source handoff

Status: **SOURCE_REVIEW_PENDING / NOT_RUN**, 2026-11-15. No production, runtime,
verification or release PASS is asserted. Root owns review, integration and
landing; this worker performed no Git mutations or native/runtime executions.

Worktree: `/home/yoon/dev/simple-collected-stream-null-20261114`, branch
`work/daemon-retention-design-20261115`. R1 freeze is
`/tmp/daemon-slice-a-completion-20261115-1d2n6p6z`, manifest SHA-256
`dd0bc63abc2aca9adc4cf62491f7c74412907e20cb2af31ddee17f4551e29430`.
The R3 design, original plans and six-file storage foundation provenance remain
unchanged. No Windows native export or baseline admission was added.

R2 review freeze: `/tmp/daemon-slice-a-owner-health-r2-20261115-ejomkr2m`, manifest
SHA-256 `526762fa8179903ab360f80ec99f75cacfa80c5349b9344b88b51649fe44922c`.
Independent Astra found root/cleanup identity, structural read-failure poisoning,
required-CURRENT disappearance and post-effect cleanup-progress defects. R3
addresses them together; none has executed acceptance evidence.

R3 review freeze: `/tmp/daemon-slice-a-owner-health-r3-20261115-7thy2b_k`, manifest
SHA-256 `53d4b34016e94675121826c49c18197a208c55d7216dc2a977d5e0fb411d2817`.
Astra accepted those focused fixes at source level and found the remaining
authoritative parent-lease read path. R4 wraps both POSIX and Windows lease
reads and POSIX cleanup lease validation in the same structural failure boundary.
An unreadable or mismatched lease poisons before error return, including a
nondestructive failed close; restoring bytes cannot revive a copied executor.

## Existing synchronization boundary

Source inspection confirmed the existing NoGC sync mutex owner declares lock
as optional, returns absence for invalid handles, and exposes a checked unlock
status. The existing native implementation uses acquire/release exclusion and
returns 1 only for valid unlock, 0 for an invalid handle. R2 uses one intentional
process-lifetime `mutex_new_gate(0)`; it neither allocates a mutex per journal
nor invents a destructor. This is a source-contract observation, not executed
cross-backend, platform or ABI qualification.

## Native-generation health and operation ownership

The private `distributed_operation_owner_health_v2.spl` registry is limited to
1024 entries, including opening, quarantined and cleanup-pending registrations.
Bindings are fixed-size configuration digests, including the length-framed POSIX
I/O root, authority, expected lease and exact event/profile configuration.
Windows root remains diagnostic because the native store owns all I/O.
Logical IDs and operation tickets
increase without reuse; exhaustion refuses work. A slot retains the exact
`FileLockOwnerV2.token` or `WindowsJournalStoreV1.same_owner` identity, binds once,
and records only the first bounded integrity reason/digest.

Every registry read/write runs under the same process-lifetime gate. The gate
contains no filesystem/provider I/O, native lifetime observation or callbacks.
Dictionary access by logical ID is bounded metadata work; only registration
scans the at-most-1024 identity records. A busy ticket remains held across the
complete journal operation after the gate is released for I/O, preventing a
copied owner from passing a health check and mutating after another alias poisons
the generation. Missing, foreign, busy and quarantined registrations refuse.

Journal wrappers cover commit, lookup, history, checkpoint, execution recovery,
read/read-required, retained-record publication, primary consumption and typed
cleanup. Internal held helpers reuse the current ticket; primary consumption
holds it continuously across executing lookup and native publication. Every
normal Result error releases its operation ticket. Gate failure returns an
error while preserving ownership/cleanup; no replacement healthy gate or slot
is fabricated. Higher-level SDK calls still compose journal operations under
their existing domain single-owner contract; this patch does not claim to serialize
arbitrary application callbacks outside those journal boundaries.

Stored replay/object/semantic projection failures record poison before returning
their error. Classification is structural, never an error-text prefix whitelist:
every inability to validate an authoritative committed record or owner lease is sticky, including
oversized, undecodable or nonregular reads. A page-read failure preserves that exact page digest despite outer
manifest/history error propagation. Normal stale revision, not-found, caller
validation, encoding capacity and unreachable publication-winner failures do
not poison a healthy canonical journal. Invalid CURRENT framing may have no
immutable identity; absence stays explicit. Diagnostics from the existing
unstructured CURRENT reader otherwise identify the authoritative graph anchor,
not an invented leaf-object identity.
An already-admitted nonempty owner whose required CURRENT disappears is
quarantined before returning CURRENT_MISSING; restoring its bytes does not reset
health. Ordinary nonempty head advancement still yields stale without poison.
Generic record read/publication paths also validate the required current graph.

## Opening and exact cleanup

POSIX opening reserves before directory/lock acquisition, then binds the actual
native generation before Ready. New owned opens, including no-profile legacy
data, carry health IDs; commit/checkpoint and all adapters preserve them.
The old unowned path-lock API remains compatibility-only, cannot opt
into a retention profile or checkpoint, and is outside this concurrent-owner
guarantee. Owned/profiled owners cannot use a nil-health bypass.

Windows opening receives an already-retained store. Duplicate native identity
is refused before validation, lease writes or cleanup and does not close that
borrowed alias. Post-acquisition reservation/registration failures retain the
actual store in typed cleanup. An unregistered external Windows cleanup may
attach only through native-identity uniqueness; it cannot reset an existing live
registration. POSIX cleanup with a missing health ID fails closed, since its
native acquisition must already have been preceded by a registered reservation.
Unadmitted external capabilities remain cleanup obligations, never Ready owners.

Cleanup carries the event/profile fields needed to recompute its complete
canonical binding before any I/O. Its remembered `health_binding` value is never
trusted to authorize altered root, authority or lease fields. Pre-publication
cleanup carries the known expected lease digest even when no lease was written.

Typed cleanup obtains the same owner ticket even for quarantined generations.
Confirmed Released/ConsumedError (or Windows released) retires only that logical
slot. Retained/Unknown keeps it. A retired POSIX copied cleanup observes its old
native token as stale and cannot read/delete a fresh lease or retire its new
registration. Stale/ambiguous observations do not erase a registered slot.
Post-effect gate failure returns the actual updated cleanup/progress and native
closed/state observations, never the pre-effect carrier. `health_pending_id`
separately records unresolved metadata retirement; it cannot resurrect a consumed
native owner or roll back `lease_published=false`. No native fault campaign has
executed this branch. Gate failure refuses further operations.

## Authored assertions and qualification limits

The six codec scenarios remain unchanged and NOT_RUN. Twenty-two actual-owned
integration scenarios are authored: the original checkpoint suite plus sticky
corrupt-read/repair/copied-commit refusal and exact first page diagnostic,
ordinary error non-poisoning, complete busy-entrypoint refusal, missing/foreign
IDs, stale copied cleanup versus a new native generation, and bounded production
opening reservations. R3 adds real two-owner root/cleanup substitution, an
oversized committed-page failure followed by restoration, and required-CURRENT
disappearance followed by restoration.
R4 adds actual oversized lease lookup and cleanup failures, exact restoration,
copied completion refusal, preserved cleanup and successful exact close/reopen.
All helpers use actual production paths; no fake owner,
fixture-local poison flag or placeholder success is an oracle. Source counts
are not registered or executed test counts. Manuals are authored, not generated.

Real Windows duplicate-store fixtures, concurrent thread/fault schedules,
native retained/unknown close injection, gate failure, counter exhaustion,
process-kill/disk-full/power-loss cases, Host receipt continuity, core/MCP checks,
SPipe/manual maintenance, coverage and performance remain **NOT_COVERED / NOT_RUN**.
`bin/release` remains unavailable. Exhausted build/native campaigns were not
restarted; no Rust seed or alternate provider supplied acceptance evidence.

Functional source batches so far: R1 exact control-byte accounting, R2 health/ticket
implementation, R3 review fixes, then the R4 lease-boundary correction. No runtime verify/fix cycle occurred. The
aggregate six-cycle guard is unchanged; a resumed task does not reset it.

Independent Astra source/architecture review is required before accepting R4.
Full DAE-05 remains open: owner-derived pins, durable expiry and tombstones,
rollback/provider reconciliation, exact physical GC and platform qualification.
Checkpointing still preserves complete history/endpoints, leaves old objects,
does not extend the lifetime event cap and does not imply power-loss durability.
