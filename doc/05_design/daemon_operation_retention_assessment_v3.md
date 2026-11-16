# DAE-05 B1 owner-held retention diagnostics

Status: SOURCE_REVIEW_PENDING / NOT_RUN, 2026-11-15. B1 is consumed diagnostics,
not response expiry, release eligibility, a dedupe fence or physical GC.
The accepted R4 source remains the baseline; this delta is functional batch 5
of the existing six-batch budget. Root approved this narrow ownership port,
Host status consumer, compatibility change and unique specs/manuals.

## Exact interface and consumed path

`distributed_operation_journal_assessment_v3(owner, request)` accepts only up to
four sorted, unique, valid operation IDs. The public request cannot choose paths,
byte maxima, native capabilities, tickets or health IDs. It returns the fixed
authority/revision/sequence, selected cached rows, missing IDs and validated
reservation payload records. These data are not authorization tokens.

The internal plan derives only `reservation-payloads/<payload_digest>.sdn` for
actual selected `host_reservation_v1` or `host_helper_reservation_v1` envelopes.
It reuses the existing intent decoder and exact action/operation matcher.
The canonical producer hashes the encoded intent at
`host_reservation_codec_v1.spl:216-224`; the payload is published before admission
at `host_capacity_owner_v1.spl:210-220`. No hash of an invented wrapper is used.
Other operation/evidence families are unassessed. In particular no terminal or
Released flag makes a helper/primary/Windows settlement receipt mandatory.

Preflight validates IDs and the generated relative paths/count/size arithmetic
before storage reads. At most four payload reads, each 65536 bytes, are possible:
the actual aggregate read bound is 262144 bytes. Invalid filename-like IDs such
as `parent.lease` reject; a valid missing operation selects no file. There is no
caller-selected file-path or callback port.

Owned journal/store authority is mandatory. One existing private operation ticket
covers live owner/lease checks, exact CURRENT, the fixed reads and producer
qualification, and final owner/CURRENT equality. The metadata gate is not held
over I/O. Every Result path releases the ticket. Invalid caller requests do not
poison. Missing, unreadable, changed or invalid authoritative payloads poison
under that ticket with the exact payload digest before returning their failure.
No raw ownership loan escapes to Host.

The actual consumer is `host_local_command_v1.host_local_status_v1`, reached by
the existing CLI and Host service `host-status` request. Its Host assessment
selects the lexicographically smallest four actual ledger operation IDs using
UTF-8 byte comparisons, then consumes the journal port. Output contains only a
versioned aggregate reservation-sample diagnostic: examined/total/omitted counts,
sample pinned/active/uncertain counts, validated payload count and fixed reasons.
It emits no operation ID, envelope, payload, proof byte or native health identity.

`Incomplete` remains explicit even when every examined reservation is pinned:
publication/reference release, all retained recovery evidence, trustworthy
terminal age and omitted subjects are not qualified. Missing ledger references,
uncertain continuity and ledger/journal revision mismatch remain visible reasons.
Compatibility-only unowned owners get zero examined subjects and the explicit
`owned-assessment-required` reason, not a fabricated operation ticket.

## Bounds and old consumers

Sampling uses one pass over cached ledger metadata with a four-element ordered
selection, followed by at most four cached-ledger matches. It does not walk the
filesystem or replay all WAL/snapshot history. This bounded explicit status
diagnostic adds work to the existing ledger-based status computation; runtime
latency/RSS qualification is NOT_RUN and no numeric performance PASS is claimed.

The actual controller status decoder was strict: it rejected every additional
field and limited nesting to depth 2. It now permits only the optional
`retentionAssessment` field while retaining all old required fields and authority,
continuity and capacity checks. The optional diagnostic is ignored for admission.
Parser bounds become 8192 source bytes, depth 4 and 128 nodes. Diagnostic keys,
reasons and counts are bounded, with no caller-supplied messages or payloads.
Old status responses remain accepted; unrelated fields still reject.

## Feasible POSIX deletion/flush producer, not implemented by B1

The next storage producer can use the existing retained-I/O owner and libc
`openat`, `statx` and `fsync`, plus a scoped libc `unlinkat` declaration if admitted.
No new `rt_*` export is needed for a Linux implementation. The current retained
directory API exposes open_file/close, not exact child deletion/directory sync;
these capabilities cannot be claimed merely from generic path unlink/fsync.

Construct a journal-private producer only under the actual writer and operation
ticket. Retain trusted WAL/objects directory descriptors, validate privacy and
identity, accept only a fixed lower-hex object digest, and re-read/hash/qualify the
exact regular nofollow leaf before deletion. Never accept a raw directory path,
descriptor, caller pin set or filename glob as deletion authority. Keep native
descriptors inside that producer; copied values must not independently close or
reuse them. Close consumes descriptor slots before the syscall and preserves
unknown cleanup without retrying a consumed fd. Qualify that lifecycle per host.

`unlinkat(dirfd, name)` is name-based, not an atomic compare-inode-and-delete
syscall. Safety therefore needs the existing exclusive writer, one operation
ticket, trusted retained ancestry and no competing root mutations, with exact
leaf identity checks. Operator/attacker replacement of the protected root is not
solved by a pathname check; continuity/rollback uncertainty requires reconciliation.
If those mutation/lifetime assumptions cannot be established, the producer must
refuse. Do not describe a two-call check/unlink race as kernel atomicity.

The effect API needs explicit Deleted/AlreadyAbsent/RetainedCleanup/Unknown
outcomes and separate observed deletion versus durability progress. No error may
erase an uncertain native owner or report the old pre-effect state. Keep the
parent writer until all actual storage cleanup obligations are resolved.

Reclamation still needs an owner-derived complete reachability/reference fold,
an exact bounded deletion plan committed through replacement CURRENT, and recovery
of that selected plan before effects. If CURRENT/pins change between batches,
revalidate rather than deleting from a stale plan. Retain all receipts needed by
Host replay until a qualified compact recovery representation exists. Endpoint
digest membership is not automatically a requirement to retain old revision
bytes; audit actual consumers before declaring those objects unreachable.

Existing retained-file sync and file/directory fsync facades can supply parts of
the barrier chain. Power-loss mode still needs actual object, publication-directory,
manifest/control and CURRENT file/directory barriers before old-object deletion,
plus durable deletion intent/progress and actual filesystem fault qualification.
Missing/failed required barriers refuse operation; there is no silent downgrade.
Windows retained stores expose neither the necessary exact committed-object
delete nor a qualified directory-publication barrier. Those remain genuine
provider-capability dependencies, separate from the existing nine-export approval.

## Remaining full requirement

V2 has no authenticated creation namespace, so tombstones must last for this
authority/root lifetime; full capacity blocks new IDs. WAL event timestamps are
zero, so age cannot be inferred from a terminal row, mtime, session generation
or grant deadline. A future protected versioned policy must commit qualified age,
complete pin release, expiry/tombstone decisions and recovery before effects.
The shared ACK callback is not a durable reference-release record. B1 adds no
unused policy/anchor contracts and does not claim these missing mechanisms exist.

All specs, native/concurrent/fault/durability checks, generated-manual maintenance,
coverage and performance remain NOT_RUN. Full DAE-05 B/C completion remains false.
