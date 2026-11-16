# Windows primary connection terminal-attempt acceptance V3

Implementation status: **WIP — SOURCE_REVIEW PENDING**.
Native acceptance status: **ALL CASES NOT_RUN; ACTUAL FIXTURES UNAVAILABLE**.
This manual is not an executable positive spec, native absence witness,
qualification result or release PASS. No test, build or native execution was
performed while authoring it.

## Inspected source and evidence boundary

The private chain is implemented in:

- `src/lib/nogc_sync_mut/io/windows_primary_connection_admission_v2.spl`:
  actual receipt authorization/claim and cleanup-only abandonment.
- `src/lib/nogc_async_mut/container/providers/windows/docker_engine_exchange_v3.spl`:
  positive-claim exchange acquisition and terminal proof factory.
- `src/lib/nogc_sync_mut/orchestration/host_primary_connection_owner_v2.spl`
  and `host_primary_connection_service_v3.spl`: returned task/receipt ownership.
- `src/lib/nogc_async_mut/container/primary_connection_attempt_v3.spl`:
  tagged live terminal proof dispatch.
- `src/lib/nogc_sync_mut/orchestration/host_primary_connection_attempt_settlement_v3.spl`:
  independent retained evidence validation and helper-only settlement.

The common `primary_connection_attempt_v3.spl` codec encodes metadata only.
Its separate pure vectors do not prove successful claim, native closure or
settlement. Opaque `WindowsPrimaryConnectionAbandonmentV3` and
`WindowsPrimaryConnectionAttemptTerminalV3` values must come from their actual
retained factories; decoding an evidence record cannot construct them.

## Required genuine native fixture

Provision an isolated enrolled Windows Docker process deployment with its
current retained root/store, installation/provider/policy pins, same actual
journal writer lease, executing parent, signed budget and exact signed helper
prepare/execution archive. Use a real `primary-connection` helper and canonical
plan pinned to `journal.lease_digest`. Keep the actual task, consumption record,
publication receipt and every returned native owner in one canonical lineage.
Do not fabricate a helper lease, receipt, native slot, absence record or grant.

The harness must observe real publication/claim outcomes, pipe acquisition,
slot/generation, pending IO and closure, and before/after journal/ledger state.
Expiry/race/error fixtures must act through genuine supported native hooks; if
a case cannot be induced faithfully, leave it NOT_RUN. Do not replace native
behavior with a scripted success or hardcoded closure flag.

Expected metadata domain is version 3,
`container-primary-connection-attempt-terminal`, resource domain
`engine-attach-attempt`, provider `windows-docker-process`. It carries the exact
plan request digest and SHA256 of the canonical consumption record.
`not-opened` has null `pipeSlot`/`pipeGeneration`; `pipe-closed` carries the exact
retired slot and positive generation. Both pending flags must be false. These
metadata properties remain necessary but insufficient without the live proof.

## Native cases

### 1. Expiry before consumption publication — NOT_RUN

Begin with a genuinely executing helper and expire its launch grant before
connection publication/acquisition. Retain the returned failed task; it must
not invent a session or pipe. Call the actual retained
`host_primary_connection_attempt_release_v3` cleanup path. It may build cleanup
metadata from the actual archived helper using
`host_primary_connection_cleanup_record_v3`, publish consumption once, and use
`windows_primary_connection_abandon_v3` to positively claim that exact receipt.
Observe the sealed cleanup-only `not-opened` proof, no slot/generation and no
Engine acquisition. Every admission alias must now be unable to claim it for
launch. This is cleanup authority, never a renewed execution grant.

### 2. Authorization failure after publication — NOT_RUN

Cause a real live-authorization refusal between publication and acquisition.
`host_primary_connection_consume_owned_v3` must return the exact record and
actual receipt with no verified authority and `publication_attempted = true`.
The retained task must keep all those values despite its error. Cleanup may
abandon the retained receipt if actual root/writer/archive checks pass. It must
not reconstruct the receipt by loading the already published record.

### 3. Positive claim followed by pre-slot rejection — NOT_RUN

Use the real authorized exchange factory and obtain a positive one-use claim.
Then induce genuine expiry before acquisition or a native connect rejection
that allocates no retained slot. Require an owner-bearing cleanup result and
the exchange's actual terminal factory to produce `not-opened`, not a generic
rejection relabeled as absence. Post-claim expiry reports
`primary-connection-consumed-expired`; a native rejection retains its actual
error. No pipe identity may be fabricated for this branch.

### 4. Acquired prehijack pipe followed by actual closure — NOT_RUN

Acquire a real pipe and induce failure/cancellation before successful hijack
transfer. Retain and drive that exact exchange owner through native cleanup.
Only its actual closed lease may produce `pipe-closed`. Require matching slot
and generation, exact consumption/request correlation and a fresh native poll
with `closed = true`, `read_pending = false`, `write_pending = false`.
Another slot, another generation or an ordinary rejection is not evidence.
Mismatched proof/record correlation must refuse with
`primary-connection-attempt-record-mismatch` or
`primary-connection-abandonment-record-mismatch` before settlement publication.

### 5. Copied claimant wins before abandonment — NOT_RUN

Retain a real copied verified admission/receipt alias and let its actual
exchange claim win first. The cleanup owner must then fail abandonment with
`primary-connection-consumption-not-claimed`. No second claimant, cleanup-only
proof or helper release may be fabricated. Keep the helper charged and retain
the winner's actual native owner until its own terminal evidence is available.
A copied receipt is not another one-use claim.

### 6. Uncertain publication cannot remint a receipt — NOT_RUN

Induce a genuine publication error where the caller cannot establish whether
publication occurred. The task sets `consumption_attempted` before publication
and retains it even when no receipt returns. A repeated cleanup step must not
retry publication or reread a path to mint another receipt. Require
`host-primary-connection-consumption-uncertain`, retained task/record and
unchanged charged allocation. Existing canonical bytes alone do not resolve
this uncertainty or prove that another claimant never acquired a pipe.

### 7. Expired launch grant still permits exact cleanup — NOT_RUN

After genuine archived execution and receipt publication, expire the launch
grant while keeping the enrolled cleanup owner/current root/writer unchanged.
New acquisition must remain refused. Exact historical helper/proof correlation
and a positive cleanup claim may still produce abandonment and settlement;
cleanup does not reauthorize launch or refresh expiry. Do not combine this
case with a changed root/policy and mistake an ownership refusal for expiry
coverage. Preserve every actual owner on any failed cleanup turn.

### 8. Independent helper-only settlement — NOT_RUN

Pass an actual terminal capability and its exact record to
`host_primary_connection_attempt_settle_v3`. Require immutable publication and
readback under `primary-connection-attempt-terminal/<sha256(helper-id)>.sdn`
and `primary-connection-attempt-settlement/<sha256(helper-id)>.sdn`. The normal
connection-settlement domain cannot coexist: expect
`connection-settlement-conflicting-domains` for a genuine conflicting domain.
Independently validate completion evidence before settling the actual helper.

Check the returned current journal/ledger owner, completed helper outcome
digest, exactly one release of its charge, and unchanged parent/sibling
allocations. Parent workload completion is not implied. Retain the returned
owner/proof on post-commit or projection errors; a stale input owner must never
replace it. If no genuine fault fixture reaches such an exceptional branch,
leave that branch untested rather than corrupting an owner to simulate it.

### 9. Same writer and current root are mandatory — NOT_RUN

Use genuine separate root/store or newly opened writer fixtures; never build
tokens by hand. A plan pinned to another writer must refuse cleanup or
settlement with `primary-connection-cleanup-owner-mismatch`,
`host-primary-connection-cleanup-owner-mismatch` or
`connection-attempt-settlement-writer-mismatch` at the applicable boundary.
Another root/store or receipt origin must fail the actual deployment/store
provenance check or `primary-connection-journal-origin-mismatch` before a new
positive claim. Charges and all real returned cleanup obligations remain
retained. A path spelling, matching SDN bytes or receipt from another store
cannot substitute for the current retained native root.

### 10. Pending native cleanup is never absence — NOT_RUN

Exercise genuine pending reads/writes, outstanding inspection and delayed pipe
close. Attempt release must retain the actual task with
`host-primary-connection-attempt-cleanup-pending`; its terminal factory may
return `primary-connection-attempt-terminal-unavailable` or
`primary-connection-attempt-cleanup-pending`. Require no terminal settlement
publication and no resource release until exact native cleanup completes.
`Closed` metadata supplied by a caller, an empty error, or lack of a session
object must not bypass these native checks.

## Evidence and acceptance limits

For eventual execution, record actual lineage, installation/policy/writer pins,
helper/parent IDs, immutable record digests, claim observations, exact native
slot/generation/pending states, returned errors and journal/ledger changes.
Never publish private keys, credential material or raw handles. Every native
case above is currently **NOT_RUN**; the WIP private chain still needs
**SOURCE_REVIEW** and actual native acceptance. No executable positive coverage
or Windows PASS is claimed by this manual or by the separate pure codec cases.


Source review update: the immutable nine-file owner/settlement/consumer snapshot
`5f2f06214ca971d7dc6a215b07f929819c371ed194ef8e5834b29c99317ef0a0`
received independent Astra review with no P0/P1 finding. This does not change any
native procedure's NOT_RUN status or add executable positive coverage.
