# Proposal: qualified no-Host-BEGIN exec child cancellation

Status: **PROPOSED / NOT_FROZEN**. Audit and interface proposal only. No source,
state transition, positive cleanup guard or native operation is implemented by
this document. Root must acknowledge ownership of the shared journal seam;
Host must freeze receipt/recovery semantics before implementation.

## Concrete source findings

Audit anchor: immutable release `df369ceddbb3e5fb1118bd41d4c7744d06220f2a`.
Host guard input is immutable `8f5d48aacb10c2ff53a1e4b5568c9ee5dca1c009`.

* `src/lib/common/contracts/distributed_operation_state_v2.spl:17–33` permits
  `cancelled` from admitted, executing and outcome-unknown. It has no transition
  back to admitted after BEGIN. A cancelled label or outcome hash alone cannot
  establish the required origin.
* `src/lib/common/task_runner/distributed_operation_journal_v2.spl:84–118`
  already reads the immutable revision chain, validates authority/sequence and
  strict WAL segments, and applies its canonical operation-event decoder and
  state transition validator. `lookup_v2` at lines151–159 returns only the
  current indexed row. There is no historical-transition batch API.
* `src/lib/nogc_sync_mut/database/wal_segmented.spl:59–107` already provides
  content-addressed revision opening, strict segment reading and CURRENT
  validation. A generic task-runner history API exists for a different owner;
  it is not authority for this distributed-operation journal.
* `host_runtime_exec_cleanup_guard_v3.spl` validates each original child packet
  before attributing its parent and currently retains every child label as a
  barrier. The Host capacity completion batch already supplies a place to
  construct and reuse one fixed-revision child-barrier map.
* `host_cleanup_evidence_v1.spl:23–98` archives the actual public SDK policy,
  signed proof and recorded context for historical authorization. Reuse this
  model; do not fabricate its wait/teardown fields for an admitted child.
* `host_exec_private_publication_v3.spl` supplies the actual private, bounded,
  final-fresh, no-replace publisher and retained-stage metadata. Its whitelist
  needs a separately reviewed cancellation kind; no second publisher is needed.

## Canonical journal seam

Proposed public read-only API in the existing journal module:

`distributed_operation_journal_history_batch_v2(owner) -> Result<DistributedOperationJournalHistoryBatchV2, text>`

Batch fields:

| Field | Type / meaning |
|---|---|
| authority_digest | text; actual journal authority |
| head_commit_digest | text; actual current owner revision |
| head_sequence | i64; actual current owner sequence |
| revision_endpoints | Dict<text, i64>; actual ancestor commit digest to its last sequence |
| operations | Dict<text, DistributedOperationHistoryV2> |

Per-operation history fields:

| Field | Type / meaning |
|---|---|
| envelope_digest | text; immutable full operation envelope digest |
| admitted_sequence | i64; initial canonical admitted event |
| last_from_state | text; actual validated source state of the final event |
| last_to_state | text; actual final target state |
| last_outcome_digest | text; actual final outcome |
| last_sequence | i64; actual final event sequence |
| last_commit_digest | text; actual enclosing immutable commit |

The module must obtain these facts from its existing canonical decode/validate
fold, not from receipt assertions, current row labels or Host-side WAL parsing.
Check the actual writer lease/CURRENT before and after scanning, enforce the
existing maximum-events bound, genesis, complete sequence and authority rules,
and return an error if the owner revision moved. Reject a forged/forked prefix
even if its claimed sequence happens to equal a real sequence.

Preferred narrow implementation: factor a private replay-snapshot reader used
by the existing open/replay and this read-only batch call. It returns data, not
a second owner or lock. One additional O(E) scan for an entire fixed projection
is acceptable for this slice. Do not call a full historical replay for each
parent, child or receipt. An indexed cache within the canonical owner can be
considered later, with its own constructor/commit review, rather than silently
expanding this first seam.

## Proposed immutable receipt

New pure contract `HostRuntimeExecNoBeginCancelReceiptV3`, using existing
operation, scope and signed grant/approval codecs. Fields:

* `parent_operation: OperationEnvelopeV2` — the original ordinary reservation,
  not an action-mutated replacement.
* `child_operation: OperationEnvelopeV2` — the exact original exec child.
* `child_packet_digest: text` — SHA-256 of the full original canonical V3
  archive; the receipt does not embed another multi-MiB packet copy.
* `scope: ContainerHostScopeV2` — exact original child-parent scope.
* `journal_authority_digest: text`.
* `before_commit_digest: text`, `before_sequence: i64` — the actual journal
  head observed while this child was still admitted.
* `signed: DistributedSignedGrantV2`,
  `approval: DistributedSignedApprovalV2` — a separately authorized parent
  cleanup proof, never the old child launch proof.
* `policy_bytes: text`, `policy_digest: text` — actual protected public policy
  loaded by the producer, not caller policy bytes.
* `authorized_unix_ms: i64`, `monotonic_ms: i64`, `policy_revision: i64`,
  `revocation_epoch: i64`, `session_generation: i64`.

Wire version/kind are fixed by the codec. Policy bytes remain bounded to 1 MiB;
canonical receipt is bounded to 4 MiB. No native absence, birth, wait, teardown,
lease or release claim appears in this receipt.

Pure names: `host_runtime_exec_no_begin_cancel_receipt_encode_v3`,
`host_runtime_exec_no_begin_cancel_receipt_decode_v3`,
`host_runtime_exec_no_begin_cancel_receipt_digest_v3`.

## Proposed owner APIs and ordering

Read:

`host_runtime_exec_no_begin_cancel_load_v3(journal, child_operation) -> Result<Receipt, text>`

Private fixed candidate location proposed for the first slice:
`journal.root/host-runtime-exec-no-begin-cancellations/sha256(child.id).sdn`.
Use the existing private publisher with a narrowly added fixed kind.

Produce:

`host_runtime_exec_cancel_admitted_v3(local, parent_operation_id, child_operation_id, signed, approval, context, refresh) -> HostRuntimeExecAdmittedCancelTurnV3`

Turn fields: `local`, `receipt: Option<Receipt>`, `cancelled: bool`,
`recovery_required: bool`, `error: text`. It has no native lease. Receipt
presence alone never means cancellation or budget release.

1. Validate the actual sole current journal owner, current trusted scope and
   continuity. Resolve the exact original child using the existing validated
   packet helper and original parent journal/execution evidence. Require the
   explicit parent ID to equal that packet's parent and require the actual child
   row to be admitted, with exact envelope/packet binding. No native inspection,
   wait, stop, destroy or absence operation is performed.
2. Refuse executing, outcome-unknown or terminal nonqualified children, and any
   retained delegation evidence. Do not turn object/file absence into native
   nonexistence evidence. Preserve existing charged parent and sibling barriers.
3. Load the actual protected SDK policy. Derive the cleanup SDK request from
   the original parent envelope with only action `host_cleanup_v1`, as the
   established cleanup verifier does. Verify both roles/signatures, exact
   subject/host/payload and fresh clock/revision/epoch/session. This grants no
   parent teardown proof and does not inherit an expired child grant.
4. Capture the actual pre-cancel journal endpoint and recorded verified context.
   Encode the immutable receipt. Publish privately before any child outcome.
   Its final-fresh guard captures only immutable policy/proof/context, not a
   Host/Container owner. Retain all stage metadata on every error.
5. After confirmed publication, refresh/reverify current cleanup authority and
   inspect the actual current child again. Require admitted, exact envelope,
   no delegation and live sole-writer revision. Use the existing canonical
   journal/daemon outcome path to commit `cancelled` with outcome equal to the
   exact canonical receipt digest. CAS/revision failure is recovery-required;
   never infer no effect from the error.
6. Return the updated owner. No child-native lease and no parent allocation
   release is returned or inferred. Parent cleanup's existing native proof and
   all sibling barriers remain independently authoritative.

## Historical qualification and batch cost

Proposed read-only validation API:

`host_runtime_exec_no_begin_cancel_validate_v3(journal, capacity, child_operation, history_batch) -> Result<bool, text>`

The actual guard builder owns this batch; it is not decoded from a request or
accepted as a remote permission token. Validate its actual authority/head/sequence
binding before use. Resolve the existing canonical original child archive and
private receipt, exact parent/child envelopes, packet digest and original scope.
Validate the archived SDK policy/proof at the receipt's recorded context, not
today's grant expiry, following the existing historical cleanup proof model.

Require ALL of these canonical history facts:

* Current row is cancelled and its outcome equals the canonical receipt digest.
* History envelope digest matches that exact current/original child.
* Final validated edge is **admitted → cancelled**, with that same outcome.
* `revision_endpoints[before_commit_digest] == before_sequence`.
* `admitted_sequence <= before_sequence < last_sequence`.

This allows unrelated recovery commits between receipt and cancellation while
rejecting a fabricated prefix. Because the canonical state machine never
returns to admitted after BEGIN, the validated edge proves no Host BEGIN.
It is not a native absence/contained-teardown proof.

Build one history batch only if cancelled candidates require qualification,
then validate all candidates and build the parent barrier map once. Total extra
history work is O(E+C), memory O(E+C), bounded by the existing events/operations
limits. No per-parent replay. The current cancellation producer need not replay
history to prove a live admitted row; historical replays belong to the batched
read/guard path. Stale cached batches are errors, not permission to omit a child.

Missing optional cancellation proof leaves a child barrier. Malformed original
child provenance retains the existing fail-closed reopen behavior. A cancelled
label, valid receipt signature alone, generic outcome hash, running=false or
parent absence cannot discharge a child. Only this qualified child barrier is
omitted; parent release still needs its original cleanup evidence.

## Recovery decisions needing explicit freeze

The single fixed receipt is intentionally immutable. A confirmed identical
pending receipt can be reused only with fresh authorization and exact matching
original operation/prefix evidence. A different receipt may never overwrite it.
If its archived proof expired, or a newly supplied proof differs, the first
slice must conservatively retain the barrier unless Host freezes a bounded
separate reauthorization record/attempt scheme. Do not silently fabricate a new
authorization time or replace the old signed receipt.

Sol owns any BEGIN interlock for pending/ambiguous cancellation evidence. The
producer itself returns no lease or release on any publication ambiguity; a
later admitted-retry BEGIN must not bypass an unresolved cancellation intent.
Exact restart/retained-stage inventory behavior needs a joint freeze before
enabling this producer. Do not add an unbounded hot-directory scan, a second
journal, a fake pending success or a native absence assumption to fill this gap.

Process-crash profile only: existing WAL CURRENT publication has no power-loss
durability claim. Private-file fsync does not strengthen the journal's profile.

## Required regressions after freeze

Real owned journal/history, original packet/private receipt and real SDK frame
fixtures must cover: admitted→cancelled positive; executing/unknown→cancelled
with otherwise matching receipt refused; forged/forked/late prefix; wrong child,
parent, policy, packet hash or scope; original/delegation contradiction; stage
and post-publication expiry faults; receipt-before-outcome crash; stale index;
multiple parents/children in one history batch; one cancelled child not clearing
a live sibling; parent release still blocked without qualified native cleanup.
All future cases are NOT_RUN until actually executed by an authorized campaign.

Ownership: this lane proposes new receipt/owner code only after freeze. Sol owns
current guard/capacity/BEGIN consumers. Root must assign/acknowledge the canonical
journal seam before mutation. No native teardown or provider protocol is owned
by this cancellation slice.
