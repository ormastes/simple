# DAE-05 operation retention and checkpoint design

Status: R3_DESIGN_REVIEW_REQUIRED, 2026-11-15. No implementation or executed
qualification is claimed. Selected requirement: DAE-05 in the existing Caret
distributed execution plan; this document elaborates that selection, not an
alternative scope. Full DAE-05 remains open until retention, reclamation,
failure recovery and platform qualification are complete.

## Source and ownership boundary

Release inspection: `ce5b5d9759ca4d6b2c7e59e69ec6de65342139ca`; assigned design
worktree base: `3e0584c314ec259ac51fe6f4edb2f3ea6d674f5d`.
Reuse `common/task_runner/distributed_operation_journal_v2`, its canonical
history fold, `distributed_operation_state_v2`, and `database/wal_segmented`.
No second domain writer, scheduler, operation state machine or background
compactor. Checkpoint is an explicit command of the existing domain owner.
Independent domain roots remain independent; a Host checkpoint never traverses
a controller, BuildRunner, Caret or Mux root.

The root-owned frozen Windows foundation has changes in both journal and WAL
files. Its `WindowsJournalStoreV1` is an owned retained-root capability, not a
path registry. `publish` supports immutable objects; `read` supports bounded
reads; `compare_replace` accepts only `database-wal/CURRENT`. It has no general
immutable-object deletion method. Extend that foundation after integration;
do not replace it or modify native exports, admission policy, or its frozen
index. Native journal export approval remains a separate dependency.

Current behavior permanently stops mutations at `sequence >= maximum_events`,
where maximum_events is at most 100000. Replay walks to genesis. Existing
history exposes admission sequence, final edge, final enclosing commit and
all revision endpoints. Host no-begin cancellation validates arbitrary retained
receipt `before_commit_digest` endpoints. A terminal operation can still have
live runtime identity, charged capacity or outstanding cleanup.

## Delivery boundary

Slice A adds checkpoint-backed bounded replay while retaining every complete
operation row and every history endpoint. It does not delete operation/result
evidence, expire responses or reclaim disk space. Old WAL objects remain
available. This is replay compaction only, not completion of DAE-05.
It also does not extend the existing lifetime admission cap: a checkpoint can
shorten replay but cannot make a lifetime-full journal accept another event.

Slice B adds owner-derived pins, explicit response expiry and durable dedupe
tombstones. Slice C adds exact unreachable-object reclamation through each
admitted storage provider and the failure/platform qualification matrix. No
placeholder Slice B/C API is added by Slice A. A bounded store must eventually
refuse work when retained identities/evidence cannot be safely reclaimed.
The selected scope also requires rollback/provider-generation reconciliation
before new admission; a syntactically valid old snapshot is not proof of current
runtime ownership. That full-system gate is detailed below and remains open.

## Frozen Slice A interfaces

Public journal API:

```simple
distributed_operation_journal_checkpoint_v2(
    owner: DistributedOperationJournalV2
) -> Result<DistributedOperationJournalV2, text>
```

The returned owner replaces the input owner, including on a zero-effect control
commit. Empty journals return `OPERATION_CHECKPOINT_EMPTY`; a checkpoint head
with no subsequent operation event returns the unchanged owner without I/O
publication. Legacy unowned/path-lock owners return
`OPERATION_CHECKPOINT_OWNED_REQUIRED`. Existing owned lock or admitted Windows
store capability is mandatory. No external effect callback is accepted.

### Explicit retention profile; unchanged lifetime admission policy

Add this exact value type to
`common/contracts/distributed_operation_retention_v2.spl`:

```simple
DistributedOperationRetentionProfileV2(
    version: i64,
    maximum_lifetime_events: i64,
    maximum_tail_events: i64
)
```

Only version 1 is accepted. Lifetime bound is 1..100000, tail bound is
1..maximum_lifetime_events. Existing `maximum_events` and its configuration
surface `maximumJournalEvents` remain the absolute lifetime-event cap, with
their existing defaults and upper bound. They are never renamed or interpreted
as tail limits. Profile.maximum_lifetime_events must equal the explicit existing
maximum_events argument; inconsistent input rejects before root/lease writes.

Add a trailing optional `retention_profile:
Option<DistributedOperationRetentionProfileV2> = nil` to the existing owned
open entrypoints, including the frozen Windows owned-open adapter. Store it in
the returned journal owner with default nil. No new configuration default or
automatic profile is introduced. Legacy open without a profile works exactly
as before for legacy journals, and checkpoint returns
`OPERATION_CHECKPOINT_PROFILE_REQUIRED` before writing objects. A caller opts
in by supplying an explicit supported profile through its protected domain
configuration; a remote request cannot choose it. Slice A does not auto-enable
the profile for any production domain.

Add `checkpoint_sequence: i64 = 0` to the journal owner. Ordinary commit and
all owner adapters preserve both added fields. `sequence` remains the global
monotonic operation-event sequence. Always first reject commit when
`sequence >= maximum_events` with the existing `OPERATION_JOURNAL_FULL`.
When a profile is present, additionally reject when
`sequence - checkpoint_sequence >= profile.maximum_tail_events` with
`OPERATION_JOURNAL_TAIL_FULL`. Checkpoint only resets this separate tail budget;
it never grants events beyond the lifetime cap. Without a profile, legacy
mutation/replay bounds are unchanged. A higher generic WAL sequence ceiling
does not authorize a higher domain admission cap.

The first checkpoint explicitly persists the exact profile in its manifest.
Before that publication, opting in can only add a stricter mutation budget;
it cannot relax the legacy lifetime cap. Existing noncheckpointed history is
read with the legacy lifetime bound even if larger than the chosen tail budget,
so an owner can checkpoint that history; mutations remain blocked at the tail
budget until it does. Empty profiled journals may admit normally within both
bounds, and checkpoint remains unavailable until their first event.

Reopen of a checkpoint requires a caller-supplied profile exactly equal to the
committed version/lifetime/tail fields and the existing maximum_events argument.
Absence yields `OPERATION_CHECKPOINT_PROFILE_REQUIRED`; any mismatch yields
`OPERATION_CHECKPOINT_PROFILE_MISMATCH`. Reject before returning a ready owner;
do not replay with fallback policy. Check the global head sequence against the
unchanged lifetime cap and the suffix count against the persisted tail bound.
Unrecognized profile versions fail closed. Increasing a lifetime cap or changing
a persisted profile requires a separately reviewed, explicit owner-policy
migration; Slice A contains no such API and cannot perform it automatically.
Never reset operation sequence or use a checkpoint as an operation transition.

Internal database API (not a second domain owner):

```simple
database_wal_checkpoint_commit_v1(root: text, identity: text,
    expected_parent: text, checkpoint_digest: text,
    store: Option<WindowsJournalStoreV1> = nil
) -> Result<DatabaseWalRevisionV1, text>
```

It validates the exact current parent, existing checkpoint manifest object and
sequence, publishes a checkpoint control revision, then uses the existing
CURRENT compare/publication path. It never deletes. Add
`checkpoint_digest: text = ""` to `DatabaseWalRevisionV1`; existing positional
constructors retain their meaning. For a checkpoint control revision,
`first_sequence == last_sequence == base_sequence`, `parent == base_commit`,
and `segment_digest == ""`. Such a revision is not a zero-length WAL segment:
`database_wal_segment_read_strict_v1` rejects it with
`WAL_CHECKPOINT_NOT_EVENT_SEGMENT`. CURRENT validates its revision and manifest
object rather than invoking the event-segment reader. Existing data commits
keep their V1 representation and may parent a checkpoint control revision.

History structures may move, unchanged, into
`common/contracts/distributed_operation_history_v2.spl` and be re-exported by
the original journal module to avoid a journal/codec import cycle. No field,
caller import, or history meaning changes.

## Storage format and one publication boundary

`database-wal/CURRENT` remains exactly 64 lowercase SHA-256 hexadecimal bytes
plus LF. It points to one immutable revision under `database-wal/objects/`.
There is no CHECKPOINT mutable file, alternate CURRENT, or root migration.
Content identity is SHA-256 of exact UTF-8 bytes, as in the existing WAL.

New checkpoint control revision is canonical SDN with this exact required-field
schema: `version` (1), `kind` ("SimpleDatabaseWalCheckpoint"),
`database_identity` (digest), `base_commit` (digest), `base_sequence` (integer),
`checkpoint_digest` (digest). All six fields are mandatory; unknown/duplicate
fields, malformed digests, noncanonical integers and trailing content reject.
Base sequence must be 1..10000000 and equal the validated parent endpoint.
The manifest must bind the same database identity, base commit and sequence.
This new revision format is explicitly rejected by old readers; unsupported
format must never be treated as an empty/new journal. No downgrade after its
publication is admitted without a separate export/migration procedure.

The checkpoint manifest is canonical SDN with this exact required-field schema:

| Field | Exact content |
| --- | --- |
| version | Integer 1 |
| kind | "DistributedOperationCheckpointV2" |
| authority_digest | Same database identity |
| base_commit | Exact pre-checkpoint CURRENT digest |
| base_sequence | Exact pre-checkpoint event sequence |
| retention_profile | Strict record: version, maximum_lifetime_events, maximum_tail_events |
| operation_count | Number of complete operation/history pairs |
| endpoint_count | Number of historical revision endpoints |
| pages | Ordered array of page records described below |

Each page record has `kind` ("operations" or "endpoints"), `ordinal` (zero-based
within kind), `digest`, `byte_count`, and `entry_count`. All
operation pages precede endpoint pages. Pages are immutable objects in the
same existing object store; the manifest does not contain paths.

Page SDN fields are `version` (1), `kind` ("DistributedOperationPageV2" or
"DistributedOperationEndpointsV2"), `authority_digest`, `base_commit`,
`base_sequence`, `ordinal`, and `entries`. Operation entries
contain `operation_id`, `envelope_digest`, `envelope`, `state`, `outcome_digest`,
`admitted_sequence`, `last_from_state`, `last_to_state`,
`last_outcome_digest`, `last_sequence`, `last_commit_digest`. Endpoint entries
contain `commit_digest` and `last_sequence`. Use the repository's strict SDN
reader/writer, not a new text parser or JSON serialization. These field lists
define schemas, not wire order. Every dictionary's key order and every string's
quoting/escaping come exclusively from existing `sdn_encode_canonical` (bytewise
sorted dictionary keys, strings quoted when required). Persist exactly its UTF-8
output plus one trailing LF. Strict decode and canonical re-encode plus one LF
must reproduce exact stored bytes. Ordered page arrays and entry sorting below
are semantic requirements and remain explicit.

Operation IDs sort by UTF-8 byte order, endpoint digests lexicographically.
Greedily fill pages to the byte limit without splitting entries; an oversized
entry fails. Reject unsorted/duplicate IDs, duplicate endpoints/pages, missing
ordinals, contradictory bindings, count/size mismatches, unknown fields and
invalid V2 states. Re-decode each envelope and verify its ID/digest; verify
terminal outcome requirements, valid last transition, positive admission and
edge sequences, edge order, and enclosing endpoint membership. Source snapshot
comes only from the canonical checked current-owner fold, never a caller-supplied
history token. Hashes detect corruption; they are not signatures authenticating
an attacker who can rewrite the protected storage root.

Budgets: each object at most 1048576 UTF-8 bytes, at most 256 pages, aggregate
manifest/control/page bytes at most 67108864, at most 100000 operations and
100000 endpoints including the new checkpoint endpoint. Validate arithmetic
before addition. These are proposed fail-closed implementation limits, not
measured performance claims. A valid old journal that exceeds snapshot limits
remains readable but cannot checkpoint; no rows/endpoints are evicted to fit.
All snapshots retain the endpoint growth, so checkpointing cannot promise
indefinite operation even when event-tail replay stays small.

## Publication, recovery and mutation ordering

1. Check live owned writer/lease and exact CURRENT. Build one canonical history
   fold and compare the full operation index. Do not invoke domain effects.
2. Encode bounded pages and manifest from that fold; publish through existing
   immutable-object primitives and read/check all exact winners. Failed or
   interrupted publication leaves only unreachable objects.
3. Publish the control revision; recheck ownership and atomically compare/publish
   CURRENT against the exact input revision. POSIX reuses the stable existing
   commit lock; Windows uses existing retained-store CURRENT CAS. The same
   domain parent writer remains held throughout; no lease/lock inode is replaced.
4. Return the new revision and checkpoint_sequence with unchanged operation
   state. Add the control revision endpoint at base_sequence when constructing
   history; it cannot be included in its own hashed manifest. Stale copied
   owners fail their existing CURRENT check.
5. Reopen follows data revisions backward until genesis or a checkpoint.
   Enforce the lifetime cap and the applicable explicit suffix budget; validate every contiguous sequence and
   authority edge. Read/validate the checkpoint and seed rows/history/endpoints;
   fold the suffix with the existing V2 transition validator. The manifest's
   base_commit endpoint must exist with base_sequence. Do not follow the
   checkpoint's historical parent to genesis after validation.

CURRENT before CAS selects the old complete journal; CURRENT after CAS selects
the complete checkpoint and suffix. A published malformed/missing checkpoint
blocks opening/mutations rather than falling back to genesis, treating IDs as
new, or inventing a repair. On an ambiguous CAS error, reopen under the actual
owner; do not retry effects. No checkpoint success is a power-loss durability
claim: files and containing directories are not fully fsync/FlushFileBuffers
qualified. A caller requiring power-loss durability must reject this capability;
it may use the weaker process-crash policy only with prior policy approval,
never through silent fallback. No such new approval is asserted by this design.
Detected corruption is sticky for that owner until authoritative
reopen/recovery. Hot lookup does not rescan immutable snapshot pages; corruption
of older objects is detected on replay/history/checkpoint validation, not
promised to be synchronously discovered before every hot lookup.
Quarantine means block mutation/admission and preserve the corrupt root and
exact failing digest for investigation, not rename CURRENT, erase evidence,
create an empty replacement root or unlink the stable writer lock. Release the
writer only through the existing typed close/cleanup obligations.

## Full DAE-05 retention contract (Slices B/C, not implemented)

The domain owner derives pins from its authoritative state while holding the
same writer. Remote callers cannot submit pin sets or declare runtime absence.
Retain full rows, histories and referenced evidence for admitted, executing and
outcome-unknown operations; for terminal operations with any live/unreconciled
runtime, capacity charge, cleanup obligation, parent/child/session binding,
retained receipt or unacknowledged publication; and for all unresolved recovery.
Missing or contradictory domain evidence pins conservatively. Cancelled,
failed, age, PID disappearance and client acknowledgement alone are insufficient
to release runtime pins. History endpoints referenced by receipts are pins too.

Response retention and dedupe retention are separate. Only after owner-verified
terminal outcome, completed exact cleanup and removal of every live reference
may the authorized response retention horizon expire. The expiry decision must
be committed with the same snapshot/CURRENT boundary as its tombstone, before
removing response bytes. A tombstone retains authority, operation ID, exact
envelope digest, terminal state/outcome digest, and original event identities.
Same-ID admission returns OPERATION_EXPIRED, never OPERATION_NOT_FOUND; changed
payload returns OPERATION_PAYLOAD_MISMATCH. Direct commit also rejects tombstoned
IDs so bypassing daemon admission cannot recreate them. Reopen recovers these
decisions before accepting mutations. V2 state-machine states stay unchanged;
expiry is a retention/disclosure classification, not another operation state.

Current V2 IDs have no independently authenticated monotonic creation epoch.
`session_generation` is not a global dedupe epoch and must not be repurposed.
Therefore the safe tombstone horizon is the lifetime of this authority/root:
never evict a tombstone merely by age or to make space. At tombstone capacity,
block new admission. A finite tombstone horizon requires a separately designed,
authenticated namespace/epoch fence that rejects every expired namespace before
lookup and prevents reuse; changing a filename, clock or session generation
does not supply it. This remains an explicit dependency, not a fabricated
existing API.

Physical reclamation removes only exact immutable objects proven unreachable
from the committed checkpoint/suffix and all pinned evidence. Publish and
re-read the replacement checkpoint before deletion; retain exact deletion work
for interrupted cleanup. Never scan/prune another domain, delete a stable lock,
follow a symlink, or infer safety from terminal status. No general Windows
object-delete operation exists in the frozen adapter. Until an approved storage
capability supports exact deletion, Windows does not reclaim bytes and reports
that limitation. POSIX reclamation also requires ownership, reachability and
crash specs before activation; it is not silently enabled by Slice A.

Disk-full, quota or retained-identity exhaustion blocks mutations before domain
effects; never evict evidence as an emergency space repair. Orphan immutable
objects from failed publication can consume disk until qualified reclamation.
Storage failure does not justify a new root, lower replay bound or erased ID.

## Rollback and boot/provider-generation uncertainty

Checksums and monotonic event sequences detect malformed content and gaps;
they cannot detect an attacker/operator restoring an internally consistent old
CURRENT together with all matching objects. An expected head kept in the same
rollback domain does not fix that limitation. The domain admission owner must
reconcile its managed native scope when journal rollback, host boot identity,
provider generation or journal/runtime continuity is uncertain. Until that
reconciliation is authoritative, block new admission, retain capacity charges
and quarantine unmatched native resources; never adopt them by PID/name alone
or infer absence from a missing journal row. Existing protected authority and
provider continuity owners supply this evidence; this checkpoint layer must
not mint an assurance from decoding a manifest. Slice A preserves their fields
and evidence but does not implement or claim that full-system admission gate.

## Acceptance and implementation ownership

See the [test plan](../03_plan/sys_test/daemon_operation_retention_v2.md) for
traceability and the [agent plan](../03_plan/agent_tasks/daemon_operation_retention_v2.md)
for scoped files/review. Architecture is the existing single domain owner over
segmented WAL, with immutable snapshots inside that owner. No new UI is required.
Independent Astra design review precedes implementation. All runtime checks,
core/MCP checks, crash/storage matrix, generated-manual checks and performance
measurements remain NOT_RUN under the existing six-cycle bootstrap stop.
