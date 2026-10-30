# BuildRunner snapshot reader retention

Base: `60f3e00e8c9d26db18fb120d16ba02d372311802`.
Approved implementation contract: parent and Astra, 2026-10-30. Execution evidence
is deferred until an admitted runtime is available; this document is design.

## Decision and rejected weaker proposal

Publish a bounded capture reservation in the existing retention authority before
any fresh acquisition or retained-snapshot read. The reservation participates in
the same canonical state root, generation and OS-owned lock as pins and leases.
Managed physical deletion refuses while any reservation remains. Acquisition
does not hold the lock: the compiler's existing retention call can take it.

Pinning only snapshots present at capture start is insufficient. Another session
can publish, register and retire a snapshot after that list is frozen; the first
acquisition can then select it for reuse while GC removes it. A global reservation
covers this interleaving and an initially empty store. A second lock or marker
file would introduce a separate authority and is not used.

## State and API

`BuildRetentionStateV1` gains `capture_owners: [text] = []`. Empty reservations
retain the exact V1 serialization and root. Nonempty reservations serialize as
version 2 with a mandatory `capture_owners` array. The decoder accepts V1 and V2;
old readers reject V2. Owner tokens are bounded and unique, and reservations
count against the existing metadata/work budgets. No expiry releases a reader.

The existing store owns these transactions under its stable lock:

- `build_retention_store_capture_begin_v2`: initialize/preserve authority and
  publish one owner reservation before any physical snapshot inventory read.
- `build_retention_store_snapshot_admit_v2`: under that reservation, validate the
  exact snapshot and its physical byte accounting; preserve independent roots;
  register it with a durable `snapshot_dependents/<session>` pin, an
  `active_builds/<session>` pin and explicit reader lease; remove only the
  caller's reservation in the same next-generation write.
- `build_retention_store_reader_release_v2`: remove only the caller's active pin
  and lease after the production manager proves all worker trees settled.
- `build_retention_store_session_retire_v2`: remove only the matching durable
  session pin after the manager records retirement and independently verifies
  no running, unknown, cancelled or unreaped work remains.

Migration inventories the bounded snapshot store while reserved. Proven legacy
units are accounted without inferring disposability; unknown/invalid physical
units remain protected and cause explicit incomplete accounting. Snapshot bytes
are distinguished from separately retained shared chunks and source history.
No blanket rebuildable classification or claim about whole-store bounds follows
from tracking a subset.

## Production order

The existing manager lock owns a state directory. Derive the reservation/session
identity from its exact canonical state/checkout/plan subject. Check a retirement
marker before acquiring any snapshot. Begin the reservation, then run ordinary
source capture or reopen; the global barrier protects compiler reuse reads too.
Admit exact source protection before inventory/adapter/staging readers continue.
Source-only legacy contexts receive the same protection. Failed acquisition
retains the reservation for explicit recovery; no timeout clears it.

Normal terminal code 0/1 releases active protection only after worker reap and
database finalization. Infrastructure failure, cancellation or crash retains it.
The durable session pin survives terminal completion because later verification
and recovery still read its source. A production retire command holds the manager
lock, verifies settled/reaped journal evidence, writes a durable retirement marker
before unpinning, and rejects future reopen/verify. Independent branch, draft,
offline, user and other-session roots remain unchanged.

The compiler's invalid planned-destination cleanup must take the existing store
lock and refuse deletion in managed mode. Validation failure never authorizes
deletion of a possibly sole durable source copy.
