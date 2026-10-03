# Checkpoint validation requires a shared aggregate work budget

Status: REPAIR SOURCE WRITTEN — independent source review and runtime execution
remain required; checkpoint installation is not production-qualified.

Date: 2026-10-03. Source checkpoint: `7a90c461297` on
`work/item2-checkpoint-20261003`. This is a source-review finding; no runtime,
throughput, memory, or production-readiness result is claimed.

## Concrete defect

`src/app/scv/db/checkpoint_validation.spl` bounds individual page reads and
history traversal, but does not bound cumulative IO or codec work for a whole
prepare/resume operation. `db_checkpoint_record` rereads and decodes a selected
page for each key, then `db_pages_lookup` validates the supplied page again.
Metadata validation, graph traversal, old-to-new preservation, and pending
classification can repeatedly visit the same page. Staging's
`DbCheckpointPageSource.maximum_bytes` does not limit these later local reads.

For Reference storage, `db_checkpoint_batch` and `db_checkpoint_row` decode the
entire snapshot for every lookup. Repeated lookups over a valid bounded snapshot
can therefore cause quadratic decode work. A small page or snapshot limit does
not establish a bounded aggregate validation cost.

The existing signature, canonical encoding, per-object quotas, ancestry cap,
and held install checks do not repair this defect. Keep the checkpoint effect
owner unfinished until a single operation-wide budget is threaded through all
validation paths, including recovery.

## Scoped repair design

Use explicit threaded reader state and return the updated state from every
reader/helper call. Do not introduce globals or assume mutation survives copies
of a value. Prepare and resume each construct one reader; nested validation,
preservation, and pending classification reuse it without resetting counters.

Initial conservative ceilings are 1 GiB cumulative validation work, a 64 MiB
verified page cache, and at most two Reference images with at most 32 MiB total
retained encoded bytes. These are admission limits, not RSS predictions or
Operating-B qualification. Charge IO and codec work separately against explicit
counters; a cache hit must still charge repeated record decoding. Reserve the
selected page's admitted maximum byte size before each physical read, including
rereads after eviction. Charge Reference input bytes before decoding and record
payload bytes before record decoding. Fail closed before performing work that
would exceed either budget, with a typed checkpoint quota error.

Cache only pages verified against the captured admitted descriptor and manifest
context. Cache hits use binary key lookup in the verified page and do not rehash
the whole page. Cache identity must bind the root/store and descriptor; callers
cannot supply an unverified page or a boolean proof. Eviction bounds retained
encoded page bytes and never refunds cumulative work. Source hydration retains
its own pre-IO quota independently of this validation budget.

Decode each Reference snapshot, identity map, and conflict catalog once. Build
bounded keyed row, accepted-batch, binding, and high-water indexes, then reuse
them in validation, old-to-new preservation, and pending preview. Account for
both old and incoming Reference images; current-state reads and recovery reads
also consume the operation's budget. A standalone validation entry point may
create a reader, but installer internals must use reader-taking functions rather
than wrappers that silently create fresh budgets.

Preserve existing checkpoint signatures, pending patch bytes, semantic planning,
history and disposition checks, active anchor semantics, and the single held
install CAS. No shared local-store protocol change is needed for this repair.
Large or skewed inputs may conservatively return quota; do not relax validation
or claim scalable history completeness to make them pass.

## Required regression sources and review boundary

- Repeated metadata lookups in one page reuse verified bytes while exhausting
  the record-work budget deterministically when the limit is small.
- Cache eviction followed by a reread consumes the same cumulative IO budget;
  a rejected reservation performs no physical read.
- Metadata validation, preservation, and pending preview share one budget and
  cannot each obtain a fresh allowance through a convenience wrapper.
- Reference row and accepted lookups reuse one decoded image; an old/new pair
  exceeding the retained encoded-image bound fails before decoding the excess.
- Prepare and resume both enforce the budget. A quota failure cannot publish
  an active checkpoint generation or acknowledge installation as complete.
- Existing signature, history, queue-preservation, and crash-recovery assertions
  continue to apply; no test replaces them with a caller-supplied safety flag.

The next review should cover only the new reader, changed call chains, and these
regressions. Runtime execution remains a separate unavailable gate. This note
records an unfinished correctness/resource guard, not a measured performance
regression or a completed implementation.

## 2026-10-03 repair source and precise accounting scope

`checkpoint_reader.spl` now returns explicit reader values from every load and
reservation. Prepare, resume, preservation, metadata/history traversal, and
pending planning retain that returned state. No nested helper resets it.
Pages enter the 64 MiB LRU cache only after actual no-follow byte reads and
descriptor/digest verification. Binary cache lookups avoid whole-page hashing;
record payload/key work is charged on hits too. Eviction and Reference release
refund retained storage only, never cumulative IO/work reservations.

Reference semantic images decode once into keyed row, accepted, binding, and
high-water indexes. Independent signed-envelope canonical validation still
decodes nested wires; it is separately charged before decoding. A previous live
Reference generation is decoded from its captured store view, without reopening
a possibly advanced HEAD or using a synthetic authenticated checkpoint key.
The retained encoded-image bound remains 32 MiB, not a heap/RSS estimate.

The 1 GiB reader IO ceiling applies to validation source-page/artifact reads and
variable preflight generations. Normal store reads reserve 64 MiB plus the
65-byte HEAD pointer; compact checkpoint generations reserve 2048+65 bytes.
Artifact reads reserve their actual 33,554,800-byte IO ceiling first, then charge
actual returned wire length before canonical decoding. Trusted policy encoding
has its own pre-encode reservation and each authorization pays its measured
canonical policy wire size plus the bounded original patch work. The work
counter represents encoded-byte/codec reservations, not measured instructions,
CPU time, or memory.

There are deliberately separate effect bounds:

- Immutable staging retains `DbCheckpointPageSource` quotas and the page
  publisher's bounded readbacks. It is not charged to the subsequent validation
  reader. Source quota alone was never a validation quota.
- The paged import owner retains its separate spill quota (64 GiB with bounded
  chunks/file count). The reader reserves both source-page passes and the
  importer's conflict-proof cache before invocation, not spill IO. No 1 GiB
  whole-import or whole-install claim is made.
- Held prepare/install/replay performs a fixed protocol, not a page/row loop:
  at most 32 generation/publisher bounded-read operations, conservatively
  bounded by `32 * (64 MiB + 65)` bytes. This covers at most five explicit held
  prechecks, three install-primitive checks, two backend-exclusion checks,
  current/readback for each publication, and staged/destination object/HEAD
  readbacks. Compact barrier reads are smaller. These protocol reads remain
  outside the validation counter; shared local-store atomicity is unchanged.

Prepare also reserves recovery-only artifact IO and journal decoding before
publishing Prepared. Resume uses actual wire decode sizes rather than charging
two artificial maximum-sized authentication envelopes. Under the same limits
and immutable admitted inputs, recovery does not acquire a larger fixed-cost
validation requirement than prepare. Lowered test limits may intentionally
reject recovery, preserving the source and Prepared marker for a default-limit
retry.

Pending paged preview reserves only distinct requested existing descriptors per
round; absent buckets cost no source IO. Retained proof revalidation work still
counts, and the shared proof loader continues enforcing its cumulative budget.
The new positive source fixture prepares/resumes an actual empty paged genesis
with an unchanged signed pending create. Negative sources cover pre-IO failure
before corrupt bytes, cache hits, eviction, image bounds, a shared pending-work
failure, and resume failure without publishing a new active generation.
