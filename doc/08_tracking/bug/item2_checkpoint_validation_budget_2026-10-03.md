# Checkpoint validation requires a shared aggregate work budget

Status: OPEN — checkpoint installation is not integration-ready.

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
