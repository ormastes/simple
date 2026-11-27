# SCV snapshot reuse: bounded proposal and remaining proof

Status: analysis only. Snapshot target: at most 2 seconds. This target has not
been demonstrated. Cache remains enabled unless the caller explicitly opts out.

## Current authority and default cache behavior

`native_build_main.spl:1277` acquires source authority before checking the final
artifact receipt at `:1341`. `native_build_warm_receipt.spl:719` allows the
receipt by default when frontend/HIR cache environment values are absent; an
explicit zero, clean request, graph rebuild, unsupported input-manifest route,
or missing authority makes that advisory path ineligible. This is conservative
reuse, rather than a default-off cache.

The v5 warm key includes the exact SCV binding, producer bytes, argv,
environment variant policy, collection profile, package-index identity and
link configuration. Its payload checks source closure bytes, object/capsule
receipts, runtime/link inputs and artifact bytes. It must not be moved before
source authority or have the SCV binding removed without a complete replacement
for positive and negative semantic dependency authority.

In particular, the current positive source-path list alone does not prove that
an added aspect, macro provider, generated input or newly matching module can
never affect this artifact. Reusing across a changed selected source inventory
requires the actual producer's negative dependency scopes as well as positive
dependencies. No such new proof is claimed by this proposal.

## Existing exact snapshot hit

`compile_snapshot.spl:188` reads and validates the canonical source inventory,
selects rows, and physically canonicalizes every selected live source. At
`:620` acquisition renders the planned rows and derives the revision. At `:634`
an existing exact revision is opened and validated without materializing source
bodies. This path already exists.

Moving the physical containment check after the exact-hit return is unsafe.
A tracked source symlink can be retargeted outside the checkout while retaining
identical bytes. `compile_source_inventory_apply_event_v1` returns no change
when all content/facet identities remain equal; the old planned revision can
therefore still exist. Windows parent junction changes may also be invisible
to Git status. Commit identity alone cannot replace fresh physical ownership.

A future commit baseline plus dirty overlay may avoid unchanged path checks
only with authoritative alias/reparse-point or filesystem-journal evidence.
The existing HEAD/status cursor is not that evidence. No path check is removed.

## Rejected canonical-chunk copy candidate

`scv_compile_snapshot_reuse_source_unscoped_v1` currently checks the current
source size, checks and hashes the canonical chunk, copies a different file
from the previous snapshot, then hashes the destination.

Copying the canonical chunk itself and retaining destination size/SHA-256 would
validate the copied bytes with one fewer hash. However, this is not equivalent
to the current admission policy and is rejected as a performance-only change.

`test/01_unit/lib/scv/compile_snapshot_revision_reuse_spec.spl` requires a miss
when the previous published copy is tampered, even if its canonical chunk is
intact. More decisively, `compile_snapshot_revision_reuse_acquire_spec.spl`
contains the negative oracle "fails closed when a tampered copy's fallback finds
a drifted source": corrupt the prior copy, make a same-length unpublished edit
to the working source, and acquisition must fail with `snapshot-index-drift`.
Copying the intact canonical chunk would instead succeed with the frozen bytes.
Hashing the previous copy as well would preserve that rule but remove the
proposed hash saving. Do not silently rewrite this regression to fit a new
implementation; changing this behavior requires an explicit policy decision.

## Smaller candidate still requiring operation timing

A remaining candidate is to create the constant chunk directory once per acquire,
and memoize successful destination parent creation within the private staging
owner. Never cache failures or share this writable state with another process.
An actual write must still fail if its directory disappears. Timing must show
that these repeated directory operations matter before implementing this delta.

## Required finite verification

1. Run the prepared native operation projection on authentic committed Git
   fixtures of 50, 500 and 5000 sources. Report preparation, source read,
   UTF-8/SHA, chunk mkdir/publication/readback, destination mkdir/write/readback,
   drift read, reuse chunk checks/copy/destination checks and total time.
2. Measure the complete unchanged snapshot acquire and final-artifact restore
   with the same producer, source, inputs, normal memory admission and exact
   options before/after. Component fixtures are not whole-owner timing proof.
3. Verify immutable unchanged rows and old snapshots, one edited source,
   same-sized edits, added/deleted source, aspect/macro provider changes and
   newly matching scopes, symlink/junction retargeting and outside ownership.
4. Corrupt a chunk under its original name, a previous snapshot source, a
   destination readback, inventory metadata and a receipt. Each relevant
   consumed input must fail admission or be repaired from independently
   verified bytes. No corrupt same-name record becomes a cache hit.
5. Obtain Fable review of the actual small diff and evidence before landing.

## Resource and evidence limits

The provisional Phase 2 compiler's SHA-256 is
`88f3c81b4a529d344cfc9459f1b3e036b6b34b49c81c1530f8d7e6af8edd8798`.
Diagnostic programs compiled by it measured 102034 alias rows in 895 ms and
seven 42604-row canonical decodes in 6.7 seconds. These programs have a
different producer lineage from the existing compiler's own startup code;
they do not rule out a producer-specific performance defect.

The operation harness failed before execution because an explicit redundant
selector named nonexistent `src/lib/sffi/platform.spl`. The real platform owner
is already inside the selected `src/lib/nogc_sync_mut/sffi` scope. Its corrected
retry omits that selector and retains its cache and failed evidence.

No compiler retry is admitted while free system commit is below its requested
budget plus reserve. Free physical RAM alone is insufficient. No production
change or two-second result is claimed while this evidence remains missing.
