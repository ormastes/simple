<!-- codex-architecture -->
# Executable Aspect Mapping Receipt and Final-Unpin Owner Bridge

## Status

Proposed — contract-first. No executable-aspect unmap is implemented by this
change.

## Decision

`ModuleLoader`'s loader-side aspect owner is the sole canonical mutable owner
of executable-aspect mapping lifecycle. `SegmentMapper` and
`SharedExecMapper` are each the canonical owner of their physical mapping
record and issue its producer receipt; neither becomes a cross-layer lifecycle
authority. Their private address/length records never cross into the aspect
package or a public receipt.

The common, sibling-safe boundary is a new frozen contract module:
`src/lib/common/structural/parallel_commit/executable_mapping_receipt.spl`.
It owns the versioned, pointer-free `ExecutableMappingReceiptV1` vocabulary;
the compiler loader owns its live registry and mapper-specific private data.
This follows the existing `common/structural/parallel_commit` ownership rule:
common owns receipt words, while a runtime/loader owner commits state.

## Boundary contract (proposed)

`ExecutableMappingReceiptV1` is a copyable mapper-issued *coordinate*, never
direct authority. Its fixed fields are:

| Field | Meaning |
| --- | --- |
| `schema` | Must equal `1`. |
| `owner_id` | Exact mapper-local owner identity supplied at materialization. |
| `mapping_key` | Opaque mapper-local segment key or symbol key. |
| `producer_kind` | Closed: `SegmentMapper` or `SharedExecMapper`. |
| `mapping_generation` | Producer generation observed at materialization. |
| `mapped_bytes`, `segment_count` | Nonnegative accounting facts. |

`ExecutableMappingReleaseResultV1` is likewise pointer-free and names
`Released`, `AlreadyReleased`, `NotFound`, `OwnerMismatch`, `GenerationMismatch`,
`FinalUnpinRequired`, or `NativeReleaseFailed`. A receipt alone cannot call
unmap: no mapper exposes receipt-driven unmap, and the future loader owner
must bind the producer coordinate to exact aspect identity/final-unpin state
inside one bounded live registry before it implements the release port.

The proposed common module imports no compiler or mapper code. It is a
contract leaf, not a virtual capsule and not a new `aspect_pack` dependency.

## Ownership and commit flow

```text
mapper-private address/size --fresh candidate--> ModuleAspectExecutableMappingOwnerV1
                                             validate exact owner/facet/generation
aspect lifecycle gate + owner registry ----deterministic commit----> live receipt row
ModuleFacetRef.release --final-unpin lease--> same owner --> mapper-private unmap
                                                    | success
                                            aspect-pack final-unpin commit
```

`ModuleAspectExecutableMappingOwnerV1` is held by `_ModuleAspectOwnerV1`; it
owns all mutable receipt rows, byte totals, capacity counters, and terminal
history,
and terminal-result ring. Its registry rows contain the mapper-private release
delegate and, only inside the loader layer, the native mapping coordinates.
No raw pointer or `i64` address is placed in a receipt, `ModuleFacetRefV1`,
`std.common.aspect_pack`, or any cross-layer callback.

Mapping is a parent-owner commit, even if a future worker materializes bytes:

1. A producer creates a fresh, uncommitted result. It is a scoped private loan
   and cannot be resolved by a facet.
2. Under the aspect lifecycle gate, the loader validates loader identity, exact
   facet generation, digest, limits, and a producer-specific completion proof.
3. The mapper issues the non-wrapping producer coordinate.  The loader commits
   that coordinate's registry row and aspect binding association together. If
   either part cannot commit, it invokes the
   same producer-private rollback before returning failure.
4. Only the parent owner publishes the aspect association for an
   `ExecutableMappingReceiptV1`. Ordering is
   `(owner_identity, facet_key bytes, facet_generation, mapping_generation)`;
   conflicting
   candidates reject rather than silently replace an active mapping.

This makes cancellation deterministic: cancellation before step 3 rolls back
the fresh candidate; cancellation after step 3 transitions the row to
`ReleasePending` and follows final-unpin protocol. It never frees a mapping
whose receipt is still live, and it never publishes a successful receipt for a
rolled-back mapping.

## Final-unpin bridge

The existing `apk_facet_unpin_v1(...) -> bool` cannot distinguish an ordinary
unpin, final non-quiescing unpin, or final quiescing release, and its lower
layer may not depend upward on a mapper. Therefore no callback can safely be
added around the current function.

Prerequisite `aspect_pack` contract v2:

1. `apk_facet_prepare_unpin_v2` atomically consumes one pin under the existing
   loader gate. For a final quiescing pin it produces a generation-bound
   `ApkFinalUnpinLeaseV2` and leaves the binding `FINAL_UNPIN_PENDING`; it does
   not free payload bytes.
2. The loader owner uses that lease to select its exact registry row(s) and
   invokes the producer-private release delegate exactly once per receipt.
3. On all releases succeeding, `apk_facet_commit_final_unpin_v2` frees aspect
   bytes. On native failure it records `ReleasePending`; the binding remains
   non-acquirable and retryable through the same owner, never reloaded over.
4. Only the loader owner may abort a pre-commit lease before it has invoked a
   mapper release. Once release starts, cancellation is a recorded terminal or
   pending state, never a second free.

The callback direction is consequently **ModuleLoader owner -> mapper private
release delegate**, after a lower-layer final-unpin lease is prepared. It is
not `aspect_pack -> compiler.loader`, preserving the MDSOC/common-to-consumer
dependency direction.

## Capacity, lifetime, and failure policy

Admission has explicit fixed limits: `max_live_receipts`,
`max_live_mapped_bytes`, and `max_terminal_results`; limits are configured at
owner construction, are positive, and reject before physical mapping when
known. Registry removal decrements bytes exactly once. The terminal-result ring
is bounded and contains only receipt IDs/status, not pointers, code, or facet
payload. Issuance exhaustion fails closed rather than wrapping.

Unload of an unpinned executable aspect uses the same prepare/release/commit
sequence as a final `ModuleFacetRefV1.release`; there is no direct
`native_free_exec_memory` escape hatch. Replacing a facet is rejected while a
receipt is live or `ReleasePending`. `SegmentMapper.unmap_owner` and
`SharedExecMapper.unmap_owner` remain bulk internal teardown APIs, not proof
that a particular facet mapping was released.

## Implemented mapper prerequisite (2026-08-26)

`std.common.structural.parallel_commit.executable_mapping_receipt` now owns
the pointer-free `ExecutableMappingReceiptV1` vocabulary and the deliberately
unimplemented `ExecutableMappingReleasePortV1` boundary.  Both
`SegmentMapper` and both maintained `SharedExecMapper` surfaces retain their
address-returning APIs for compatibility and add receipt-returning mapping
entrypoints.  The mapper itself issues the coordinate immediately after it
commits a live native record; the coordinate includes only owner-local key,
non-wrapping mapping generation, byte count, segment count, and producer kind.

No mapper exposes `unmap_receipt`: a copied receipt is therefore not authority
to free native memory, and release before a final-unpin lease is unavailable by
construction.  Receipt-producing `SharedExecMapper` calls also reject replace
requests, so the receipt lane cannot retire an earlier receipt-bearing mapping
through hot-reload replacement.  The new receipt path adds no registry or payload copy; it is
O(1) over the record just committed.  Existing record registries remain the
only mapper-held state and their removal semantics, W^X transitions, and code
cache behavior are unchanged.  Generation exhaustion fails closed.

## Remaining blockers

Implementation is intentionally blocked because all of these contracts are
missing on `origin/main` at `63352be37a7`:

- `_ModuleAspectOwnerV1` has catalog ownership only; it has no mapping registry,
  capacity accounting, receipt issuer, or producer delegate interface.
- `ModuleFacetRefV1.release` calls `apk_facet_unpin_v1` directly, whose `bool`
  result is insufficient for a staged final-unpin handoff.
- `std.common.aspect_pack` has no generation-bound final-unpin lease or
  prepare/commit/abort transition, and must not import `compiler.loader`.

Until those prerequisites land, the existing statement in
`module_loader_compat.spl` remains correct: executable unmap is not claimed
after final unpin because no executable mapping receipt crosses that boundary.

## Static performance and memory review

The mapper receipt path performs the existing materialization followed by one
O(1) lookup of the record it just committed; it allocates no second registry,
copies no payload, adds no W^X transition, and issues no release syscall. The
hot non-final release path remains one lifecycle-gate admission plus one
bounded registry lookup; it performs no scan of mapper records, packs, or
payload bytes. Final release is O(receipts for exact facet generation), with a
facet-to-receipt adjacency index owned by the loader; it must not call
`unmap_owner` or rescan all registry rows. Admission/release uses preflight
capacity counters, avoids payload copies, and retains no native address in any
copyable record. Compaction is prohibited in the hot path; a bounded ring
overwrites only completed terminal summaries. Native release remains the only
syscall-bearing step and happens outside no-longer-needed payload processing,
while lifecycle state stays gate-serialized.

## References

- `src/compiler/99.loader/segment_mapper.spl`
- `src/compiler/99.loader/loader/object_mapper.spl`
- `src/compiler/99.loader/module_loader_compat.spl`
- `src/lib/common/aspect_pack.spl`
- `doc/04_architecture/language/parallel_ownership_model.md`
