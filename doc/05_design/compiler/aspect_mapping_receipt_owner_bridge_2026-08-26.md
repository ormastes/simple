# Executable Aspect Mapping Receipt Bridge — Detail Design and Authored Specs

## Scope and non-goal

This is the implementation contract for a future executable-aspect lane. It
does not alter current non-executable aspect behavior and does not assert that
an `i64` address is a receipt or that a bulk mapper cleanup proves release.

## Proposed types and ownership

| Type | Owner / boundary | Mutability |
| --- | --- | --- |
| `ExecutableMappingReceiptV1` | physical mapper / common vocabulary | Frozen, pointer-free producer coordinate |
| `ExecutableMappingCandidateV1` | loader-private producer-to-owner result | Scoped loan; no public address |
| `ModuleAspectExecutableMappingOwnerV1` | `_ModuleAspectOwnerV1` | Canonical registry, limits, issuer, terminal ring |
| `ExecutableMappingRegistryRowV1` | loader-private | Exact producer delegate plus private coordinates |
| `ApkFinalUnpinLeaseV2` | `std.common.aspect_pack` | Generation-bound, single transition lease |
| `ExecutableMappingReleaseResultV1` | common receipt contract | Frozen pointer-free outcome |

The future registry key is `(facet_key, facet_generation, mapping_key,
mapping_generation)`; the direct facet index is `facet_key + NUL +
facet_generation`. A receipt validates exact mapper `owner_id`, producer kind,
mapping key, and mapping generation; the loader registry separately binds its
artifact digest and aspect-owner identity.
No `address`, function pointer, `SegmentMapper`, `SharedExecMapper`, closure,
or arbitrary dynamic payload crosses a common/aspect boundary.

## State machine

```text
FreshCandidate -> CommittedLive -> ReleasePending -> Released
       |               |                 |
       +-> RolledBack  +-> cancellation  +-> NativeReleaseFailed (retry only)
```

`CommittedLive` is reachable only after the loader owner atomically associates
the receipt with the exact aspect generation. `Released` consumes the live row
and writes one bounded terminal summary. A repeated receipt sees that summary
or `NotFound`; it can never release a newer mapping.

## Required API sequencing

1. **Done (mapper prerequisite):** each mapper has a receipt-returning map
   entrypoint alongside its compatibility address API.  The receipt is issued
   only after a live native record exists and has no raw address.  The common
   `ExecutableMappingReleasePortV1` is intentionally a contract only; no
   mapper exposes receipt-driven release before final-unpin exists.
2. Add the common receipt data types and well-formedness checks, without native
   imports.
3. Add the bounded owner registry and deterministic parent commit.
4. Add `aspect_pack` v2 final-unpin prepare, commit, and pre-release abort.
5. Change `ModuleFacetRefV1.release` to ask its loader owner to execute the
   protocol while the lifecycle gate is held. It must not call mapper APIs.
6. Route zero-pin unload through the same protocol; retain the legacy v1 path
   for facets with no executable receipt.

## Authored, unexecuted race/ownership specifications

These scenarios are deliberately design evidence only: the requester excluded
test/SPipe execution and the APIs they require do not yet exist.

| ID | Setup/action | Required observation |
| --- | --- | --- |
| AMR-OWN-001 | Two candidates target one `(facet,generation)` under contention. | Gate admits one parent commit; the other is rejected and rolled back; only one receipt ID is live. |
| AMR-OWN-002 | A copied receipt is supplied by another loader identity. | `OwnerMismatch`; no producer release delegate runs. |
| AMR-RACE-003 | Unload marks a pinned facet quiescing while a holder releases its final pin. | New pin fails; final-unpin lease is unique; one release path commits payload release. |
| AMR-RACE-004 | Native unmap fails after final-unpin prepare. | Binding remains non-acquirable `ReleasePending`; bytes are not claimed released; retry uses same receipt ID. |
| AMR-RACE-005 | Cancellation occurs before parent receipt commit. | Candidate rollback runs exactly once; no receipt/facet index/byte counter is published. |
| AMR-RACE-006 | Cancellation occurs after commit but before final unpin. | Receipt remains live; cancellation only records pending unload and cannot unmap early. |
| AMR-BOUND-007 | Receipt and byte capacity are full. | Admission fails before map where size is known; no registry/terminal ring grows. |
| AMR-STALE-008 | Old receipt is replayed after unload then reload. | No release of new generation: generation/ID mismatch or bounded terminal `AlreadyReleased`. |
| AMR-ORDER-009 | Two workers materialize same digest in different completion order. | Parent commits by documented tuple order; loser is rejected/rolled back independent of completion timing. |

## Static review record (cycle 2 of at most 3)

PASS, design-only:

- Canonical mutable state has one named owner.  Each mapper issues a coordinate
  only for its just-committed native record; it creates no second registry.
- All cross-layer records are copies/frozen coordinates or a generation-bound
  lease; raw addresses and raw callback transports are excluded.
- Parent validates then deterministically commits/rolls back child-produced
  candidates. Unknown overlap/conflict rejects.
- Registry, bytes, ID issuance, and terminal history are bounded; no release
  path scans all mappings.
- Existing address APIs, W^X transitions, and code-cache behavior are unchanged.
  Receipt mapping adds one O(1) record lookup and no payload copy/syscall.
- No executable unmap is asserted against current v1 APIs; in particular there
  is no `unmap_receipt` entrypoint before final-unpin v2 exists.

Implementation remains blocked pending the five prerequisite contracts named in
the architecture decision. No tests, builds, benchmarks, optimizer passes, or
verification gates were run for this design-only work.
