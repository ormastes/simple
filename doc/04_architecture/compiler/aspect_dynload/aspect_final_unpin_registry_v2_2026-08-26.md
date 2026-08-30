<!-- codex-architecture -->
# Aspect final-unpin registry V2

## Status

Prerequisite contract. Authored but not executed: mapping-receipt production and
the mapper-owned release-port integration are separate lanes.

## Ownership and direction

`std.common.aspect_pack` owns only the facet pin/state machine and can reserve
the one remaining pin of a quiescing binding. It emits `ApkFinalUnpinStageV2`,
a pointer-free value containing loader/facet generation, stage id, and copied
mapper receipt identity. It has no mapper pointer, address, closure, or
callback.

`compiler.loader.aspect_final_unpin_registry` is the loader-owned mutable root.
It admits a bounded `AspectMapperBindingReceiptV1` at mapping time and matches
the exact `(loader, facet, facet generation, mapper owner, mapping id, mapping
generation, release port)` before producing `AspectOwnerReleaseRequestV1`.
The named mapper owner consumes that request through its own port; it is never
called from `aspect_pack`.

## Transaction

```text
loader owner: admit immutable mapping receipt
loader owner: quiesce facet; stage exact final pin
registry: verify receipt and emit owner-only release request
mapper owner: release through its own port; report outcome
loader owner: commit cached-byte retirement on success / rollback stage on failure
```

No executable unmap is claimed or invoked in this lane. A forged, stale, or
cross-owner receipt produces no release request; a failed mapper outcome rolls
the lower reservation back to quiescing + one pin. The existing
`apk_facet_unpin_v1` ABI remains available but refuses to bypass a V2 staged
final pin.

## Bounds and static cost

The registry caps live binding receipts and retained terminal tombstones at
1024 each. Lookup/staging/completion are expected O(1) dictionary operations;
completion has no full binding scan and stores only scalar/text receipt facts.
Aspect-pack's monotonic stage id fails closed on exhaustion, and the existing
bounded facet tombstone policy remains unchanged.

## Integration blockers

1. The current `origin/main` has no typed mapping-receipt producer shared by
   `SegmentMapper`/`SharedExecMapper` and this registry.
2. There is no mapper-owned release port that can consume
   `AspectOwnerReleaseRequestV1` and return a verified release outcome.
3. End-to-end tests must run only after both owners are wired under the existing
   lifecycle gate; these source-level ownership/race specs are deliberately not
   execution evidence.
