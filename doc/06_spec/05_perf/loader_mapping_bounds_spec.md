# P4 loader mapping bounds

> Executable specification: `test/05_perf/loader_mapping_bounds_spec.spl`

## At a Glance

| Field | Value |
|---|---|
| Category | Compiler / loader performance |
| Status | Fail-fast until P3 production-owner admission |
| Source | `test/05_perf/loader_mapping_bounds_spec.spl` |
| Architecture | `doc/04_architecture/compiler_export_and_mapping_bounds_2026-09-14.md` |
| Design | `doc/05_design/compiler_export_and_mapping_bounds_2026-09-14.md` |
| Generator | `simple spipe-docgen` source contract; this path is the canonical manual |

This manual records the P4 verification contract for bounded SMF/JIT mapping
resources. It does not claim native allocation, RSS, or callable-address
evidence. Until P3 admits the frozen constructors and lease ledger, each
scenario checks the production-owner seam and fails with `MissingEvidence`.

## Scenarios

### P4-A01 — Separate entry and byte capacity

#### should refuse a request over either finite capacity without admitting a partial reservation

1. Prepare finite `retained_entries`, `retained_payload_bytes`,
   `owned_mapping_entries`, and `owned_mapping_bytes` limits.
2. Require `LoaderCacheResidency` to report both retained and owned entry/byte
   dimensions.
3. Once P3 is admitted, execute exact-fit entry and byte cases, then verify a
   second entry is refused before allocation.

#### should admit an exact fit and reject a second entry beyond the two-entry limit

1. Acquire two entries whose payload exactly fits both independent limits.
2. Verify reservation counters are committed atomically.
3. Verify the next admission increments `admission_refusals` and performs no
   mapper allocation.

### P4-A02 — Overflow and allocation ordering

#### should reject oversized and arithmetic-overflow requests before native allocation

1. Submit oversized and arithmetic-overflow requests.
2. Verify subtraction-safe reservation checks reject them.
3. Verify `exec_mapping_map_rx` is not called by a refused request.

#### should preserve the existing semantic error order before a budget refusal

1. Exercise disabled-JIT, depth, cache-hit, cycle, compile, mapping, and
   publication failure cases.
2. Verify each retains its existing `CompilationError`/result envelope.
3. Verify budget refusal occurs only at the allocation boundary.

### P4-A03 — Active and legacy pin ownership

#### should keep an actively leased mapping resident when pressure evicts unpinned entries

1. Acquire an explicit `LoaderResourceLease`.
2. Apply entry/byte pressure while the lease is active.
3. Verify an active mapping is not evicted; if all candidates are pinned,
   admission is refused.

#### should treat repeated raw get calls as one idempotent legacy pin until the caller boundary

1. Call legacy `SmfCache.get` repeatedly for one resource.
2. Verify `legacy_pinned_entries` does not grow once per hit.
3. Verify only the established explicit evict/clear/drop boundary releases the
   implicit pin.

### P4-A04 — Generation and reload

#### should retain an old leased generation while publishing a fresh generation after eviction

1. Evict the reusable generation and reload the same path.
2. Verify the new generation has a monotonic identity while the old leased
   generation remains resident.
3. Submit stale, duplicate, and foreign releases; verify none decrement the
   fresh resource.

#### should make zero retention non-reusable without killing a usable current lease

1. Set retained entry and payload retention to zero.
2. Verify no reusable cache entry is retained while a returned lease remains
   usable.
3. Verify a zero hard mapping ceiling refuses mapping before allocation.

### P4-A05 — Failed release retention

#### should retain failed releases and their bytes for retry instead of claiming eviction

1. Force a native release failure through the production owner.
2. Verify `release_failures`, retired ownership, and resident bytes remain
   charged.
3. Retry the release and verify counters change only after acknowledged success.

#### should preserve the primary update or compile error while recording cleanup failure separately

1. Publish a successful mapping and fail the optional SMF update.
2. Verify the result is `UpdateFailed` with its primary error intact.
3. Verify cleanup evidence is recorded separately and does not erase mapping
   ownership.

### P4-A06 — Shared object mapper lifetime

#### should account actual mapped extents and keep callable addresses alive through the owner lease

1. Acquire executable storage through the shared mapper.
2. Verify accounting uses the actual mapped extent, not only code length.
3. Verify the callable address remains valid until the final owner lease is
   released, then unmaps exactly once.

#### should reject stale or foreign mapper releases without decrementing totals

1. Submit stale, duplicate, and foreign release receipts.
2. Verify each is rejected by owner/generation/token identity.
3. Verify `owned_mapping_entries` and `owned_mapping_bytes` are unchanged.

### P4-A07 — Dual import route classification

#### should classify provider-backed and direct-file imports as separate loader routes

1. Exercise the provider-backed byte route.
2. Exercise the direct-file compatibility fallback.
3. Verify the receipt records route identity and does not merge unlike native
   and compatibility evidence.

#### should keep the compatibility surface from claiming native mapping admission

1. Inspect the root compatibility SMF surface separately from the loader
   owner.
2. Verify compatibility types preserve their existing API without fake native
   claims.
3. Verify native mapping receipts originate only from the `99.loader/loader`
   owner and carry the production mapper identity.

## Evidence and admission

The executable spec is the authority for seam presence and scenario traceability.
P3 must replace each fail-fast seam with production-owner execution checks,
including exact counter equality after every operation, native acquire/read/
release, callable-address lifetime, and matched native/compatibility receipts.
Source scans, model mappers, raw pointers, and synthetic timing/RSS values do
not close this manual. The larger startup, interpreter, compiler, dynlib,
cross-language, and generated-binary matrix remains separate work.

<details>
<summary>Executable SSpec</summary>

Run:

```text
bin/simple test test/05_perf/loader_mapping_bounds_spec.spl --mode=interpreter
```

</details>
