# HIR/native cache identity is invalidated by unrelated env changes

- **Date:** 2026-11-22
- **Status:** open
- **Severity:** P2

## Symptom

A cosmetic environment change discards most of the HIR cache.

## Evidence

Phase 3 build f27 reused f26's cache dir but reported `[hir-cache] hits=206 misses=1707` (then hits=287 misses=1937). Between f26 and f27 the env gained `SIMPLE_ABI_ADMISSION_RECEIPT` and the cache root moved. Cache identity folds the whole `SIMPLE_*` environment, so about 90% of the HIR cache was lost.

## Repro

Run two consecutive builds over the same cache dir, adding one unrelated `SIMPLE_*` variable for the second; compare `[hir-cache]` hit counts.

## Workaround

Keep the `SIMPLE_*` environment byte-identical between builds that should share a cache.

## Fix direction

Key the cache on a declared allowlist of semantic env keys instead of the whole `SIMPLE_*` environment.
