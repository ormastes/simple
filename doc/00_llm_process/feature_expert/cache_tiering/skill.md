# Feature Expert: Cache Tiering (Semantic Incremental Build v2)

## What this is
The tier/storage/GC layer built on top of the Option-C identity layer
(see [cache_identity](../cache_identity/skill.md) — read that first; this
feature adds NO new hash scheme and reuses its canonical encoder).

Three scopes: L1 workspace (`.simple/build-cache/`), L2 machine
(`$SIMPLE_CACHE`, falls back under `.simple/machine-cache/`), L3 remote-main
(read-only; writes are trusted-CI-only and currently DISABLED).

**Status: first milestone. Compute-and-store only — nothing in the normal
compile path consumes these modules yet.** The live cache is still
`.build_cache.sdn` + `.build/mir_cache/`.

## Source of truth
- Design (normative): `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md`
- Plan + waves: `doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md`
- **Frozen contract:** `doc/03_plan/compiler/cache/c0_schema_freeze_2026-08-09.md`
  (schema_version 2, 20 canonical positions; 1–14 byte-identical to v1 and
  already proven). Any rename/reorder/removal is a schema_version bump.
- Schema: `src/compiler/80.driver/cache/schema/cache_protocol.sdn`
- Known gaps: `doc/08_tracking/bug/cache_v2_first_milestone_known_gaps_2026-08-10.md`

## Code map
| File | Role |
|---|---|
| `cache/cas_store.spl` | CAS + `ResultManifest` + **closure-gated publish**: an action mapping is written only after every referenced artifact digest exists. Verify-before-serve, quarantine on mismatch. |
| `cache/action_index/action_index.spl` | `ActionDigest -> ResultManifestDigest`, namespace-scoped. Same key + different result = `Conflict`, **never** an overwrite. |
| `cache/tier_router/tier_router.spl` | L1→L2 **exact-key** lookup, L2-hit read-through backfill into L1, process-local memo as single-flight guard. |
| `cache/metadata/cache_limits.spl` | high 0.90 / low 0.75 watermarks, hard_limit_ratio 1.05, min_free_ratio 0.05, tmp 24h, quarantine 7d. |
| `cache/lease/lease.spl` | File-per-lease under `leases/`; acquire/release/heartbeat; stale reclaim needs dead-process proof or a conservative 6h timeout. |
| `cache/gc/fast_gc.spl` | tmp/quarantine expiry, oldest-first eviction of unleased mappings, atomic rename to `trash/`. Stops at the LOW watermark (hysteresis). |
| `cache/gc/mark_sweep.spl` | Roots = pins + leases + retained mappings; marks manifests then their artifacts. **Refcounts are advisory, mark-sweep is authoritative.** |
| `cache/gc/admission.spl` | Pre-write reject over hard limit / under reserve — a rejected cache write is a SKIP, never a build failure. `PinnedOverflow` reports instead of deleting protected roots. |

Specs: `test/01_unit/compiler/cache_v2/{tier_router,gc}_spec.spl`.
Adversarial fixtures: `test/02_integration/compiler/cache_v2/fixtures/`.

## Landmines
- **CAS paths split the digest** across a 2-char directory and the remainder
  filename (`cas/sha256/ab/cdef…`). A `path.contains(full_digest)` membership
  test therefore NEVER matches — it silently reports "unreferenced" for every
  live blob. C3 shipped this bug and caught it; use exact-path equality against
  `cas_blob_path`/`cas_action_path`. This is the single easiest way to write a
  GC that deletes live data while all its tests pass.
- **Exact-key only.** No prefix, restore-key, nearest-branch, or timestamp
  fallback may ever return a compiler artifact. A "helpful" fuzzy lookup here is
  a correctness bug, not a feature.
- **Git identity is admission, never identity.** Branch/commit/PR/CI-run never
  enter `ActionDigest` — they live in `PromotionReceipt`. Adding one would
  destroy cross-branch sharing while proving nothing.
- GC may cause a **false miss** but never a dangling hit. When in doubt,
  over-invalidate.
- Trash and quarantine are never served. Publishing an action mapping before its
  full artifact closure exists is the crash-window bug this design exists to
  prevent.
- Every verdict cited in the landed commits came from the **Rust seed** binary.
  GREEN here does not prove self-hosted correctness.

## Verification
```bash
bin/simple test test/01_unit/compiler/cache_v2/tier_router_spec.spl   # 6/6
bin/simple test test/01_unit/compiler/cache_v2/gc_spec.spl            # 8/8
```
Only the `SPEC FILE VERDICT ... executed=N` line (N>0) is evidence — exit 0
alone proves nothing (an absolute path makes `simple test` run nothing and
still exit 0).

Every behavioural change here was sabotage-probed: break impl → observe RED →
revert → observe GREEN. A GC/cache test that cannot fail proves nothing, because
the failure mode is silent data loss.
