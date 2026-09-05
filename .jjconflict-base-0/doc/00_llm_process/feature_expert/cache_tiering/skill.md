# Feature Expert: Cache Tiering (Semantic Incremental Build v2)

## What this is
The tier/storage/GC/promotion/AOP-group layer built on top of the Option-C identity
layer (see [cache_identity](../cache_identity/skill.md) — read that first; this
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
- Guide: `doc/07_guide/compiler/semantic_build_cache.md`

## Code map — storage tiers (C1) and GC (C3)
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

## Code map — remote promotion (C2)
| File | Role |
|---|---|
| `cache/promotion/promotion_receipt.spl` | `PromotionReceipt` per design §14.5; signing digest split from full-record digest. |
| `cache/promotion/eligibility.spl` | The 10 §15.1 conditions as an explicit conjunction. Returns **which** condition failed — never a bare boolean. |
| `cache/promotion/git_ancestry.spl` | `GitAncestryOracle` (injectable, so tests don't depend on repo state). `MainSnapshot` carries remote URL/repo id/tip/fetch time/auth flag; `snapshot_is_fresh` enforces max-age + authenticated fetch, so a **stale local `origin/main` cannot authorize promotion even when the raw ancestry bit is true**. |
| `cache/remote/remote_policy.spl` | §15.4 matrix as frozen literal data over 6 producer classes. |
| `cache/remote/remote_client.spl` | Read-only. `RemoteTransport` exposes only `fetch_*`; the §14.2 verification order names which step failed. |

## Code map — AOP invalidation groups (C4)
Under `src/compiler/85.mdsoc/aop_cache/` and `aop_index/`: group keys, Merkle
candidate partitions by `(module_path, join_point_kind)`, the four reverse
dependency tables, and the §16.5 invalidation transaction.

## Formal model (C6)
`src/verification/cache_protocol/` — a NEW Lean project that **imports** the frozen
`cache_identity` v1 rather than re-declaring it, so v2 binds to the already-proven
v1 encoder. 74 theorems, zero `sorry`/`admit`/`axiom`/`native_decide`.
Generator: `src/app/gen_cache_model/`. Gate:
`scripts/check/check-cache-protocol-formal.shs`.

Golden vectors are checked by Lean `decide` against bytes computed independently by
the Simple generator — correspondence is a **proof**, not a diff.

Two theorems are openly NOT closed: wire-format injectivity (needs a prefix-code
parsing argument; injectivity holds at the `Canon` term level) and correspondence to
`action_key.spl`'s production encoder (no v2 encoder exists there yet).

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
- **A fresh ancestry bit is not enough for promotion.** `git merge-base
  --is-ancestor` against a stale local `origin/main` says "yes" for commits that
  are not on the real main. Freshness + authentication of the snapshot is part of
  the proof, not a nicety.
- **The AOP layer is built over a tree that has no pointcuts.** Matching is an
  untyped `WeavingRule.predicate_text` string, weaving mutates MIR in place (no
  per-target artifact), and `BlockId` is a transient integer that must never be
  serialized into a key. 7 of the 11 invalidation-matrix rows therefore
  deliberately OVER-invalidate, each flagged `conservative=true` with a reason.
  Over-invalidation is fine; under-invalidation is the only unacceptable outcome.
- GC may cause a **false miss** but never a dangling hit.
- Trash and quarantine are never served. Publishing an action mapping before its
  full artifact closure exists is the crash-window bug this design exists to
  prevent.
- Every verdict cited in the landed commits came from the **Rust seed** binary.
  GREEN here does not prove self-hosted correctness.

## Verification
```bash
bin/simple test test/01_unit/compiler/cache_v2/tier_router_spec.spl   # 6/6
bin/simple test test/01_unit/compiler/cache_v2/gc_spec.spl            # 8/8
bin/simple test test/01_unit/compiler/cache_v2/aop_group_spec.spl     # 12/12
bin/simple test test/01_unit/compiler/cache_v2/promotion_spec.spl     # 33/33
sh scripts/check/check-cache-protocol-formal.shs                      # PASS, exit 0
```
Only the `SPEC FILE VERDICT ... executed=N` line (N>0) is evidence — exit 0
alone proves nothing (an absolute path makes `simple test` run nothing and
still exit 0).

**Do not read a guard's exit code through a pipe.** `sh guard.shs | tail -1; echo $?`
reports `tail`'s status, not the guard's — this produced a false "the gate fails
open" reading during review. Capture first: `out=$(sh guard.shs); rc=$?`.

**A scan that finds nothing may have scanned nothing.** The trust-bypass grep
returned clean against a path that did not exist. Always pair an absence check
with a control that must produce a hit.

Every behavioural change here was sabotage-probed: break impl → observe RED →
revert → observe GREEN. A GC/cache test that cannot fail proves nothing, because
the failure mode is silent data loss.
