# driver_cache Layer Expert

## Role

Own layer-specific process knowledge for the driver's cache layer
(`src/compiler/80.driver/cache/`). This layer owns build artifact identity
(SHA-256 action keys and CAS blobs; BLAKE3-256 package TLDR interface/action
archive keys), content-addressed storage, the workspace/machine/remote
tier router, storage quota and garbage collection, and remote-main promotion
policy.

**It decides what may be REUSED instead of recomputed. A false hit here is
silent miscompilation; a false miss is only wasted time.** Every ambiguity in
this layer resolves toward recomputation.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl.md)

## Layer Links

- Identity/encoder: [src/compiler/80.driver/cache/action_key.spl](../../../../src/compiler/80.driver/cache/action_key.spl)
  — the ONE canonical encoder. Every digest in this layer routes through its
  `canon_str`/`canon_nat`/`canon_field`/`canon_seq` helpers.
- CAS + result manifests: [src/compiler/80.driver/cache/cas_store.spl](../../../../src/compiler/80.driver/cache/cas_store.spl)
- Tier router: [src/compiler/80.driver/cache/tier_router/tier_router.spl](../../../../src/compiler/80.driver/cache/tier_router/tier_router.spl)
- Action index: [src/compiler/80.driver/cache/action_index/action_index.spl](../../../../src/compiler/80.driver/cache/action_index/action_index.spl)
- GC / leases / limits: `src/compiler/80.driver/cache/{gc,lease,metadata}/`
- Promotion / remote policy: `src/compiler/80.driver/cache/{promotion,remote}/`
- Frozen schema: [src/compiler/80.driver/cache/schema/cache_protocol.sdn](../../../../src/compiler/80.driver/cache/schema/cache_protocol.sdn)
- Formal model: `src/verification/cache_protocol/` (imports the frozen
  `cache_identity` v1 project; does not re-declare it)

Feature wikis: [cache_identity](../../feature_expert/cache_identity/skill.md),
[cache_tiering](../../feature_expert/cache_tiering/skill.md),
[interface_compat](../../feature_expert/interface_compat/skill.md).

## Layer rules

1. **One hash scheme.** Never add a second encoder or a second CAS. The schema
   freeze (`doc/03_plan/compiler/cache/c0_schema_freeze_2026-08-09.md`) fixes 20
   canonical positions; positions 1–14 are byte-identical to v1 and already
   proven. A rename, reorder, or removal is a `schema_version` bump, not a patch.
   The digest function is part of the key: `package_tldr_interface_key_v1` and
   `package_tldr_action_key_v1` hash with BLAKE3-256 under the `/v2` domain tags
   (2026-10-18). The frontend private parse (`.fpc`) key is XXH3-128 through the
   `rt_xxh3_128_text` accelerator (2026-10-19), and the M2->M3 `.fpc` binding
   re-derives it with `frontend_parse_cache_key`, never the build cache's SHA-256
   `content_hash`. `cas_put`/`cas_get` and HIR body digests stay on SHA-256 (64
   hex is pinned there; switching needs a schema bump, not just the accelerator).
2. **Exact-key lookup only.** No prefix, restore-key, nearest-branch, or
   timestamp fallback may return a compiler artifact.
3. **Git identity is admission, never identity.** Branch, commit, PR number, and
   CI run belong in `PromotionReceipt`, never in `ActionDigest` — putting them in
   the key destroys cross-branch sharing and proves nothing.
4. **Publish an action mapping only after the full artifact closure exists.**
   The crash window between "blob written" and "mapping published" is the bug
   this ordering exists to prevent.
5. **Adding a KEY field requires a matching visibility theorem.** The formal gate
   compares semantic field count against generated theorem count and FAILS when
   they diverge. Do not add a field and defer the proof.
6. **Developer machines never write remote-main.** There is deliberately no flag
   or env var that can flip it; keep it that way.

## Verification for this layer

```bash
bin/simple test test/01_unit/compiler/cache_v2/tier_router_spec.spl
bin/simple test test/01_unit/compiler/cache_v2/gc_spec.spl
bin/simple test test/01_unit/compiler/cache_v2/promotion_spec.spl
sh scripts/check/check-cache-protocol-formal.shs     # PASS/FAIL/ERROR on last line
```

Guard verdicts are the LAST line of stdout, and the exit code is authoritative:
0 = PASS, 1 = FAIL, 2 = ERROR (nothing checked). **Capture before inspecting** —
`sh guard.shs | tail -1; echo $?` reports `tail`'s status and has already produced
a false "the gate fails open" reading in review.

Sabotage-probe every behavioural change in this layer. A cache test that cannot
fail proves nothing, because the failure mode is silent: wrong bytes served
confidently, or live data deleted while all tests stay green.

## Status caveat

The live cache is still `.build_cache.sdn` + `.build/mir_cache/` — legacy makes
every decision. The only reachable v2 path is **shadow mode**
(`src/compiler/80.driver/cache/integration/shadow_mode.spl`, opt-in
`SIMPLE_CACHE_V2_SHADOW=1`, hooked in `driver_build/incremental.spl`): it
compares, never decides. Its ActionKey is coarser than the frozen 15-field
intent (empty target/cfg/witness fields) — safe only because shadow output is
advisory; do NOT promote shadow to authoritative before real interface digests
populate the key. Shadow sees recompiled modules only (legacy hits bypass it).
C5 block cache (`cache/block/`) and the C9 gateway (`src/app/cache_gateway/`)
exist but have no consumers.

- 2026-10-25: landed cache protocol: `.spab` (opt-in `SIMPLE_FRONTEND_SPAB=1`), DigestV1 (unknown algo = miss, at most 3 per side), GuardIdV1, single-flight, usage ledger, reference-aware eviction, Lean gates `check-cache-protocol-formal.shs` / `check-cache-formal-source-binding.shs`. See `doc/07_guide/tooling/bootstrap_options.md`.
- 2026-10-25: Per-file src to obj is the DEFAULT (#4525 compiler, #4542 guide, scripts PR 2026-10-25): each module lowers to its own `aot-<hash>.o` in the per-module object cache under `SIMPLE_NATIVE_BUILD_CACHE_DIR`, codegen fans out over `SIMPLE_NATIVE_BUILD_THREADS` (scripts: host.sdn `max_build_jobs`), then all objects link into one binary. Stage 3 scripts pass `SIMPLE_BOOTSTRAP=` empty so the bootstrap_fixed shortcut is not forced; `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` opts back into the whole-program lane (hashed into the Stage 3 args). First-object proof: 9-module closure, 9 objects, first at 160 s, last at 174 s, binary runs. Object cache: `driver_aot_native_output.spl` (`driver_native_build_cache_dir`, scope dir + `build_cache.sdn`).
- Superseded 2026-10-25; default updated 2026-10-26: `.spab` is the DEFAULT parse-cache store (#4582, #4589 zero-copy hit); `SIMPLE_FRONTEND_SPAB=0` opts out (`src/compiler/10.frontend/frontend_spab_cache_v1.spl:11,40`). The true per-file `--file-worker` pipeline (#4576 #4584 #4585 #4588 #4594 #4575 #4580 #4597 #4598 #4603) is selected by default when `SIMPLE_FILE_WORKERS` is unset (`NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "1"`); `SIMPLE_FILE_WORKERS=0` opts out. `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` keeps the whole-program route. No native overlap receipt exists yet, so the shared default is not qualification evidence. Contract: `doc/05_design/compiler/incremental_build/true_per_file_pipeline_v1.md`.
