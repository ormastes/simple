# HIR cache: sharded and direct Stage 3 routes never share an entry

Date: 2026-10-20
Status: OPEN. Diagnosis measured; fix depends on the closure-walk parity lane.

## Symptom

Stage 3 (r16b Stage 2 compiler, lane `simple-lane-boot6`, direct route) logged
`[hir-cache] hits=0 misses=1352 stores=1352 ... rejected=absent:1352` against a
cache dir (`stage3-native-cache/hir`) that already held 2261 entries stored by
the earlier SHARDED r16b run. Every lookup missed as `absent`, so the key itself
differs; no entry was rejected for header, checksum or decode.

## Measured key-input differences

`hir_cache_key` (`src/compiler/80.driver/driver_hir_cache.spl`) hashes
`sha256(source_path)`, the source bytes, `hir_cache_closure_digest(surfaces)`,
the entry flag, five env switches and the codec header. The entry headers of
both sets are byte-identical (same producer identity), so two inputs differ:

| input | sharded workers | direct route |
|---|---|---|
| `source_path` embedded in the entry | absolute SCV snapshot path, `/home/.../build/scv/snapshots/scv-revision-v1-<rev>/src/...` (2259 of 2260) | relative `src/...` (1352 of 1353) |
| closure surfaces | 2259 distinct modules (includes `src/plugins/backend_vulkan`, `backend_vhdl`, ...) | 1353 modules |

Both feed the key: the path digest directly, and the closure digest through
each surface's `canonical_path` and through the surface count. The module sets
overlap completely (all 1353 direct modules appear in the sharded set), so the
divergence is the path form plus the sharded walk's 906 extra modules.

## Why the key cannot just ignore the path

Cached HIR retains the physical source path, and `HirModule.name` IS that path
(the MIR scope-trace selector matches it). A key that dropped the path form
would hand the direct route a module named by a snapshot path. Sharing needs
one of:

1. both routes present the same canonical source path (the direct route opening
   the same SCV snapshot paths the workers use, or the workers presenting
   root-relative paths); or
2. a root-relative key plus rebasing every embedded path on load.

And the closure digest is whole-closure: until the sharded walk and the direct
walk produce the same surface set (`work/closure-walk-parity`, uncommitted WIP
in `/home/yoon/dev/simple-lane-walkparity` touching `native_build_closure.spl`,
`driver_source_loading.spl`, `driver_source_pipeline_loading.spl`), the inputs
genuinely differ and a miss is the correct answer. A per-module dependency
closure digest (only the surfaces a module transitively imports) would make the
key depend on semantic inputs alone, but that is a key redesign, not a tweak.

## Next step

Land walk parity first, then option 1 (one canonical path form for both
routes). Re-measure with the `[hir-cache] hits=` line on a direct run against a
sharded-populated dir.
