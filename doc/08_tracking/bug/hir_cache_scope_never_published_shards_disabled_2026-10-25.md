# HIR cache scope never published; HIR/MIR shards disabled

- **Status:** Fixed (branch `work/hir-cache-scope-publish-20261025`)
- **Date:** 2026-10-25
- **Area:** native-build orchestration, frontend/HIR cache identity (`80.driver`, `app/cli/native_build_main.spl`)

## Symptom
Every stage-3 / per-file-lane `native-build` with the frozen stage-2 Windows compiler:
- parent: `[hir-cache] disabled reason=no-compiler-scope`
- HIR shard children: `HIR cache identity unavailable for shard`
- MIR shard children: "HIR inventory/cache unavailable"

The parent then lowers all 1453 modules single-threaded (~56-59 min) and MIR falls back to the
single-process path.

## Evidence
308-module `src/app/cli/lint_entry.spl` closure, frozen stage2, `SIMPLE_FRONTEND_CACHE=1`,
`SIMPLE_FRONTEND_CACHE_DIR`, `SIMPLE_HIR_CACHE=1`, `SIMPLE_HIR_CACHE_DIR`, `--entry-closure --mode dynload`:
- run3/run4 (default): `no-compiler-scope`; parse rows `cached=0`; frontend cache dir empty even after
  the parse shard printed `done ... parses=308`.
- run1: every HIR shard child failed `HIR cache identity unavailable for shard`; build aborted.
- run2 (only change `SIMPLE_FRONTEND_CACHE_SCOPE=probe-scope-1`): `[frontend-cache] hits=308`,
  4 HIR shards lowered 307 modules in parallel, `[hir-cache] ... stores=72 refused=0`.

## Mechanism
1. The retained parse path gated publication on `options.mode == CompileMode.Interpret`. In a compiled
   stage2 the enum does not survive the options transport (see `bootstrap_main.spl`), so the gate
   misfired and the scope was never published. `cli_mode_text` is the reliable channel.
2. Shard children are spawned by `native_build_focused_capsule_shards_v1` before the parent's phase 2
   publishes anything, so children never inherited one identity, and none computed its own.
3. Since #4525 the default stage-3 lane runs with explicit semantic policy, and both HIR lowering sites
   forced the closure digest to `""` under that policy, so HIR shards died with
   `HIR cache identity unavailable for shard` even when a scope existed.

## Fix
1. `driver_frontend_cache_scope_publish_allowed_v1(mode_text, cli_mode_text)` (new leaf
   `driver_cache_scope_policy_v1.spl`) replaces the enum-only gate in
   `driver_source_pipeline_parsing.spl`; only an interpret run is refused.
2. `native_build_publish_cache_scope_v1` publishes `SIMPLE_FRONTEND_CACHE_SCOPE` once (via
   `native_build_cache_scope_key(nil, nil, [], 0, native_build_frontend_identity())`, after pinning
   `SIMPLE_BINARY` to the running compiler) before any shard spawns; prints
   `[cache-scope] published source=orchestrator`. Skipped when already set or both caches are `0`.
3. HIR cache decoupled from the frontend ON/OFF switch: `hir_cache_identity_scope_v1` uses the published
   scope when `SIMPLE_FRONTEND_CACHE=0`; `native_build_hir_shard_count` no longer requires the frontend
   cache. Header is byte-identical when both caches are on.
4. `hir_cache_digest_allowed_v1` admits the explicit-semantic-policy lane;
   `hir_cache_policy_closure_digest_v1` appends `|compiler_explicit_semantic_policy=1` to that lane's
   digest so its entries never alias default-lane entries (default-lane digests unchanged).

## Pin
`test/01_unit/compiler/driver/driver_cache_scope_publication_spec.spl` (mirror in `test/unit/...`):
publish gate truth table, identity-scope table, digest admission and policy folding.
Not run on the Windows host: `parse: in ...windows_redirected_process.spl: Unexpected token: expected Fn, found Colon`.

## Expected effect
HIR shards admitted (12-80 workers per the lane's memory policy); the parent adopts cache hits
(~0.2 s/module) instead of lowering (~1.4 s/module); MIR shards get their HIR inventory.

## Follow-up
The frontend `.fpc` hit path is 3.5x slower than a cold parse on this binary (455 ms vs 130 ms per
file). Separate bug; lanes may run `SIMPLE_FRONTEND_CACHE=0` while keeping the HIR cache.
