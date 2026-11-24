# Native object cache never reused across cache dirs (cached=0 after a 5-file change)

Status: open (analysis only; no fix landed)
Symptom: bootstrap_main.spl Phase 3 rerun, 5 sources changed, previous 1472
`aot-<hash>.o` + `.capsule-receipt` copied into the tree's `build/`, run with a
FRESH `SIMPLE_NATIVE_BUILD_CACHE_DIR`: HIR cache 568/576 reused, but
`native_cache total=1598 cached=0 misses=1598`.

## Root cause (proven from source; the live run itself was not re-executed)

A native object hit needs ALL of the following, and every one is bound to the
cache directory, not to the module:

1. `build_cache.get_cached_outputs(cache_source)` non-nil
   (`src/compiler/80.driver/driver_aot_native_output.spl:2931-2935`). The
   `BuildCache` is loaded from `<cache_dir>/build_cache.sdn`
   (`driver_aot_native_output.spl:930-931`, load at `:2640`). A fresh dir has no
   build_cache.sdn, so `cached_outputs` is nil for every module. Copied `.o`
   files are never consulted without it. This alone explains `cached=0`.
2. Scope directory `<cache_dir>/s<hash>`; the hash folds the environment identity
   (`driver_aot_native_output.spl:947-972`). `SIMPLE_NATIVE_BUILD_CACHE_DIR` is a
   semantic environment field (`cache/native_build_environment_identity.spl:87`)
   and, unlike `SIMPLE_NATIVE_NOOP_FINAL_OUTPUT`, `SIMPLE_MIR_SHARD*` etc., it is
   in none of the exclusion lists (`:262-450`; grep finds no other mention). `PWD`
   (`:34`) is likewise folded. So a different cache dir => different scope name.
3. Object path `native_aot_object_path_v1` hashes the absolute
   `output_base` (= `<cache_dir>/<scope>/object`)
   (`src/compiler/80.driver/native_aot_artifacts.spl:26-28`), so the
   `aot-<hash>.o` names differ per cache dir. Copying old files into `build/`
   cannot match: lookup only uses `object_base` under the cache scope root
   (`driver_aot_native_output.spl:2634`), never `build/`.
4. `FrozenNativeModuleCapsuleV1.expected_identity()` embeds `object_path`
   (`driver_types.spl:191-192`) and the capsule check requires
   `scoped_outputs[0] == cached_capsule.object_path` (`:2973`), so even a
   correctly copied object + receipt is rejected when its absolute path moved.

Per-module keys are NOT polluted by whole-program digests: the module witness
(`driver_native_shadow_witness_v1`, `:395-446`) folds only the module's own MIR
identity, direct dependency/resolution facts, external layouts and config; the
closure digest is explicitly diagnostic-only (`:2589-2595`). MIR shard identity
(`SIMPLE_MIR_SHARD*`) is excluded from the fingerprint (`:276-311`). So a 5-file
change should invalidate only the touched modules plus dependents whose
dependency/layout facts changed (inferred, not measured).

## Inferred (not proven)
That the reporter's rerun used a different cache dir than the first run is
inferred from "fresh dir". If both runs shared one dir, items 1-4 do not apply
and the miss would come from the witness/capsule (config fingerprint or
environment field drift); then compare `[NATIVE] ... witness_reason` lines
(`witness_shadow_mismatch_lines`, `:2927-2929`).

## Why no fix in this change
Making keys relocatable means changing the capsule identity (drop absolute
`object_path` / hash a scope-relative path), the object naming, the scope-name
environment fold, and a way to import/rebase build_cache.sdn entries. That alters
capsule/receipt schema across several consumers
(`driver_collection_native_receipt.spl`, `cold_hir_native_object_persistence_v1.spl`,
`smf/runtime_std_native_sections_v1.spl`, `native_mir_shard.spl:441`) and cannot
be validated without a native build, which is not allowed on this host.

## Workaround
Reuse the SAME `SIMPLE_NATIVE_BUILD_CACHE_DIR` (and same cwd) across reruns;
do not copy objects between dirs.

## Proposed fix
- Add `SIMPLE_NATIVE_BUILD_CACHE_DIR` (and `PWD`) to the projection exclusions.
- Bind object names and capsule `object_path` to a scope-relative path.
- Provide a build_cache.sdn rebase (like `build_cache_rebind_scv_snapshot_all_v1`)
  for relocated cache dirs.
- Add a spec on `native_aot_object_path_v1` / environment fingerprint asserting
  the key is invariant to cache dir.
