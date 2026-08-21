# native-build object cache never persisted entries: second identical build = 0 hits (2026-08-21)

**Status:** FIXED (working tree, stage-1 bootstrap lane); spec
`test/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.spl`.

## Symptom

`build/native_cache` (and every `build/bootstrap/native_cache/<lane>/`) held only
metadata: `build_cache.sdn` was always

    version: 2
    entries: [
    ]

(23 bytes), so a second, byte-identical `native-build` recompiled every module.

## Repro (3-module fixture, seed8 `/mnt/data/.cargo-target-fable/release/simple`, `scratchpad/cachefx/`)

```
SIMPLE_CACHE_SCOPE=cachefx simple native-build --source src --entry-closure --threads 4 \
  --cache-dir cache --entry src/main.spl -o out1   # run1: [NATIVE] cache: 0 hits, 3 misses, 66 s
... identical run2                                  # BEFORE: 0 hits, 3 misses, 11 files rewritten
                                                    # AFTER:  3 hits, 0 misses, 0 objects rewritten
```

After the fix run2 writes only `build_cache.sdn`, `.cache_scope`, `phase.marker`,
`manifest.sdn` and the `.smf` sidecar; `object.*.o` and their
`.capsule-receipt`s are untouched and `build_cache.sdn` carries one row per
module (1,972 bytes).

## Root cause

`src/compiler/80.driver/driver_aot_native_output.spl`: the per-capsule
checkpoint `driver_native_collect_capsule_result_v1(batch, build_cache, name,
obj)` calls `build_cache.update_entry(..)` + `build_cache.save()` on the
`BuildCache` it received as a CALL ARGUMENT (directly on the single-module
path, via `builder.set_owner_collect(..)` on the parallel path). That update
never reaches the caller's `build_cache` instance — the seed interpreter
hands `me`-method self-updates back by variable NAME into the callee frame
only — so the caller's final `build_cache.save()` (line ~893, "Save build cache.
Done BEFORE the fail-closed check") wrote its still-empty entry map over the
checkpoint's file. Every build therefore ended with `entries: []`, and every
lookup on the next build missed.

## Fix

In the post-process loop that reconstructs outputs from `uncached_names`, record
`build_cache.update_entry(capsule.cache_source, FileFingerprint.from_file(..), [], [obj_path])`
on the CALLER's cache for every capsule whose receipt validates, before the
final `save()`. The per-capsule checkpoint is left in place (it still gives a
partial file if the parent dies mid-phase).

## Related

- `--cache-dir` / `--threads` do reach the driver (`SIMPLE_NATIVE_BUILD_CACHE_DIR`
  / `SIMPLE_NATIVE_BUILD_THREADS` are exported by `app.io._CliCompile.compile_targets`);
  that wiring was not the defect.
- The cache scope directory already folds `SIMPLE_CACHE_SCOPE` (`lane=`), the
  compiler identity and a `sources-<interface fingerprint>` component, so the
  fix makes incremental stage builds in one lane genuinely reusable.
