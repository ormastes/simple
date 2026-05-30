# Native immutable map/set facade probes fail from committed test paths

Date: 2026-05-14
Status: Resolved for committed-path smoke probes

## Summary

Focused native probes for `PersistentMap` and `PersistentSet` through the immutable facade roots now pass from committed `test/unit/lib/...` paths. The root cause was missing explicit `-> []` return annotations on HAMT and collision helpers that return array-shaped nodes/entries; native lowering could preserve `set()` length behavior while losing stable lookup shape for `get()` after `set()`.

## Reproduction

These committed-path probes originally failed natively with one failed file and no per-expect detail:

```bash
SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/gc_async_immut/map_facade_native_spec.spl --mode=native --clean --force-rebuild --format json
SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/backend_facade_map_native_probe_spec.spl --mode=native --clean --force-rebuild --format json
```

The temporary `tmp/gc_async_immut_map_native_probe_spec.spl` body with `PersistentMap.empty().set("a", 1).get("a")` passed natively before the temporary file was removed. After adding explicit array return annotations in `src/lib/nogc_async_immut/persistent_map/hamt_node.spl` and `src/lib/nogc_async_immut/persistent_map/collision.spl`, the committed-path map/set facade smoke specs pass natively across `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut`.

## Impact

Runtime-family promotion is no longer blocked on committed-path `PersistentMap`/`PersistentSet` smoke probes. Broader promotion remains blocked on overwrite/removal paths, deeper set behavior, trie mutation/lookup, and cleanup of known native type-loader/minimal-runtime-stub warnings.

## Next Steps

- Keep the committed-path smoke specs as the promotion gate for future native return-shape regressions.
- Broaden coverage to map overwrite/removal, set membership/removal, and trie mutation/lookup.
- Resolve known native type-loader and minimal-runtime-stub warnings before promoting the immutable facade families from advanced-scoped to public.
