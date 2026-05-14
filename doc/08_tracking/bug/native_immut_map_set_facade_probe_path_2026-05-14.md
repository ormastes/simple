# Native immutable map/set facade probes fail from committed test paths

Date: 2026-05-14
Status: Open

## Summary

Focused native probes for `PersistentMap` and `PersistentSet` through the immutable facade roots are not yet suitable for committed test coverage. The same single-operation `PersistentMap` body passed from a temporary `tmp/` probe during diagnosis, but failed when committed under `test/unit/lib/...`; this suggests a native test path/module naming or source-root interaction rather than enough evidence to promote map/set facade behavior.

## Reproduction

These committed-path probes failed natively with one failed file and no per-expect detail:

```bash
SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/gc_async_immut/map_facade_native_spec.spl --mode=native --clean --force-rebuild --format json
SIMPLE_LIB=src cargo run --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple -- test test/unit/lib/backend_facade_map_native_probe_spec.spl --mode=native --clean --force-rebuild --format json
```

The temporary `tmp/gc_async_immut_map_native_probe_spec.spl` body with `PersistentMap.empty().set("a", 1).get("a")` passed natively before the temporary file was removed.

## Impact

Runtime-family promotion remains blocked for map/set/trie native behavior coverage. Do not mark `PersistentMap` or `PersistentSet` facade behavior as promoted until committed-path native specs pass.

## Next Steps

- Identify whether native test module naming, file path, source-root closure, or BDD lowering differs between `tmp/` probes and committed `test/unit/lib/**` probes.
- Reintroduce committed specs only after native pass evidence exists from the committed paths.
- Then broaden coverage to map overwrite/removal, set membership/removal, and trie mutation/lookup.
