# Native Immutable Facade Collection BDD Blockers

Status: closed
Date: 2026-05-14

## Impact

The `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut` facade families have native BDD coverage for root immutable map one-entry, two-entry, branch-shaped insert, branch-shaped overwrite, and branch-shaped removal committed paths; root immutable set one-entry, two-entry, branch-shaped insert, dedupe, and branch-shaped removal committed paths; package-level `persistent_trie` shared-prefix/overwrite paths; and typed plus untyped chained root-facade `PersistentTrie` shared-prefix paths. The tracked collection facade blockers in this report are closed; broader public promotion still depends on clearing native type-loader/minimal-runtime-stub warnings and any additional full-suite coverage gaps tracked in the runtime family support matrix.

## Evidence

- Plain native `run` completes reduced HAMT remove and trie shared-prefix/overwrite probes with expected printed values.
- Direct no-GC async trie-node native BDD coverage now passes for shared-prefix `trie_set`/`trie_get` via `test/unit/lib/nogc_async_immut/trie_node_native_spec.spl`.
- Interpreter `test/unit/lib/immut/persistent_trie_spec.spl` now passes all `82` examples against the pair-array trie backend, including `from_dict`.
- Package-level native BDD specs now pass for `PersistentTrie.empty().set("app", 1).set("apple", 2)` and overwrite behavior through `std.{gc_async_immut,gc_sync_immut,nogc_sync_immut}.persistent_trie.{PersistentTrie}` via `test/unit/lib/{gc_async_immut,gc_sync_immut,nogc_sync_immut}/trie_facade_native_spec.spl`.
- Typed root-facade native BDD specs now pass for the same shared-prefix/overwrite behavior through `std.{gc_async_immut,gc_sync_immut,nogc_sync_immut}.{PersistentTrie}` via `test/unit/lib/{gc_async_immut,gc_sync_immut,nogc_sync_immut}/trie_root_facade_native_spec.spl`.
- Untyped chained root-facade native BDD specs now pass for `PersistentTrie.empty().set("app", 1).set("apple", 2)` through `std.{gc_async_immut,gc_sync_immut,nogc_sync_immut}.{PersistentTrie}` via `test/unit/lib/{gc_async_immut,gc_sync_immut,nogc_sync_immut}/trie_root_facade_native_spec.spl`.
- Native BDD specs now pass for branch-shaped `PersistentMap.empty().set("app", 1).set("apple", 2)`, branch-shaped map overwrite, branch-shaped map removal, `PersistentSet.empty().add("app").add("apple")`, set dedupe, and branch-shaped set removal through the GC async, GC sync immutable, and no-GC sync immutable facades. The map overwrite/removal closure required replacing internal HAMT/collision length-driven array scans with iterator scans so broad root facades cannot route array length calls through `PersistentList.len` in native dispatch; set dedupe/removal then passes because `PersistentSet` is backed by `PersistentMap`.
- Direct small-hash HAMT branch overwrite BDD probes pass; the root-facade trie chain now also passes after the committed HAMT/collision dispatch closure.

## Next Steps

1. Keep the tracked map/set/trie facade specs in the native smoke set when changing immutable facades.
2. Clear remaining native type-loader/minimal-runtime-stub warnings before promoting the immutable facade families from advanced-scoped to public.
