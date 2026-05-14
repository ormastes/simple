# Native Immutable Facade Collection BDD Blockers

Status: open
Date: 2026-05-14

## Impact

The `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut` facade families have native BDD coverage for root immutable map one-entry, two-entry, branch-shaped insert, branch-shaped overwrite, and branch-shaped removal committed paths; root immutable set one-entry, two-entry, branch-shaped insert, dedupe, and branch-shaped removal committed paths; package-level `persistent_trie` shared-prefix/overwrite paths; and typed root-facade `PersistentTrie` shared-prefix/overwrite paths. Broader public promotion remains blocked for untyped chained root-facade trie mutation because reduced native BDD specs fail or time out before producing assertion detail.

## Evidence

- Plain native `run` completes reduced HAMT remove and trie shared-prefix/overwrite probes with expected printed values.
- Direct no-GC async trie-node native BDD coverage now passes for shared-prefix `trie_set`/`trie_get` via `test/unit/lib/nogc_async_immut/trie_node_native_spec.spl`.
- Interpreter `test/unit/lib/immut/persistent_trie_spec.spl` now passes all `82` examples against the pair-array trie backend, including `from_dict`.
- Package-level native BDD specs now pass for `PersistentTrie.empty().set("app", 1).set("apple", 2)` and overwrite behavior through `std.{gc_async_immut,gc_sync_immut,nogc_sync_immut}.persistent_trie.{PersistentTrie}` via `test/unit/lib/{gc_async_immut,gc_sync_immut,nogc_sync_immut}/trie_facade_native_spec.spl`.
- Typed root-facade native BDD specs now pass for the same shared-prefix/overwrite behavior through `std.{gc_async_immut,gc_sync_immut,nogc_sync_immut}.{PersistentTrie}` via `test/unit/lib/{gc_async_immut,gc_sync_immut,nogc_sync_immut}/trie_root_facade_native_spec.spl`.
- Native BDD specs now pass for branch-shaped `PersistentMap.empty().set("app", 1).set("apple", 2)`, branch-shaped map overwrite, branch-shaped map removal, `PersistentSet.empty().add("app").add("apple")`, set dedupe, and branch-shaped set removal through the GC async, GC sync immutable, and no-GC sync immutable facades. The map overwrite/removal closure required replacing internal HAMT/collision length-driven array scans with iterator scans so broad root facades cannot route array length calls through `PersistentList.len` in native dispatch; set dedupe/removal then passes because `PersistentSet` is backed by `PersistentMap`.
- Native BDD `test` still fails on untyped chained root-facade trie mutation through `use std.gc_async_immut.{PersistentTrie}` and `PersistentTrie.empty().set("app", 1).set("apple", 2)`. Reduced probes show broad root import and `PersistentTrie.empty()` pass, and `val base: PersistentTrie = PersistentTrie.empty()` followed by typed `set` receivers passes. The latest failing GDB backtrace for `tmp/root_trie_set_probe_spec.spl` enters `rt_native_eq`, then `nogc_async_immut.persistent_map.hamt_node.hamt_set`, then `PersistentMap.set`, before reaching trie frames. This points to native root-facade method dispatch ambiguity when several imported classes expose `set`.
- Direct small-hash HAMT branch overwrite BDD probes pass, which points to an interaction between native BDD execution and the committed hash/trie paths rather than a full backend import failure.

## Next Steps

1. Reduce the native BDD harness failure to a committed `test/unit` regression that reports assertion or process status detail.
2. Isolate whether the timeout is in branch update/remove codegen, BDD wrapper generation, or runtime value comparison.
3. Promote untyped root-facade trie chain specs only after the native BDD specs pass from tracked `test/unit/lib/...` paths.
