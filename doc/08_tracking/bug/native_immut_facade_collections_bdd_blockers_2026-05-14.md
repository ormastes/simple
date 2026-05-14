# Native Immutable Facade Collection BDD Blockers

Status: open
Date: 2026-05-14

## Impact

The `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut` facade families have native BDD coverage for root immutable map/set one-entry and two-entry committed paths. Broader public promotion remains blocked for map/set branch overwrite/removal, set dedupe/removal, and trie mutation/lookup because reduced native BDD specs fail or time out before producing assertion detail.

## Evidence

- Plain native `run` completes reduced HAMT remove and trie shared-prefix/overwrite probes with expected printed values.
- Direct no-GC async trie-node native BDD coverage now passes for shared-prefix `trie_set`/`trie_get` via `test/unit/lib/nogc_async_immut/trie_node_native_spec.spl`.
- Interpreter `test/unit/lib/immut/persistent_trie_spec.spl` now passes all `82` examples against the pair-array trie backend, including `from_dict`.
- Native BDD `test` times out after 120 seconds on reduced HAMT branch overwrite/remove probes such as `gc_async_immut_map_remove_len_native_probe_spec.spl` and `gc_async_immut_hamt_two_key_overwrite_actual_hash_native_probe_spec.spl`.
- Native BDD `test` fails on trie construction through `PersistentTrie.empty().set("app", 1).set("apple", 2)` even when the assertion is only `expect(true).to_equal(true)`.
- Direct small-hash HAMT branch overwrite BDD probes pass, which points to an interaction between native BDD execution and the committed hash/trie paths rather than a full backend import failure.

## Next Steps

1. Reduce the native BDD harness failure to a committed `test/unit` regression that reports assertion or process status detail.
2. Isolate whether the timeout is in branch update/remove codegen, BDD wrapper generation, or runtime value comparison.
3. Promote map/set overwrite/removal, set dedupe/removal, and trie shared-prefix/overwrite specs only after the native BDD specs pass from tracked `test/unit/lib/...` paths.
