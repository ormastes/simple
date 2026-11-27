# Persistent collections: typed nodes are slower on the seed interpreter

- **Status:** OPEN (owner accepted landing; revisit after S3-D monomorphisation)
- **Component:** `src/lib/nogc_async_immut/persistent_{map,vec,trie,sorted_map,list}`
- **Found:** 2026-11-28, S8-K struct/enum node conversion review

## Symptom

Replacing heterogeneous node arrays with `RbNode<K,V>` / `HamtNode<K,V>` /
`RrbNode<T>` / `TrieNode<V>` / `ConsCell<T>` is slower on the seed interpreter
(`simple-local-20261128a`). Spec pass counts are unchanged.

| workload | before | after |
|---|---|---|
| PersistentMap 12k set+get | 74s | 146s |
| PersistentMap 6k set+get | baseline | +45% |
| PersistentTrie / PersistentSortedMap | baseline | about +20% |
| peak memory | baseline | +20-25% |

The slowdown is in the get path and grows with n. Cause is not identified
(candidates: enum/struct match dispatch, struct field access on generic
instances, deep structural `==` on nodes).

## Next step

Profile `hamt_get` after S3-D monomorphisation lands; compare against the
array-node baseline on the same binary.
