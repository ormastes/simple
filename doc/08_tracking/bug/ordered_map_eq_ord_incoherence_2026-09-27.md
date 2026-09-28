# OrderedMap Eq/Ord disagreement can delete the wrong key (2026-09-27)

Status: source guard present; native integer-key path still fails and needs repair.

The generic AVL `OrderedMap<K,V>` previously searched with `==` and `<`, but deletion used `<` and `>` and treated the remaining case as equality. If a key type reports neither `<` nor `>` while `==` is false, deletion could remove the visited node rather than the requested key. The map could also admit two keys in one ordering equivalence class.

The map now checks lookup, insertion, and deletion comparisons for agreement between `Eq` and `Ord` on each compared pair. It panics with an explicit key-order diagnostic for equal-and-ordered, mutually ordered, or incomparable-but-unequal pairs. Existing integer/text rotation and removal specs describe the ordinary path but have not run on an admitted runner; an inconsistent custom-key or NaN-key failure test and interpreter/native execution remain required. This dynamic check cannot prove global comparator coherence for pairs that are never compared. Generic trait-bound enforcement at instantiation remains a separate gate under REQ-PSC-002/-007.

The original generic `self.compare_key(K,K)` method made `contains_key(7)` false immediately after an integer-key insertion, even though direct equality on the stored key was true. Moving `K` comparisons into each map operation fixed that lookup, but the subsequent exact-source native probe panicked with the Eq/Ord diagnostic during replacement or later insertion of coherent `i64` keys. Treat this as an unresolved native generic comparison/materialization defect, not proof that the supplied key violates the contract. See [the native probe](ordered_map_native_contains_key_after_insert_2026-09-27.md).
