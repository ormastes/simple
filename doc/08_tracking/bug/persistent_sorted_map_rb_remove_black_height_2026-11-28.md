# PersistentSortedMap.remove rebuilds an all-black tree (black-height violated)

- **Status:** OPEN (pre-existing, not introduced by S8-K)
- **Component:** `src/lib/nogc_async_immut/persistent_sorted_map/path_copy.spl`
  (`rb_remove` -> `rb_build_from_sorted`)

## Symptom

`rb_remove` collects the remaining entries and rebuilds with
`rb_build_from_sorted`, which colors every node BLACK. A median-split tree of
n nodes is only perfectly balanced when n+1 is a power of two; otherwise the
deepest level makes paths differ in black count, so the red-black black-height
invariant is violated after a remove. Lookups stay correct; later inserts rely
on LLRB fix-up that assumes the invariant.

## Why not fixed here

Coloring the deepest partial level red is not enough: LLRB also requires red
links to lean left, and a median-split deepest level can hang a red right
child. A correct fix is either a true LLRB delete (move-red-left/right) or a
builder that places the partial level on left children only.
