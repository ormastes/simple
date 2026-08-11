# `pure.collections.group_by` silently drops every member after the first

**Date:** 2026-07-31
**Component:** `src/lib/gc_async_mut/pure/collections.spl:73` (`group_by`)
**Severity:** silent wrong results — correct group count, wrong contents
**Status:** fixed

## Fix

Rewritten with two parallel locals — `var keys: [K]` and `var members: [[T]]` —
because an array-of-arrays IS mutable through index (`members[j].push(item)`
reaches the stored bucket), unlike a tuple field. The existing linear scan over
`keys` finds the slot; keys and members are zipped into `[(K, [T])]` at the end.
Linear per insert — no bucket copy-back, so no O(n²)-within-a-group trade-off.
Contract preserved: groups in first-encounter key order, members in input order.
Spec now asserts full membership (`[(1, [1, 3]), (0, [2, 4, 6])]` and
`[(0, [2, 8, 4])]`): 10 examples, 0 failures. The O(n * distinct_keys) slot scan
remains, marked with a `# ponytail:` note naming dict-slot lookup as the
upgrade path.

## Symptom

Every group contains only the element that created it. The group *count* and
key *order* are correct, which is what makes this hard to notice.

```
group_by([1, 2, 4, 3, 6], parity)
  expected  [(1, [1, 3]), (0, [2, 4, 6])]
  actual    [(1, [1]),    (0, [2])]

group_by([2, 8, 4], parity)
  expected  [(0, [2, 8, 4])]
  actual    [(0, [2])]
```

## Cause

```
groups[j].1.push(item)
```

Indexing to reach a **tuple field** yields a copy, so `.push` mutates the copy
and it is discarded — the write never reaches `groups`. No error, no warning.

This is one instance of a wider class, probed and audited separately in
`doc/08_tracking/bug/mutate_through_index_loses_write_2026-07-31.md`. The rule is
narrower than "arrays are value types": `b[0].push(x)` on a `[[i64]]` **works**;
it is dict values and tuple/struct fields that lose the write. Six sites in
`src/lib` share the defect, including `dependency_tracker/graph.spl:54`, where
every graph node keeps only its first edge.

## Evidence that it is pre-existing

Found while replacing the function's O(n * distinct_keys) inner scan with a
`Dict<K, i64>` slot lookup. The rewrite failed two examples, so the original
body was restored and the **same spec re-run against the unmodified function**:

```
✗ orders groups by first encounter of their key   expected [2] to equal [2, 4, 6]
✗ keeps members in input order within a group     expected [2] to equal [2, 8, 4]
```

Byte-identical failures. The defect predates any change made today; swapping in
the dict preserved it exactly, because the dict replaced the *lookup*, not the
push.

## Why it is not fixed here

The obvious repair — read the bucket, push, write it back —

```
var bucket = members[idx]
bucket.push(item)
members[idx] = bucket
```

is correct but copies the bucket on every insert, making membership O(n²)
*within* a group. That trades a silent correctness bug for a performance one and
deserves its own design pass. Linear options worth weighing:

- flat member array plus per-group offsets, built by counting then placing
  (needs a pre-sized array, so needs a default `T` or an index-based variant);
- return `[(K, [i64])]` of **indices** and let the caller project;
- a mutable-bucket type that is not copied on element access.

## Scope

`unique` in the same file had the same O(n²) shape and **was** fixed (dict
membership, verified 5/5) — it needed no nested mutation, only a flat `result`.

Anything relying on `group_by` for members rather than keys is silently wrong
today. Audit before the fix lands.

## Related

- `.claude/memory/feedback_arrays_value_types.md` — arrays are passed by copy
- `doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md`
  §8.3 (grouped hash join) and Wave 2 STD-UNIQ in the parallel plan
