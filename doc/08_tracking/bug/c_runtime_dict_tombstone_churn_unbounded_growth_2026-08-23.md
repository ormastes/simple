# C runtime: a delete-heavy dict grows its table forever (tombstones drive the doubling)

**Date:** 2026-08-23
**Area:** `src/runtime/runtime_native.c` — `rt_core_dict_put` resize branch
**Status:** FIXED (runtime-only, no `rt_*` ABI change, no layout change)
**Found by:** the runtime perf lane, while auditing the `rt_*` collection
families for the cost class filed in
`c_runtime_string_concat_quadratic_2026-08-22.md`. That record's audit checked
`keys()`/`values()`/`rt_for_iterable` and `rt_dict_set` on the INSERT path and
found them correct; it did not exercise the DELETE path, which is where this
lives.

## The defect

`rt_core_dict_put` resized with a single unconditional rule:

```c
if ((d->len + d->tombstones + 1) * 10 > d->cap * 7) {
    rt_core_dict_resize(d, d->cap * 2);   /* doubling was the ONLY option */
}
```

Counting tombstones against the load factor is correct — a tombstone lengthens
a probe chain exactly as a live entry does. Doubling as the only response is
not. `rt_core_dict_del` converts a live entry to a tombstone (`occupied = -1`),
so the loop

```
d[k] = v
d.remove(k)
```

drives the load factor to 70% with **tombstones alone** while `len` stays at 0
or 1. Every crossing doubles the table and clears the tombstones, so capacity
tracks the number of CHURN OPERATIONS rather than the number of live entries,
and never comes back down. A dict that is empty at rest ends up holding tens of
megabytes.

This is exactly the failure mode `rt_core_register_immortal_ptr` already
documents and guards against for the immortal-pointer table
(`runtime_native.c:1477`, "A transient teardown can leave millions of tombstones
while very few live objects remain"). The dict simply never got the same guard.

## Measured (before)

C harness linked against `build/simple-core/libsimple_runtime.a`, N insert+delete
pairs on one dict, live count 0 throughout:

| N churn pairs | wall | peak RSS |
|---|---|---|
| 100,000 | 0.016 s | 4.2 MB |
| 400,000 | 0.122 s | 10.4 MB |
| 1,600,000 | 0.625 s | 34.9 MB |

4x the churn → ~3.4x the footprint: linear growth for a dict with zero entries.

## The fix

Rehash **in place at the same capacity** when tombstones outnumber live entries
and the live set is sparse — the identical guard and thresholds the immortal
registry uses. `rt_core_dict_resize`'s rehash loop already drops tombstones, so
a same-capacity resize costs the same O(cap) walk it would have cost while
doubling; it just does not hand the memory away permanently.

```c
int64_t next_cap = d->cap * 2;
if (d->cap > RT_CORE_DICT_INIT_CAP &&
    d->tombstones > d->len &&
    (d->len + 1) * 10 < d->cap * 5) {
    next_cap = d->cap;
}
rt_core_dict_resize(d, next_cap);
```

Semantics are untouched: same keys, same values, same iteration contract, same
`rt_*` signatures. A dict that genuinely holds n entries has `len >= tombstones`
at the crossing and still doubles exactly as before.

## Measured (after)

| N churn pairs | wall | peak RSS |
|---|---|---|
| 100,000 | 0.009 s | 2.1 MB |
| 400,000 | 0.025 s | 2.1 MB |
| 1,600,000 | 0.119 s | 2.1 MB |
| 6,400,000 | 0.407 s | 2.1 MB |

Footprint flat across a 64x range; wall time linear and ~5x faster at 1.6M
(the doubling was also paying `calloc` + full-table rehash on ever-larger
tables).

## Test pinning the mechanism

`src/runtime/test/rt_dict_tombstone_churn_growth_selfcheck.c` — a growth-ratio
assertion, not a wall-clock threshold: 4x the churn must not grow the peak
footprint by more than 4 MB (pre-fix it grew by 32.8 MB). It also asserts the
inverse, that a dict genuinely holding 50,000 entries still grows and still
reads back correctly, so the guard cannot be "satisfied" by refusing to resize;
and that a 16-key resident set survives 400,000 in-place rehashes intact.

Verified failing pre-fix and passing post-fix:

```
PRE-FIX:  FAIL: 4x churn grew peak footprint by 32772 kB   rc=1
POST-FIX: PASS (400k churn +256 kB, 1.6M churn +256 kB, delta 0 kB)   rc=0
```

Pinned in `scripts/check/check-perf-regression-tests.shs` by two rows: the
same-cap rehash branch in `runtime_native.c`, and the selfcheck's presence.

## Not changed here (still open, unchanged scope)

`rt_string_concat` remains a fresh `malloc` + two `memcpy` per call. The
2026-08-22 design stop in `c_runtime_string_concat_quadratic_2026-08-22.md`
stands and was re-read, not re-litigated: `RtCoreString` carries no refcount,
strings are registered immortal and aliased by pointer, so no runtime-only
sole-owner fast path is sound. That fix is a MIR lowering feature
(`rt_string_append_owned` with an escape check, or builder-loop lowering) and
belongs to a lane that may edit lowering.
