# COW-alias ratchet was blind to `src/lib` — 211 unseen offenders

- **Date:** 2026-08-23
- **Class:** performance / memory-efficiency (COW-alias antipattern, `.claude/rules/code-style.md`)
- **Status:** FIXED (scanner scope) + 3 hot-path functions fixed (21 offender rows); remaining 198 frozen in baseline
- **Related:** `doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md`

## Defect

`scripts/check/check-cow-alias-hotpath.shs` hardcoded `SRC="$ROOT/src/compiler"`
(line 299 pre-fix) and scanned **only** the compiler tree — 1,567 files. The
standard library, `src/lib`, is **7,864 `.spl` files** and was never scanned at
all. The ratchet therefore reported `PASS — ... 7 offender(s)` while the tree
actually carried **219**.

This is not a coverage nicety. A ratchet exists to stop a defect class from
growing; a ratchet with 83% of the source tree outside its scope does not stop
anything there, and nobody could tell from its verdict line that it wasn't
looking.

Measured (authoritative scanner, run with `--root` pointed at a hardlinked
`src/lib`, 2026-08-23):

```
FAIL — 7864 file(s) scanned, 212 offender(s), 212 new, 0 stale
```

vs. the compiler-only baseline of 7.

## Hot-path offender fixed

Three functions in `src/lib/common/js/engine/vm_object_store.spl` —
`set_property`, `set_reference_property`, `remove_property` — used the
canonical ROUNDTRIP shape across **seven** parallel arrays:

```
var prop_obj_ids = self.prop_obj_ids     # alias: strong_count 2
...                                       # x7
prop_obj_ids.push(obj_id)                 # Arc::make_mut deep-copies the WHOLE array
...
self.prop_obj_ids = prop_obj_ids
```

The JS VM's object store is a global append-only property log, so
`prop_obj_ids` is the size of every property of every live object in the heap.
Each call therefore deep-copied **seven whole-heap-sized arrays** on the append
path, and three on the in-place-update path (the indexed writes
`prop_values[i] = v` go through the alias, so each one is itself a whole-array
copy). `set_property` is the hottest path in the VM — every JS property write
and every array element store lands there, including the `set_property` loop
inside `create_array_from` — so the cost is O(P) per property write and O(P²)
to build an object or array. Fixed by
mutating through the single owner (`self.prop_obj_ids.push(...)`), which is
exactly semantics-preserving: no other live binding observes the field between
the alias and the store-back, so the copy was never serving value semantics.

Offender rows removed by this fix: 21 (7 arrays x 3 functions).

## Fix

1. `scan()` takes an optional path prefix; the driver calls it twice, over
   `src/compiler` (unprefixed, so the existing 7 baseline rows stay valid) and
   `src/lib` (prefixed `lib/`, so a lib path can never collide with a
   compiler-relative path of the same name). Both trees are fail-closed: 0
   files under **either** is `ERROR`, never a pass.
2. Baseline regenerated (reviewed): `PASS — 9674 file(s) scanned, baseline
   regenerated with 198 offender(s)` — 7 compiler rows + 191 lib rows. The
   compiler-only ratchet's verdict had been `7`.
3. Selftest gains a 9th fixture asserting the prefixed scan emits
   `lib/`-prefixed rows — without it, deleting the second `scan()` call would
   silently restore the blind spot and every fixture would still pass.

## NOT fixed here — filed as a design issue

`vm_object_store` looks a property up by scanning the whole append-only log
backwards (`get_property`, `set_property`, `remove_property`): O(P) per
property access, and the key-enumeration paths nest a `seen_keys` linear scan
inside that loop for O(P²). That is the store's *design*, not a local defect,
so per the standing constraint it is recorded rather than rewritten. A fix
needs a per-object key->slot index, which changes the store's data model.
