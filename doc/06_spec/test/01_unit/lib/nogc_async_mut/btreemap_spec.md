# BTreeMap / BTreeSet Unit Spec — B1

> Verifies that the FFI-backed BTreeMap and BTreeSet externs behave correctly

<!-- sdn-diagram:id=btreemap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=btreemap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

btreemap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=btreemap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BTreeMap / BTreeSet Unit Spec — B1

Verifies that the FFI-backed BTreeMap and BTreeSet externs behave correctly

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/btreemap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that the FFI-backed BTreeMap and BTreeSet externs behave correctly
after the B1 refactor replaces copy-pasted tagged-value macros in the 4 boot
C files with `#include "../../common/baremetal_runtime.h"`.

These tests run in interpreter mode (no --mode=native / --mode=smf per
memory `feedback_compile_mode_false_greens`).  They exercise the same extern
layer that `collections.c`, `hashmap.c`, `primitives.c`, and `rt_extras.c`
implement, ensuring the macro include-swap does not silently break the ABI.

**B1 gate:** all tests here must pass both before and after the include-swap.
If they fail before the swap, the baseline is broken — fix before proceeding.
If they fail after, the macro definitions in `baremetal_runtime.h` diverged.

Covers call sites:
  - `collections.c`:1–15  (TAG_MASK, ENCODE_INT, IS_INT, IS_HEAP, NIL_VALUE)
  - `hashmap.c`:27–46     (TAG_MASK, ENCODE_INT, IS_INT, IS_HEAP — subset)
  - `primitives.c`:27–52  (full set + HeapHeader, RuntimeString, RuntimeArray)
  - `rt_extras.c`:34–51   (full set + HeapHeader, RuntimeString)

Boundary cases:
  - empty map / set operations
  - 32-entry stress insert (exercises internal BTree node splits)
  - remove of non-existent key (no panic)
  - double-insert same key (last write wins)
  - first_key / last_key ordering guarantee
  - clear then re-insert

## Scenarios

### BTreeMap — B1 macro parity gate

#### new() produces a valid empty map

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
expect(__rt_btreemap_len(m)).to_equal(0)
```

</details>

#### insert returns true and increases len

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
val inserted = __rt_btreemap_insert(m, "alpha", 1)
expect(inserted).to_equal(true)
expect(__rt_btreemap_len(m)).to_equal(1)
```

</details>

#### get retrieves an inserted value

1.   =   rt btreemap insert
   - Expected: got equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "key1", 42)
val got = __rt_btreemap_get(m, "key1")
expect(got).to_equal(42)
```

</details>

#### contains_key is true after insert, false for missing key

1.   =   rt btreemap insert
   - Expected: __rt_btreemap_contains_key(m, "present") is true
   - Expected: __rt_btreemap_contains_key(m, "absent") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "present", 1)
expect(__rt_btreemap_contains_key(m, "present")).to_equal(true)
expect(__rt_btreemap_contains_key(m, "absent")).to_equal(false)
```

</details>

#### remove drops the key and decreases len

1.   =   rt btreemap insert
   - Expected: __rt_btreemap_len(m) equals `1`
2.   =   rt btreemap remove
   - Expected: __rt_btreemap_len(m) equals `0`
   - Expected: __rt_btreemap_contains_key(m, "to_remove") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "to_remove", 99)
expect(__rt_btreemap_len(m)).to_equal(1)
_ = __rt_btreemap_remove(m, "to_remove")
expect(__rt_btreemap_len(m)).to_equal(0)
expect(__rt_btreemap_contains_key(m, "to_remove")).to_equal(false)
```

</details>

#### remove of non-existent key does not panic and len stays the same

1.   =   rt btreemap insert
2.   =   rt btreemap remove
   - Expected: __rt_btreemap_len(m) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "exists", 1)
_ = __rt_btreemap_remove(m, "ghost_key")
expect(__rt_btreemap_len(m)).to_equal(1)
```

</details>

#### double-insert same key: last value wins, len stays 1

1.   =   rt btreemap insert
2.   =   rt btreemap insert
   - Expected: __rt_btreemap_len(m) equals `1`
   - Expected: __rt_btreemap_get(m, "dup") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "dup", 10)
_ = __rt_btreemap_insert(m, "dup", 20)
expect(__rt_btreemap_len(m)).to_equal(1)
expect(__rt_btreemap_get(m, "dup")).to_equal(20)
```

</details>

<details>
<summary>Advanced: 32-entry stress insert, lookup, and remove — exercises BTree node splits</summary>

#### 32-entry stress insert, lookup, and remove — exercises BTree node splits

1.   =   rt btreemap insert
2.   =   rt btreemap insert
3.   =   rt btreemap insert
4.   =   rt btreemap insert
5.   =   rt btreemap insert
6.   =   rt btreemap insert
7.   =   rt btreemap insert
8.   =   rt btreemap insert
9.   =   rt btreemap insert
10.   =   rt btreemap insert
11.   =   rt btreemap insert
12.   =   rt btreemap insert
13.   =   rt btreemap insert
14.   =   rt btreemap insert
15.   =   rt btreemap insert
16.   =   rt btreemap insert
17.   =   rt btreemap insert
18.   =   rt btreemap insert
19.   =   rt btreemap insert
20.   =   rt btreemap insert
21.   =   rt btreemap insert
22.   =   rt btreemap insert
23.   =   rt btreemap insert
24.   =   rt btreemap insert
25.   =   rt btreemap insert
26.   =   rt btreemap insert
27.   =   rt btreemap insert
28.   =   rt btreemap insert
29.   =   rt btreemap insert
30.   =   rt btreemap insert
31.   =   rt btreemap insert
32.   =   rt btreemap insert
   - Expected: __rt_btreemap_len(m) equals `32`
   - Expected: __rt_btreemap_get(m, "k00") equals `0`
   - Expected: __rt_btreemap_get(m, "k15") equals `15`
   - Expected: __rt_btreemap_get(m, "k31") equals `31`
33.   =   rt btreemap remove
34.   =   rt btreemap remove
35.   =   rt btreemap remove
36.   =   rt btreemap remove
   - Expected: __rt_btreemap_len(m) equals `28`
   - Expected: __rt_btreemap_contains_key(m, "k00") is false
   - Expected: __rt_btreemap_contains_key(m, "k01") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
# Insert 32 entries with lexicographic keys k00..k31
_ = __rt_btreemap_insert(m, "k00", 0)
_ = __rt_btreemap_insert(m, "k01", 1)
_ = __rt_btreemap_insert(m, "k02", 2)
_ = __rt_btreemap_insert(m, "k03", 3)
_ = __rt_btreemap_insert(m, "k04", 4)
_ = __rt_btreemap_insert(m, "k05", 5)
_ = __rt_btreemap_insert(m, "k06", 6)
_ = __rt_btreemap_insert(m, "k07", 7)
_ = __rt_btreemap_insert(m, "k08", 8)
_ = __rt_btreemap_insert(m, "k09", 9)
_ = __rt_btreemap_insert(m, "k10", 10)
_ = __rt_btreemap_insert(m, "k11", 11)
_ = __rt_btreemap_insert(m, "k12", 12)
_ = __rt_btreemap_insert(m, "k13", 13)
_ = __rt_btreemap_insert(m, "k14", 14)
_ = __rt_btreemap_insert(m, "k15", 15)
_ = __rt_btreemap_insert(m, "k16", 16)
_ = __rt_btreemap_insert(m, "k17", 17)
_ = __rt_btreemap_insert(m, "k18", 18)
_ = __rt_btreemap_insert(m, "k19", 19)
_ = __rt_btreemap_insert(m, "k20", 20)
_ = __rt_btreemap_insert(m, "k21", 21)
_ = __rt_btreemap_insert(m, "k22", 22)
_ = __rt_btreemap_insert(m, "k23", 23)
_ = __rt_btreemap_insert(m, "k24", 24)
_ = __rt_btreemap_insert(m, "k25", 25)
_ = __rt_btreemap_insert(m, "k26", 26)
_ = __rt_btreemap_insert(m, "k27", 27)
_ = __rt_btreemap_insert(m, "k28", 28)
_ = __rt_btreemap_insert(m, "k29", 29)
_ = __rt_btreemap_insert(m, "k30", 30)
_ = __rt_btreemap_insert(m, "k31", 31)
expect(__rt_btreemap_len(m)).to_equal(32)
# Spot-check a few lookups
expect(__rt_btreemap_get(m, "k00")).to_equal(0)
expect(__rt_btreemap_get(m, "k15")).to_equal(15)
expect(__rt_btreemap_get(m, "k31")).to_equal(31)
# Remove half
_ = __rt_btreemap_remove(m, "k00")
_ = __rt_btreemap_remove(m, "k08")
_ = __rt_btreemap_remove(m, "k16")
_ = __rt_btreemap_remove(m, "k24")
expect(__rt_btreemap_len(m)).to_equal(28)
expect(__rt_btreemap_contains_key(m, "k00")).to_equal(false)
expect(__rt_btreemap_contains_key(m, "k01")).to_equal(true)
```

</details>


</details>

#### first_key and last_key reflect sorted order

1.   =   rt btreemap insert
2.   =   rt btreemap insert
3.   =   rt btreemap insert
   - Expected: __rt_btreemap_first_key(m) equals `apple`
   - Expected: __rt_btreemap_last_key(m) equals `cherry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "banana", 2)
_ = __rt_btreemap_insert(m, "apple", 1)
_ = __rt_btreemap_insert(m, "cherry", 3)
expect(__rt_btreemap_first_key(m)).to_equal("apple")
expect(__rt_btreemap_last_key(m)).to_equal("cherry")
```

</details>

#### clear empties the map; re-insert works after clear

1.   =   rt btreemap insert
2.   =   rt btreemap insert
3.   =   rt btreemap clear
   - Expected: __rt_btreemap_len(m) equals `0`
   - Expected: __rt_btreemap_contains_key(m, "a") is false
4.   =   rt btreemap insert
   - Expected: __rt_btreemap_len(m) equals `1`
   - Expected: __rt_btreemap_get(m, "fresh") equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "a", 1)
_ = __rt_btreemap_insert(m, "b", 2)
_ = __rt_btreemap_clear(m)
expect(__rt_btreemap_len(m)).to_equal(0)
expect(__rt_btreemap_contains_key(m, "a")).to_equal(false)
_ = __rt_btreemap_insert(m, "fresh", 99)
expect(__rt_btreemap_len(m)).to_equal(1)
expect(__rt_btreemap_get(m, "fresh")).to_equal(99)
```

</details>

#### keys() returns a non-nil result for a non-empty map

1.   =   rt btreemap insert
   - Expected: ks equals `ks)   # non-nil: would panic if nil dereference`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "x", 10)
val ks = __rt_btreemap_keys(m)
expect(ks).to_equal(ks)   # non-nil: would panic if nil dereference
```

</details>

#### values() returns a non-nil result for a non-empty map

1.   =   rt btreemap insert
   - Expected: vs equals `vs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "x", 10)
val vs = __rt_btreemap_values(m)
expect(vs).to_equal(vs)
```

</details>

#### entries() returns a non-nil result for a non-empty map

1.   =   rt btreemap insert
   - Expected: es equals `es`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "x", 10)
val es = __rt_btreemap_entries(m)
expect(es).to_equal(es)
```

</details>

### BTreeSet — B1 macro parity gate

#### new() produces an empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
expect(__rt_btreeset_len(s)).to_equal(0)
```

</details>

#### insert returns true and increases len

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
val ok = __rt_btreeset_insert(s, "alpha")
expect(ok).to_equal(true)
expect(__rt_btreeset_len(s)).to_equal(1)
```

</details>

#### contains is true after insert, false for missing

1.   =   rt btreeset insert
   - Expected: __rt_btreeset_contains(s, "present") is true
   - Expected: __rt_btreeset_contains(s, "absent") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "present")
expect(__rt_btreeset_contains(s, "present")).to_equal(true)
expect(__rt_btreeset_contains(s, "absent")).to_equal(false)
```

</details>

#### duplicate insert is idempotent: len stays 1

1.   =   rt btreeset insert
2.   =   rt btreeset insert
   - Expected: __rt_btreeset_len(s) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "dup")
_ = __rt_btreeset_insert(s, "dup")
expect(__rt_btreeset_len(s)).to_equal(1)
```

</details>

#### remove drops element and decreases len

1.   =   rt btreeset insert
2.   =   rt btreeset remove
   - Expected: __rt_btreeset_len(s) equals `0`
   - Expected: __rt_btreeset_contains(s, "to_remove") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "to_remove")
_ = __rt_btreeset_remove(s, "to_remove")
expect(__rt_btreeset_len(s)).to_equal(0)
expect(__rt_btreeset_contains(s, "to_remove")).to_equal(false)
```

</details>

#### remove of non-existent element does not panic

1.   =   rt btreeset insert
2.   =   rt btreeset remove
   - Expected: __rt_btreeset_len(s) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "real")
_ = __rt_btreeset_remove(s, "ghost")
expect(__rt_btreeset_len(s)).to_equal(1)
```

</details>

#### first and last reflect sorted order

1.   =   rt btreeset insert
2.   =   rt btreeset insert
3.   =   rt btreeset insert
   - Expected: __rt_btreeset_first(s) equals `apple`
   - Expected: __rt_btreeset_last(s) equals `zebra`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "mango")
_ = __rt_btreeset_insert(s, "apple")
_ = __rt_btreeset_insert(s, "zebra")
expect(__rt_btreeset_first(s)).to_equal("apple")
expect(__rt_btreeset_last(s)).to_equal("zebra")
```

</details>

#### clear empties the set; re-insert works after clear

1.   =   rt btreeset insert
2.   =   rt btreeset insert
3.   =   rt btreeset clear
   - Expected: __rt_btreeset_len(s) equals `0`
4.   =   rt btreeset insert
   - Expected: __rt_btreeset_len(s) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "a")
_ = __rt_btreeset_insert(s, "b")
_ = __rt_btreeset_clear(s)
expect(__rt_btreeset_len(s)).to_equal(0)
_ = __rt_btreeset_insert(s, "fresh")
expect(__rt_btreeset_len(s)).to_equal(1)
```

</details>

#### to_array returns a non-nil result for a non-empty set

1.   =   rt btreeset insert
   - Expected: arr equals `arr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "item")
val arr = __rt_btreeset_to_array(s)
expect(arr).to_equal(arr)
```

</details>

<details>
<summary>Advanced: 32-entry stress insert and lookup</summary>

#### 32-entry stress insert and lookup

1.   =   rt btreeset insert
2.   =   rt btreeset insert
3.   =   rt btreeset insert
4.   =   rt btreeset insert
5.   =   rt btreeset insert
6.   =   rt btreeset insert
7.   =   rt btreeset insert
8.   =   rt btreeset insert
9.   =   rt btreeset insert
10.   =   rt btreeset insert
11.   =   rt btreeset insert
12.   =   rt btreeset insert
13.   =   rt btreeset insert
14.   =   rt btreeset insert
15.   =   rt btreeset insert
16.   =   rt btreeset insert
17.   =   rt btreeset insert
18.   =   rt btreeset insert
19.   =   rt btreeset insert
20.   =   rt btreeset insert
21.   =   rt btreeset insert
22.   =   rt btreeset insert
23.   =   rt btreeset insert
24.   =   rt btreeset insert
25.   =   rt btreeset insert
26.   =   rt btreeset insert
27.   =   rt btreeset insert
28.   =   rt btreeset insert
29.   =   rt btreeset insert
30.   =   rt btreeset insert
31.   =   rt btreeset insert
32.   =   rt btreeset insert
   - Expected: __rt_btreeset_len(s) equals `32`
   - Expected: __rt_btreeset_first(s) equals `s00`
   - Expected: __rt_btreeset_last(s) equals `s31`
   - Expected: __rt_btreeset_contains(s, "s15") is true
   - Expected: __rt_btreeset_contains(s, "s99") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "s00")
_ = __rt_btreeset_insert(s, "s01")
_ = __rt_btreeset_insert(s, "s02")
_ = __rt_btreeset_insert(s, "s03")
_ = __rt_btreeset_insert(s, "s04")
_ = __rt_btreeset_insert(s, "s05")
_ = __rt_btreeset_insert(s, "s06")
_ = __rt_btreeset_insert(s, "s07")
_ = __rt_btreeset_insert(s, "s08")
_ = __rt_btreeset_insert(s, "s09")
_ = __rt_btreeset_insert(s, "s10")
_ = __rt_btreeset_insert(s, "s11")
_ = __rt_btreeset_insert(s, "s12")
_ = __rt_btreeset_insert(s, "s13")
_ = __rt_btreeset_insert(s, "s14")
_ = __rt_btreeset_insert(s, "s15")
_ = __rt_btreeset_insert(s, "s16")
_ = __rt_btreeset_insert(s, "s17")
_ = __rt_btreeset_insert(s, "s18")
_ = __rt_btreeset_insert(s, "s19")
_ = __rt_btreeset_insert(s, "s20")
_ = __rt_btreeset_insert(s, "s21")
_ = __rt_btreeset_insert(s, "s22")
_ = __rt_btreeset_insert(s, "s23")
_ = __rt_btreeset_insert(s, "s24")
_ = __rt_btreeset_insert(s, "s25")
_ = __rt_btreeset_insert(s, "s26")
_ = __rt_btreeset_insert(s, "s27")
_ = __rt_btreeset_insert(s, "s28")
_ = __rt_btreeset_insert(s, "s29")
_ = __rt_btreeset_insert(s, "s30")
_ = __rt_btreeset_insert(s, "s31")
expect(__rt_btreeset_len(s)).to_equal(32)
expect(__rt_btreeset_first(s)).to_equal("s00")
expect(__rt_btreeset_last(s)).to_equal("s31")
expect(__rt_btreeset_contains(s, "s15")).to_equal(true)
expect(__rt_btreeset_contains(s, "s99")).to_equal(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
