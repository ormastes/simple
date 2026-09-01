# BTreeMap / BTreeSet Unit Spec — B1

> Purpose: Prove that BTreeMap — B1 macro parity gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BTreeMap / BTreeSet Unit Spec — B1

Purpose: Prove that BTreeMap — B1 macro parity gate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/btreemap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that BTreeMap — B1 macro parity gate.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### BTreeMap — B1 macro parity gate

#### new() produces a valid empty map

- new() produces a valid empty map
- Verify: new() produces a valid empty map
   - Expected: __rt_btreemap_len(m) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new() produces a valid empty map")
step("Verify: new() produces a valid empty map")
# @req: REQ-LIB-NOGC-ASYNC-MUT-001
val m = __rt_btreemap_new()
expect(__rt_btreemap_len(m)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### insert returns true and increases len

- insert returns true and increases len
- Verify: insert returns true and increases len
   - Expected: inserted is true
   - Expected: __rt_btreemap_len(m) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("insert returns true and increases len")
step("Verify: insert returns true and increases len")
val m = __rt_btreemap_new()
val inserted = __rt_btreemap_insert(m, "alpha", 1)
expect(inserted).to_equal(true)
expect(__rt_btreemap_len(m)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### get retrieves an inserted value

- get retrieves an inserted value
- Verify: get retrieves an inserted value
   - Expected: got equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get retrieves an inserted value")
step("Verify: get retrieves an inserted value")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "key1", 42)
val got = __rt_btreemap_get(m, "key1")
expect(got).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### contains_key is true after insert, false for missing key

- contains_key is true after insert, false for missing key
- Verify: contains_key is true after insert, false for missing key
   - Expected: __rt_btreemap_contains_key(m, "present") is true
   - Expected: __rt_btreemap_contains_key(m, "absent") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains_key is true after insert, false for missing key")
step("Verify: contains_key is true after insert, false for missing key")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "present", 1)
expect(__rt_btreemap_contains_key(m, "present")).to_equal(true)
expect(__rt_btreemap_contains_key(m, "absent")).to_equal(false)
```

</details>

#### remove drops the key and decreases len

- remove drops the key and decreases len
- Verify: remove drops the key and decreases len
   - Expected: __rt_btreemap_len(m) equals `1`
   - Expected: __rt_btreemap_len(m) equals `0`
   - Expected: __rt_btreemap_contains_key(m, "to_remove") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove drops the key and decreases len")
step("Verify: remove drops the key and decreases len")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "to_remove", 99)
expect(__rt_btreemap_len(m)).to_equal(1)  # oracle: 1 — named expected value from the requirement
_ = __rt_btreemap_remove(m, "to_remove")
expect(__rt_btreemap_len(m)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(__rt_btreemap_contains_key(m, "to_remove")).to_equal(false)
```

</details>

#### remove of non-existent key does not panic and len stays the same

- remove of non-existent key does not panic and len stays the same
- Verify: remove of non-existent key does not panic and len stays the same
   - Expected: __rt_btreemap_len(m) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove of non-existent key does not panic and len stays the same")
step("Verify: remove of non-existent key does not panic and len stays the same")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "exists", 1)
_ = __rt_btreemap_remove(m, "ghost_key")
expect(__rt_btreemap_len(m)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### double-insert same key: last value wins, len stays 1

- double-insert same key: last value wins, len stays 1
- Verify: double-insert same key: last value wins, len stays 1
   - Expected: __rt_btreemap_len(m) equals `1`
   - Expected: __rt_btreemap_get(m, "dup") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("double-insert same key: last value wins, len stays 1")
step("Verify: double-insert same key: last value wins, len stays 1")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "dup", 10)
_ = __rt_btreemap_insert(m, "dup", 20)
expect(__rt_btreemap_len(m)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(__rt_btreemap_get(m, "dup")).to_equal(20)
```

</details>

<details>
<summary>Advanced: 32-entry stress insert, lookup, and remove — exercises BTree node splits</summary>

#### 32-entry stress insert, lookup, and remove — exercises BTree node splits

- 32-entry stress insert, lookup, and remove — exercises BTree node splits
- Verify: 32-entry stress insert, lookup, and remove — exercises BTree node splits
   - Expected: __rt_btreemap_len(m) equals `32`
   - Expected: __rt_btreemap_get(m, "k00") equals `0`
   - Expected: __rt_btreemap_get(m, "k15") equals `15`
   - Expected: __rt_btreemap_get(m, "k31") equals `31`
   - Expected: __rt_btreemap_len(m) equals `28`
   - Expected: __rt_btreemap_contains_key(m, "k00") is false
   - Expected: __rt_btreemap_contains_key(m, "k01") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("32-entry stress insert, lookup, and remove — exercises BTree node splits")
step("Verify: 32-entry stress insert, lookup, and remove — exercises BTree node splits")
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
expect(__rt_btreemap_len(m)).to_equal(32)  # oracle: 32 — named expected value from the requirement
# Spot-check a few lookups
expect(__rt_btreemap_get(m, "k00")).to_equal(0)
expect(__rt_btreemap_get(m, "k15")).to_equal(15)
expect(__rt_btreemap_get(m, "k31")).to_equal(31)
# Remove half
_ = __rt_btreemap_remove(m, "k00")
_ = __rt_btreemap_remove(m, "k08")
_ = __rt_btreemap_remove(m, "k16")
_ = __rt_btreemap_remove(m, "k24")
expect(__rt_btreemap_len(m)).to_equal(28)  # oracle: 28 — named expected value from the requirement
expect(__rt_btreemap_contains_key(m, "k00")).to_equal(false)
expect(__rt_btreemap_contains_key(m, "k01")).to_equal(true)
```

</details>


</details>

#### first_key and last_key reflect sorted order

- first_key and last_key reflect sorted order
- Verify: first_key and last_key reflect sorted order
   - Expected: __rt_btreemap_first_key(m) equals `apple`
   - Expected: __rt_btreemap_last_key(m) equals `cherry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first_key and last_key reflect sorted order")
step("Verify: first_key and last_key reflect sorted order")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "banana", 2)
_ = __rt_btreemap_insert(m, "apple", 1)
_ = __rt_btreemap_insert(m, "cherry", 3)
expect(__rt_btreemap_first_key(m)).to_equal("apple")
expect(__rt_btreemap_last_key(m)).to_equal("cherry")
```

</details>

#### clear empties the map; re-insert works after clear

- clear empties the map; re-insert works after clear
- Verify: clear empties the map; re-insert works after clear
   - Expected: __rt_btreemap_len(m) equals `0`
   - Expected: __rt_btreemap_contains_key(m, "a") is false
   - Expected: __rt_btreemap_len(m) equals `1`
   - Expected: __rt_btreemap_get(m, "fresh") equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear empties the map; re-insert works after clear")
step("Verify: clear empties the map; re-insert works after clear")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "a", 1)
_ = __rt_btreemap_insert(m, "b", 2)
_ = __rt_btreemap_clear(m)
expect(__rt_btreemap_len(m)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(__rt_btreemap_contains_key(m, "a")).to_equal(false)
_ = __rt_btreemap_insert(m, "fresh", 99)
expect(__rt_btreemap_len(m)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(__rt_btreemap_get(m, "fresh")).to_equal(99)
```

</details>

#### keys() returns a non-nil result for a non-empty map

- keys() returns a non-nil result for a non-empty map
- Verify: keys() returns a non-nil result for a non-empty map
   - Expected: ks equals `ks)   # non-nil: would panic if nil dereference`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys() returns a non-nil result for a non-empty map")
step("Verify: keys() returns a non-nil result for a non-empty map")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "x", 10)
val ks = __rt_btreemap_keys(m)
expect(ks).to_equal(ks)   # non-nil: would panic if nil dereference
```

</details>

#### values() returns a non-nil result for a non-empty map

- values() returns a non-nil result for a non-empty map
- Verify: values() returns a non-nil result for a non-empty map
   - Expected: vs equals `vs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("values() returns a non-nil result for a non-empty map")
step("Verify: values() returns a non-nil result for a non-empty map")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "x", 10)
val vs = __rt_btreemap_values(m)
expect(vs).to_equal(vs)
```

</details>

#### entries() returns a non-nil result for a non-empty map

- entries() returns a non-nil result for a non-empty map
- Verify: entries() returns a non-nil result for a non-empty map
   - Expected: es equals `es`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entries() returns a non-nil result for a non-empty map")
step("Verify: entries() returns a non-nil result for a non-empty map")
val m = __rt_btreemap_new()
_ = __rt_btreemap_insert(m, "x", 10)
val es = __rt_btreemap_entries(m)
expect(es).to_equal(es)
```

</details>

### BTreeSet — B1 macro parity gate

#### new() produces an empty set

- new() produces an empty set
- Verify: new() produces an empty set
   - Expected: __rt_btreeset_len(s) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new() produces an empty set")
step("Verify: new() produces an empty set")
val s = __rt_btreeset_new()
expect(__rt_btreeset_len(s)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### insert returns true and increases len

- insert returns true and increases len
- Verify: insert returns true and increases len
   - Expected: ok is true
   - Expected: __rt_btreeset_len(s) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("insert returns true and increases len")
step("Verify: insert returns true and increases len")
val s = __rt_btreeset_new()
val ok = __rt_btreeset_insert(s, "alpha")
expect(ok).to_equal(true)
expect(__rt_btreeset_len(s)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### contains is true after insert, false for missing

- contains is true after insert, false for missing
- Verify: contains is true after insert, false for missing
   - Expected: __rt_btreeset_contains(s, "present") is true
   - Expected: __rt_btreeset_contains(s, "absent") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains is true after insert, false for missing")
step("Verify: contains is true after insert, false for missing")
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "present")
expect(__rt_btreeset_contains(s, "present")).to_equal(true)
expect(__rt_btreeset_contains(s, "absent")).to_equal(false)
```

</details>

#### duplicate insert is idempotent: len stays 1

- duplicate insert is idempotent: len stays 1
- Verify: duplicate insert is idempotent: len stays 1
   - Expected: __rt_btreeset_len(s) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("duplicate insert is idempotent: len stays 1")
step("Verify: duplicate insert is idempotent: len stays 1")
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "dup")
_ = __rt_btreeset_insert(s, "dup")
expect(__rt_btreeset_len(s)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### remove drops element and decreases len

- remove drops element and decreases len
- Verify: remove drops element and decreases len
   - Expected: __rt_btreeset_len(s) equals `0`
   - Expected: __rt_btreeset_contains(s, "to_remove") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove drops element and decreases len")
step("Verify: remove drops element and decreases len")
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "to_remove")
_ = __rt_btreeset_remove(s, "to_remove")
expect(__rt_btreeset_len(s)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(__rt_btreeset_contains(s, "to_remove")).to_equal(false)
```

</details>

#### remove of non-existent element does not panic

- remove of non-existent element does not panic
- Verify: remove of non-existent element does not panic
   - Expected: __rt_btreeset_len(s) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove of non-existent element does not panic")
step("Verify: remove of non-existent element does not panic")
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "real")
_ = __rt_btreeset_remove(s, "ghost")
expect(__rt_btreeset_len(s)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### first and last reflect sorted order

- first and last reflect sorted order
- Verify: first and last reflect sorted order
   - Expected: __rt_btreeset_first(s) equals `apple`
   - Expected: __rt_btreeset_last(s) equals `zebra`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first and last reflect sorted order")
step("Verify: first and last reflect sorted order")
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "mango")
_ = __rt_btreeset_insert(s, "apple")
_ = __rt_btreeset_insert(s, "zebra")
expect(__rt_btreeset_first(s)).to_equal("apple")
expect(__rt_btreeset_last(s)).to_equal("zebra")
```

</details>

#### clear empties the set; re-insert works after clear

- clear empties the set; re-insert works after clear
- Verify: clear empties the set; re-insert works after clear
   - Expected: __rt_btreeset_len(s) equals `0`
   - Expected: __rt_btreeset_len(s) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear empties the set; re-insert works after clear")
step("Verify: clear empties the set; re-insert works after clear")
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "a")
_ = __rt_btreeset_insert(s, "b")
_ = __rt_btreeset_clear(s)
expect(__rt_btreeset_len(s)).to_equal(0)  # oracle: 0 — named expected value from the requirement
_ = __rt_btreeset_insert(s, "fresh")
expect(__rt_btreeset_len(s)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### to_array returns a non-nil result for a non-empty set

- to_array returns a non-nil result for a non-empty set
- Verify: to_array returns a non-nil result for a non-empty set
   - Expected: arr equals `arr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_array returns a non-nil result for a non-empty set")
step("Verify: to_array returns a non-nil result for a non-empty set")
val s = __rt_btreeset_new()
_ = __rt_btreeset_insert(s, "item")
val arr = __rt_btreeset_to_array(s)
expect(arr).to_equal(arr)
```

</details>

<details>
<summary>Advanced: 32-entry stress insert and lookup</summary>

#### 32-entry stress insert and lookup

- 32-entry stress insert and lookup
- Verify: 32-entry stress insert and lookup
   - Expected: __rt_btreeset_len(s) equals `32`
   - Expected: __rt_btreeset_first(s) equals `s00`
   - Expected: __rt_btreeset_last(s) equals `s31`
   - Expected: __rt_btreeset_contains(s, "s15") is true
   - Expected: __rt_btreeset_contains(s, "s99") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("32-entry stress insert and lookup")
step("Verify: 32-entry stress insert and lookup")
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
expect(__rt_btreeset_len(s)).to_equal(32)  # oracle: 32 — named expected value from the requirement
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-NOGC-ASYNC-MUT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7dd44b49e059f9aa4190d6b03a49beaf0c4c44195fe00646ad9847f3bdbab8a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7dd44b49e059f9aa4190d6b03a49beaf0c4c44195fe00646ad9847f3bdbab8a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7dd44b49e059f9aa4190d6b03a49beaf0c4c44195fe00646ad9847f3bdbab8a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/nogc_async_mut/btreemap_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/btreemap_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/btreemap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/btreemap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/btreemap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/btreemap_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new() produces a valid empty map' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/btreemap_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'insert returns true and increases len' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/btreemap_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get retrieves an inserted value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
