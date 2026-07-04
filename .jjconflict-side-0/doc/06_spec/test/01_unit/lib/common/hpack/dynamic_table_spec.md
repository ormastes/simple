# Dynamic Table Specification

> <details>

<!-- sdn-diagram:id=dynamic_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynamic_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynamic_table_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynamic_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Table Specification

## Scenarios

### DynamicTable — empty table

#### lookup on empty table returns nil for index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_empty()
expect(dynamic_table_lookup(t, 1).?).to_equal(false)
```

</details>

#### lookup on empty table returns nil for index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_empty()
expect(dynamic_table_lookup(t, 0).?).to_equal(false)
```

</details>

#### lookup on empty table returns nil for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_empty()
expect(dynamic_table_lookup(t, -1).?).to_equal(false)
```

</details>

#### empty table has current_size 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_empty()
expect(t.current_size).to_equal(0)
```

</details>

#### empty table has correct max_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_empty()
expect(t.max_size).to_equal(4096)
```

</details>

### DynamicTable — single insert

#### lookup at relative index 1 returns the entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_single()
val e = dynamic_table_lookup(t, 1) ?? DynamicEntry(name: "", value: "")
expect(e.name).to_equal("content-type")
expect(e.value).to_equal("text/plain")
```

</details>

#### lookup at relative index 2 returns nil after single insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_single()
expect(dynamic_table_lookup(t, 2).?).to_equal(false)
```

</details>

#### current_size equals name_len + value_len + 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_single()
# "content-type".len() = 12, "text/plain".len() = 10, +32 = 54
expect(t.current_size).to_equal(54)
```

</details>

#### entries length is 1 after single insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_single()
expect(t.entries.len()).to_equal(1)
```

</details>

### DynamicTable — multi-insert ordering

#### most recent entry is at relative index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_two()
val e = dynamic_table_lookup(t, 1) ?? DynamicEntry(name: "", value: "")
expect(e.name).to_equal("accept")
expect(e.value).to_equal("*/*")
```

</details>

#### oldest entry is at the highest relative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_two()
val e = dynamic_table_lookup(t, 2) ?? DynamicEntry(name: "", value: "")
expect(e.name).to_equal("content-type")
expect(e.value).to_equal("text/plain")
```

</details>

#### entries length is 2 after two inserts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_two()
expect(t.entries.len()).to_equal(2)
```

</details>

#### current_size is sum of both entry sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_two()
# "content-type"(12) + "text/plain"(10) + 32 = 54
# "accept"(6) + "*/*"(3) + 32 = 41
# total = 95
expect(t.current_size).to_equal(95)
```

</details>

### DynamicTable — eviction when size cap exceeded

#### evicts oldest entry when inserting third entry into cap=68 table

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_eviction_scenario()
# ("a","1") was evicted; newest is ("c","3"), then ("b","2")
expect(t.entries.len()).to_equal(2)
```

</details>

#### newest entry after eviction is at index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_eviction_scenario()
val e = dynamic_table_lookup(t, 1) ?? DynamicEntry(name: "", value: "")
expect(e.name).to_equal("c")
expect(e.value).to_equal("3")
```

</details>

#### second entry after eviction is the middle insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_eviction_scenario()
val e = dynamic_table_lookup(t, 2) ?? DynamicEntry(name: "", value: "")
expect(e.name).to_equal("b")
expect(e.value).to_equal("2")
```

</details>

#### evicted entry is not accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_eviction_scenario()
expect(dynamic_table_lookup(t, 3).?).to_equal(false)
```

</details>

#### current_size after eviction fits within max_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_eviction_scenario()
expect(t.current_size).to_be_less_than(69)
```

</details>

### DynamicTable — single entry larger than max_size

#### table is empty after oversized insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_oversized_insert()
expect(t.entries.len()).to_equal(0)
```

</details>

#### current_size is 0 after oversized insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_oversized_insert()
expect(t.current_size).to_equal(0)
```

</details>

#### oversized entry is not present in the table

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_oversized_insert()
expect(dynamic_table_lookup(t, 1).?).to_equal(false)
```

</details>

#### max_size is unchanged after oversized insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_oversized_insert()
expect(t.max_size).to_equal(10)
```

</details>

### DynamicTable — resize

#### resize down evicts oldest entries to fit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_after_resize_down()
# original had ("y","2") at idx 1, ("x","1") at idx 2; resize to 34
# keeps only one entry (the newest)
expect(t.entries.len()).to_equal(1)
```

</details>

#### resize down keeps newest entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_after_resize_down()
val e = dynamic_table_lookup(t, 1) ?? DynamicEntry(name: "", value: "")
expect(e.name).to_equal("y")
expect(e.value).to_equal("2")
```

</details>

#### resize up does not change number of entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = _make_two()
val after = _make_after_resize_up()
expect(after.entries.len()).to_equal(before.entries.len())
```

</details>

#### resize up raises max_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_after_resize_up()
expect(t.max_size).to_equal(8192)
```

</details>

#### resize up preserves entry at index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_after_resize_up()
val e = dynamic_table_lookup(t, 1) ?? DynamicEntry(name: "", value: "")
expect(e.name).to_equal("accept")
```

</details>

#### resize down sets correct new max_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_after_resize_down()
expect(t.max_size).to_equal(34)
```

</details>

### DynamicTable — dynamic_table_find

#### returns full match for existing (name, value)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_find_table()
# content-type: application/json is newest (index 1)
val r = dynamic_table_find(t, "content-type", "application/json")
expect(r.0).to_equal(1)
expect(r.1).to_equal(true)
```

</details>

#### returns name-only match when value differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cache-control appears twice; no entry has value "max-age=3600"
val t = _make_find_table()
val r = dynamic_table_find(t, "cache-control", "max-age=3600")
expect(r.0).to_be_greater_than(0)
expect(r.1).to_equal(false)
```

</details>

#### returns (-1, false) for unknown name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_find_table()
val r = dynamic_table_find(t, "x-custom", "anything")
expect(r.0).to_equal(-1)
expect(r.1).to_equal(false)
```

</details>

#### find on empty table returns (-1, false)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_empty()
val r = dynamic_table_find(t, "content-type", "text/html")
expect(r.0).to_equal(-1)
expect(r.1).to_equal(false)
```

</details>

#### returns the newest matching index for name-only match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cache-control appears at indices 2 (no-cache, newer) and 3 (no-store, oldest)
val t = _make_find_table()
val r = dynamic_table_find(t, "cache-control", "max-age=0")
# newest cache-control is at index 2 (content-type is 1, cache-control no-cache is 2)
expect(r.0).to_equal(2)
expect(r.1).to_equal(false)
```

</details>

### DynamicTable — eviction order is from oldest end

#### three inserts into tight cap evict in FIFO (oldest-first) order

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cap = 34 fits exactly one entry (size 34 each)
val t0 = dynamic_table_new(34)
val t1 = dynamic_table_insert(t0, "a", "1")
val t2 = dynamic_table_insert(t1, "b", "2")
val t3 = dynamic_table_insert(t2, "c", "3")
# After each insert only one entry fits; newest survives
val e1 = dynamic_table_lookup(t1, 1) ?? DynamicEntry(name: "", value: "")
val e2 = dynamic_table_lookup(t2, 1) ?? DynamicEntry(name: "", value: "")
val e3 = dynamic_table_lookup(t3, 1) ?? DynamicEntry(name: "", value: "")
expect(e1.name).to_equal("a")
expect(e2.name).to_equal("b")
expect(e3.name).to_equal("c")
```

</details>

#### after each eviction the table has at most one entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = dynamic_table_new(34)
val t1 = dynamic_table_insert(t0, "a", "1")
val t2 = dynamic_table_insert(t1, "b", "2")
val t3 = dynamic_table_insert(t2, "c", "3")
expect(t1.entries.len()).to_equal(1)
expect(t2.entries.len()).to_equal(1)
expect(t3.entries.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hpack/dynamic_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DynamicTable — empty table
- DynamicTable — single insert
- DynamicTable — multi-insert ordering
- DynamicTable — eviction when size cap exceeded
- DynamicTable — single entry larger than max_size
- DynamicTable — resize
- DynamicTable — dynamic_table_find
- DynamicTable — eviction order is from oldest end

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
