# Persistent Dict Intensive Specification

> 1. assert dict len

<!-- sdn-diagram:id=persistent_dict_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_dict_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_dict_intensive_spec -> spipe
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_dict_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Dict Intensive Specification

## Scenarios

### PersistentDict

### Core operations

#### creates an empty dict

1. assert dict len
2. assert dict is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = PersistentDict.new()
assert dict.len() == 0
assert dict.is_empty()
```

</details>

#### inserts and retrieves a value

1. assert dict len
2. assert dict get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = PersistentDict.new().set("key", 42)
assert dict.len() == 1
assert dict.get("key") == Some(42)
```

</details>

#### updates an existing key

1. assert dict1 get
2. assert dict2 get


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict1 = PersistentDict.new().set("key", 1)
val dict2 = dict1.set("key", 2)
assert dict1.get("key") == Some(1)
assert dict2.get("key") == Some(2)
```

</details>

#### removes a key

1. assert dict1 len
2. assert dict2 len
3. assert dict2 get
4. assert dict2 get


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict1 = PersistentDict.new().set("a", 1).set("b", 2)
val dict2 = dict1.remove("a")
assert dict1.len() == 2
assert dict2.len() == 1
assert dict2.get("a") == None
assert dict2.get("b") == Some(2)
```

</details>

### Immutability

#### keeps earlier versions unchanged

1. assert base get
2. assert next get
3. assert final get


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = PersistentDict.new().set("a", 1)
val next = base.set("b", 2)
val final = next.remove("a")
assert base.get("b") == None
assert next.get("a") == Some(1)
assert final.get("a") == None
```

</details>

#### supports a small version chain

1. var dict = PersistentDict new
2. dict = dict set
3. assert versions[0] len
4. assert versions[10] len
5. assert dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var versions: [PersistentDict] = []
var dict = PersistentDict.new()
for i in 0..25:
    versions = versions + [dict]
    dict = dict.set("key_{i}", i)

assert versions[0].len() == 0
assert versions[10].len() == 10
assert dict.len() == 25
```

</details>

### Bulk operations

#### merge combines dicts

1. assert merged len
2. assert merged get
3. assert merged get
4. assert merged get


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict1 = PersistentDict.new().set("a", 1).set("b", 2)
val dict2 = PersistentDict.new().set("b", 20).set("c", 3)
val merged = dict1.merge(dict2)
assert merged.len() == 3
assert merged.get("a") == Some(1)
assert merged.get("b") == Some(20)
assert merged.get("c") == Some(3)
```

</details>

#### filter keeps matching entries

1. var dict = PersistentDict new
2. dict = dict set
3. assert evens len
4. assert evens get
5. assert evens get
6. assert evens get


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = PersistentDict.new()
for i in 0..12:
    dict = dict.set("key_{i}", i)

val evens = dict.filter(\k, v: v % 2 == 0)
assert evens.len() == 6
assert evens.get("key_0") == Some(0)
assert evens.get("key_1") == None
assert evens.get("key_10") == Some(10)
```

</details>

#### map_values transforms values

1.  set
2.  set
3.  map values
4. assert doubled get
5. assert doubled get


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doubled = PersistentDict.new()
    .set("a", 1)
    .set("b", 2)
    .map_values(_1 * 2)
assert doubled.get("a") == Some(2)
assert doubled.get("b") == Some(4)
```

</details>

### Conversion

#### round-trips through entries

1.
2.
3.
4. assert dict len
5. assert entries len
6. assert entries has
7. assert entries has
8. assert entries has


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = PersistentDict.from_entries([
    ("a", 1),
    ("b", 2),
    ("c", 3)
])
val entries = dict.entries()
assert dict.len() == 3
assert entries.len() == 3
assert entries_has(entries, "a", 1)
assert entries_has(entries, "b", 2)
assert entries_has(entries, "c", 3)
```

</details>

#### returns keys and values

1.
2.
3. assert keys len
4. assert values len
5. assert keys contains
6. assert keys contains
7. assert values contains
8. assert values contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = PersistentDict.from_entries([
    ("a", 1),
    ("b", 2)
])
val keys = dict.keys()
val values = dict.values()
assert keys.len() == 2
assert values.len() == 2
assert keys.contains("a")
assert keys.contains("b")
assert values.contains(1)
assert values.contains(2)
```

</details>

### Edge cases

#### handles empty string keys

1. assert dict get


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = PersistentDict.new().set("", 42)
assert dict.get("") == Some(42)
```

</details>

#### handles unicode keys

1.  set
2.  set
3.  set
4. assert dict get
5. assert dict get
6. assert dict get


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = PersistentDict.new()
    .set("héllo", 1)
    .set("世界", 2)
    .set("🚀", 3)
assert dict.get("héllo") == Some(1)
assert dict.get("世界") == Some(2)
assert dict.get("🚀") == Some(3)
```

</details>

### Array helpers

#### inserts, updates, and removes at the expected position

1. assert array insert
2. assert array update
3. assert array remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
assert array_insert(arr, 1, 99) == [1, 99, 2, 3]
assert array_update(arr, 1, 99) == [1, 99, 3]
assert array_remove(arr, 1) == [1, 3]
```

</details>

#### leaves the original array unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val _ = array_insert(arr, 1, 99)
val _ = array_update(arr, 1, 99)
val _ = array_remove(arr, 1)
assert arr == [1, 2, 3]
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/collections/persistent_dict_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentDict
- Core operations
- Immutability
- Bulk operations
- Conversion
- Edge cases
- Array helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
