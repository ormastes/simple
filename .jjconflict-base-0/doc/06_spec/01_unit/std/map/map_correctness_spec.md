# Map Correctness Specification

> 1. check

<!-- sdn-diagram:id=map_correctness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=map_correctness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

map_correctness_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=map_correctness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Map Correctness Specification

## Scenarios

### Map correctness

#### creates an empty map

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = MiniMap.new()
check(map.is_empty())
check(map.len() == 0)
check(map.capacity == 4)
```

</details>

#### inserts and retrieves entries

1. var map = MiniMap new
2. map insert
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = MiniMap.new()
map.insert("key", 42)
check(not map.is_empty())
check(map.len() == 1)
check(map.get("key") == Some(42))
check(map.has("key"))
```

</details>

#### updates an existing key without duplicating it

1. var map = MiniMap new
2. map insert
3. map insert
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = MiniMap.new()
map.insert("key", 1)
map.insert("key", 2)
check(map.len() == 1)
check(map.get("key") == Some(2))
```

</details>

#### returns None for a missing key

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = MiniMap.new()
check(map.get("missing") == None)
check(not map.has("missing"))
```

</details>

#### removes entries and keeps other entries intact

1. var map = MiniMap new
2. map insert
3. map insert
4. map insert
5. check
6. check
7. check
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = MiniMap.new()
map.insert("a", 1)
map.insert("b", 2)
map.insert("c", 3)

val removed = map.remove("b")
check(removed == Some(2))
check(map.len() == 2)
check(map.get("a") == Some(1))
check(map.get("b") == None)
check(map.get("c") == Some(3))
```

</details>

#### clears all entries

1. var map = MiniMap new
2. map insert
3. map insert
4. map clear
5. check
6. check
7. check
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = MiniMap.new()
map.insert("a", 1)
map.insert("b", 2)
map.clear()

check(map.is_empty())
check(map.len() == 0)
check(map.get("a") == None)
check(sum_counts(map.buckets) == 0)
```

</details>

#### returns keys values and entries in insertion order

1. var map = MiniMap new
2. map insert
3. map insert
4. check
5. check text
6. check text
7. check
8. check
9. check
10. check
11. check text
12. check
13. check text
14. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = MiniMap.new()
map.insert("a", 1)
map.insert("b", 2)

val keys = map.keys()
val values = map.values()
val entries = map.entries()

check(keys.len() == 2)
check_text(keys[0], "a")
check_text(keys[1], "b")
check(values.len() == 2)
check(values[0] == 1)
check(values[1] == 2)
check(entries.len() == 2)
check_text(entries[0].key, "a")
check(entries[0].value == 1)
check_text(entries[1].key, "b")
check(entries[1].value == 2)
```

</details>

#### grows capacity when the load threshold is exceeded

1. var map = MiniMap with capacity
2. map insert
3. map insert
4. map insert
5. map insert
6. check
7. check
8. check
9. check
10. check
11. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = MiniMap.with_capacity(4)
val initial_capacity = map.capacity
map.insert("a", 1)
map.insert("bb", 2)
map.insert("ccc", 3)
map.insert("dddd", 4)

check(map.capacity == initial_capacity * 2)
check(map.len() == 4)
check(map.get("a") == Some(1))
check(map.get("bb") == Some(2))
check(map.get("ccc") == Some(3))
check(map.get("dddd") == Some(4))
```

</details>

#### clones independently

1. var original = MiniMap new
2. original insert
3. original insert
4. original insert
5. check
6. check
7. check
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var original = MiniMap.new()
original.insert("a", 1)
original.insert("b", 2)

val copy = original.clone()
original.insert("c", 3)

check(original.len() == 3)
check(copy.len() == 2)
check(copy.get("c") == None)
check(copy.get("a") == Some(1))
check(copy.get("b") == Some(2))
```

</details>

#### tracks bucket counts for inserted entries

1. var map = MiniMap with capacity
2. map insert
3. map insert
4. map insert
5. map insert
6. check
7. check
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = MiniMap.with_capacity(4)
map.insert("a", 1)
map.insert("bb", 2)
map.insert("ccc", 3)
map.insert("dddd", 4)

check(sum_counts(map.buckets) == 4)
check(map.buckets.len() == map.capacity)
check(map.capacity >= 4)
```

</details>

#### handles special and unicode keys

1. var map = MiniMap new
2. map insert
3. map insert
4. map insert
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = MiniMap.new()
map.insert("key\nwith\nnewlines", 1)
map.insert("key\twith\ttabs", 2)
map.insert("héllo", 3)

check(map.get("key\nwith\nnewlines") == Some(1))
check(map.get("key\twith\ttabs") == Some(2))
check(map.get("héllo") == Some(3))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/map/map_correctness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Map correctness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
