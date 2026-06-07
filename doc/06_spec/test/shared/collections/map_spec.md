# Map Specification

> 1. expect m keys

<!-- sdn-diagram:id=map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

map_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Map Specification

## Scenarios

### Dict (Map)

#### Construction

#### creates empty dict

1. expect m keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = {}
expect m.keys().len() == 0
```

</details>

#### Basic operations

#### inserts and retrieves value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["name"] = "Alice"
expect m["name"] == "Alice"
```

</details>

#### updates existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["count"] = 1
m["count"] = 2
expect m["count"] == 2
```

</details>

#### contains_key returns true for existing keys

1. expect m has


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["key"] = "value"
expect m.has("key")
```

</details>

#### contains_key returns false for missing keys

1. expect not m has


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = {}
expect not m.has("missing")
```

</details>

#### len increases with insertions

1. expect m keys
2. expect m keys
3. expect m keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
expect m.keys().len() == 0
m["a"] = 1
expect m.keys().len() == 1
m["b"] = 2
expect m.keys().len() == 2
```

</details>

#### len does not increase for updates

1. expect m keys
2. expect m keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["key"] = 1
expect m.keys().len() == 1
m["key"] = 2
expect m.keys().len() == 1
```

</details>

#### Keys, values

#### keys returns all keys

1. expect keys len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["a"] = 1
m["b"] = 2
m["c"] = 3
val keys = m.keys()
expect keys.len() == 3
```

</details>

#### empty dict returns empty key list

1. expect m keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = {}
expect m.keys().len() == 0
```

</details>

#### Multiple entries

#### handles many insertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
for i in 0..10:
    val k = "key{i}"
    m[k] = i
val klen = m.keys().len()
expect klen == 10
expect m["key5"] == 5
```

</details>

#### Different value types

#### stores integer values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["count"] = 42
expect m["count"] == 42
```

</details>

#### stores text values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["name"] = "Alice"
expect m["name"] == "Alice"
```

</details>

#### stores boolean values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["active"] = true
expect m["active"] == true
```

</details>

#### Edge cases

#### handles empty string key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m[""] = "empty key"
expect m[""] == "empty key"
```

</details>

#### handles similar keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["test"] = 1
m["test1"] = 2
m["test2"] = 3
expect m["test"] == 1
expect m["test1"] == 2
```

</details>

#### Iteration

#### can iterate over entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["a"] = 1
m["b"] = 2
m["c"] = 3
var count = 0
for key in m.keys():
    count = count + 1
expect count == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/collections/map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dict (Map)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
