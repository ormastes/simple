# Hash Trait Specification

> 1. check

<!-- sdn-diagram:id=hash_trait_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hash_trait_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hash_trait_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hash_trait_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hash Trait Specification

## Scenarios

### Hash trait

### Text hashing

#### is stable for the same string

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = hash_text("hello")
val h2 = hash_text("hello")
check(h1 == h2)
```

</details>

#### changes for different strings

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_text("hello") != hash_text("world"))
```

</details>

#### handles empty string

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_text("") == 17)
```

</details>

#### treats unicode input as distinct

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_text("hello") != hash_text("héllo"))
```

</details>

### Integer hashing

#### is stable for the same integer

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_int(42) == hash_int(42))
```

</details>

#### changes across adjacent integers

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_int(42) != hash_int(43))
```

</details>

#### handles negative values

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_int(-1) != hash_int(0))
```

</details>

### Boolean hashing

#### maps true and false to different hashes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_bool(true) != hash_bool(false))
```

</details>

#### maps false to zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_bool(false) == 0)
```

</details>

### Collection hashing

#### combines array element hashes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = hash_array([1, 2, 3])
val b = hash_array([1, 2, 4])
check(a != b)
```

</details>

#### is order sensitive

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_array([1, 2, 3]) != hash_array([3, 2, 1]))
```

</details>

#### preserves uniqueness across a small sample

1. hash text
2. hash text
3. hash text
4. hash text
5. hash text
6. hash text
7. hash text
8. hash text
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hashes = [
    hash_text("a"),
    hash_text("hi"),
    hash_text("at"),
    hash_text("ah"),
    hash_text("fly"),
    hash_text("bit"),
    hash_text("stop"),
    hash_text("zebra")
]
check(unique_count(hashes) == hashes.len())
```

</details>

### Pair hashing

#### combines tuple-like values

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_pair(42, 7) != hash_pair(42, 8))
```

</details>

#### is order sensitive

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_pair(1, 2) != hash_pair(2, 1))
```

</details>

### Hash characteristics

#### changes when one character changes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = hash_text("test")
val h2 = hash_text("tesa")
check(h1 != h2)
```

</details>

#### remains non-zero for non-empty input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(hash_text("sample") != 0)
```

</details>

#### keeps repeated hashing consistent

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = hash_array([hash_int(1), hash_int(2), hash_int(3)])
val second = hash_array([hash_int(1), hash_int(2), hash_int(3)])
check(first == second)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/hash/hash_trait_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Hash trait
- Text hashing
- Integer hashing
- Boolean hashing
- Collection hashing
- Pair hashing
- Hash characteristics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
