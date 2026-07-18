# Advanced Indexing and Slicing Specification

> Tests for advanced indexing features including:

<!-- sdn-diagram:id=advanced_indexing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=advanced_indexing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

advanced_indexing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=advanced_indexing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Indexing and Slicing Specification

Tests for advanced indexing features including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1015, #1016, #1017 |
| Category | Language, Collections |
| Status | Complete |
| Source | `test/03_system/feature/usage/advanced_indexing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for advanced indexing features including:
- Negative indexing (Python-style -1, -2, etc.)
- Slice operations with start:end:step syntax
- String slicing
- Multi-dimensional indexing

## Scenarios

### Advanced Indexing

#### negative indexing

#### accesses last element with -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[-1] == 50
```

</details>

#### accesses second-to-last with -2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[-2] == 40
```

</details>

#### accesses first element with negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect arr[-3] == 10
```

</details>

#### works with strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello"
expect s[-1] == "o"
expect s[-5] == "H"
```

</details>

#### negative indexing with single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [42]
expect arr[-1] == 42
```

</details>

#### slicing operations

#### slices with start and end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[1:4] == [20, 30, 40]
```

</details>

#### slices from beginning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[:3] == [10, 20, 30]
```

</details>

#### slices to end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[2:] == [30, 40, 50]
```

</details>

#### slices with step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[::2] == [10, 30, 50]
```

</details>

#### reverses with negative step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[::-1] == [50, 40, 30, 20, 10]
```

</details>

#### slices with start:end:step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[2:8:2] == [2, 4, 6]
```

</details>

#### empty slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect arr[5:10] == []
```

</details>

#### string slicing

#### slices substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello World"
expect s[0:5] == "Hello"
```

</details>

#### slices from end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello World"
expect s[-5:] == "World"
```

</details>

#### slices middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefgh"
expect s[2:6] == "cdef"
```

</details>

#### reverses string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello"
expect s[::-1] == "olleH"
```

</details>

#### handles UTF-8 characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello 🌍 World"
expect s[6:7] == "🌍"
```

</details>

#### combined operations

#### slices with negative start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[-3:] == [30, 40, 50]
```

</details>

#### slices with negative end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[:-2] == [10, 20, 30]
```

</details>

#### slices with both negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 40, 50]
expect arr[-4:-1] == [20, 30, 40]
```

</details>

#### negative indices in string slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello World"
expect s[-5:-1] == "Worl"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
