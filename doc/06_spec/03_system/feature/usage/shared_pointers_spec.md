# Reference Counted Pointers Specification

> <details>

<!-- sdn-diagram:id=shared_pointers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_pointers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_pointers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_pointers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reference Counted Pointers Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SHARED-PTR |
| Category | Runtime |
| Status | Implemented |
| Source | `test/03_system/feature/usage/shared_pointers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Behaviors

- Reference count incremented on clone, decremented on drop
- Value is deallocated when reference count reaches zero
- Cloning creates shallow copy with incremented reference count

## Scenarios

### Reference Counted Pointers

#### creates pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = new * 42
expect ptr == 42
```

</details>

#### pointer arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = new * 10
val b = new * 5
expect a + b == 15
```

</details>

#### multiple references

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = new * 42
val b = a
expect a + b == 84
```

</details>

### Reference Semantics

#### tracks multiple references

1. expect ref1 len
2. expect ref2 len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3]
val ref1 = list
val ref2 = list
expect ref1.len() == 3
expect ref2.len() == 3
```

</details>

#### clones underlying data

1. expect cloned len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [1, 2, 3]
val cloned = original
expect cloned[0] == 1
expect cloned.len() == 3
```

</details>

#### dict references work correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"key": 42}
val ref = data
expect ref["key"] == 42
```

</details>

### Memory Safety

#### data remains valid while referenced

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val r1 = data
expect r1[0] == 1
```

</details>

#### strings are valid

1. expect ref len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val ref = s
expect ref.len() == 5
```

</details>

#### nested data structures work

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = [[1, 2], [3, 4]]
val ref = outer
expect ref[0][0] == 1
expect ref[1][1] == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
