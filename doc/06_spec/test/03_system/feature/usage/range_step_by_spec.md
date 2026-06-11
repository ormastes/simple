# Range Step Specification

> arr[::2]       # Every other element (step=2)

<!-- sdn-diagram:id=range_step_by_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=range_step_by_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

range_step_by_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=range_step_by_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Range Step Specification

arr[::2]       # Every other element (step=2)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RANGE-STEP |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/range_step_by_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Slice with step
arr[::2]       # Every other element (step=2)
arr[1::2]      # Every other starting from index 1
arr[::-1]      # Reversed
arr[1:5:2]     # Slice from 1 to 5 with step 2

# Range iteration (stdlib method)
for i in (0..10).step_by(2):
print i    # 0, 2, 4, 6, 8
```

## Key Behaviors

- Step value can be positive (forward) or negative (reverse)
- Step of 1 is the default (every element)
- Step of -1 reverses the sequence
- Step of 2 selects every other element
- Works on arrays, strings, and any sliceable type

## Scenarios

### Range Step (Slicing with Step)

#### basic step on arrays

#### selects every other element with step 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[::2] == [0, 2, 4, 6, 8]
```

</details>

#### selects every third element with step 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[::3] == [0, 3, 6, 9]
```

</details>

#### selects every fourth element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
expect arr[::4] == [0, 4, 8]
```

</details>

#### step with start offset

#### starts from index 1 with step 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[1::2] == [1, 3, 5, 7, 9]
```

</details>

#### starts from index 2 with step 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[2::3] == [2, 5, 8]
```

</details>

#### starts from middle of array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[5::2] == [5, 7, 9]
```

</details>

#### step with start and end

#### slices range with step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[1:8:2] == [1, 3, 5, 7]
```

</details>

#### slices narrow range with step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[2:6:2] == [2, 4]
```

</details>

#### slices with step larger than range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[0:5:10] == [0]
```

</details>

#### negative step (reverse)

#### reverses entire array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect arr[::-1] == [5, 4, 3, 2, 1]
```

</details>

#### reverses empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
expect arr[::-1] == []
```

</details>

#### reverses single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [42]
expect arr[::-1] == [42]
```

</details>

#### reverses with step -2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
expect arr[::-2] == [9, 7, 5, 3, 1]
```

</details>

#### step on strings

#### selects every other character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefgh"
expect s[::2] == "aceg"
```

</details>

#### reverses string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect s[::-1] == "olleh"
```

</details>

#### selects odd-indexed characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefgh"
expect s[1::2] == "bdfh"
```

</details>

#### slices string with step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "0123456789"
expect s[1:8:2] == "1357"
```

</details>

#### edge cases

#### handles step equal to length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect arr[::5] == [1]
```

</details>

#### handles step greater than length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect arr[::10] == [1]
```

</details>

#### handles step of 1 (identity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect arr[::1] == [1, 2, 3, 4, 5]
```

</details>

#### handles empty slice with step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect arr[5:5:2] == []
```

</details>

#### practical examples

#### extracts even indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = ["a", "b", "c", "d", "e", "f"]
expect data[::2] == ["a", "c", "e"]
```

</details>

#### extracts odd indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = ["a", "b", "c", "d", "e", "f"]
expect data[1::2] == ["b", "d", "f"]
```

</details>

#### reverses for iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
var sum = 0
for n in nums[::-1]:
    sum = sum * 10 + n
expect sum == 54321
```

</details>

#### samples at regular intervals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readings = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
val sampled = readings[::3]
expect sampled == [10, 40, 70, 100]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
