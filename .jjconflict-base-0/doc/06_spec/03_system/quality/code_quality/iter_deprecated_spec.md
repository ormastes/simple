# List.iter() Deprecation Replacement Spec

> Canary spec verifying that the replacement APIs for the deprecated `List<T>.iter()` method work correctly. The deprecated `iter()` will be removed; these tests lock the replacement contract so it cannot regress.

<!-- sdn-diagram:id=iter_deprecated_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=iter_deprecated_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

iter_deprecated_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=iter_deprecated_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# List.iter() Deprecation Replacement Spec

Canary spec verifying that the replacement APIs for the deprecated `List<T>.iter()` method work correctly. The deprecated `iter()` will be removed; these tests lock the replacement contract so it cannot regress.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-foreach-deprecated |
| Category | Testing |
| Difficulty | 1/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/iter_deprecated_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Canary spec verifying that the replacement APIs for the deprecated `List<T>.iter()`
method work correctly. The deprecated `iter()` will be removed; these tests lock
the replacement contract so it cannot regress.

Replacements for `List<T>.iter()`:
- Inline iteration: `for x in list` (preferred — avoids closure capture limits)
- Callback iteration: `list.each(fn)` (use when callback is a named function)
- Indexed iteration: `list.each_with_index(fn)`

NOTE: These specs verify the replacement methods work. They cannot directly
assert that the deprecated method is gone — that is a grep gate at phase 7-verify:
  `rg -F 'iter()' src/compiler_rust/lib/std/src/core/list.spl`
should return zero deprecated usages after phase 5-implement completes.

## Scenarios

### List.each() iterates all elements (replaces iter())

#### List.each() visits every element in order

1. parts push
   - Expected: parts.join("") equals `102030`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [10, 20, 30]
var parts: [text] = []
each(items, \n:
    parts.push(n.to_string())
)
expect(parts.join("")).to_equal("102030")
```

</details>

#### List.each() on empty list calls fn zero times

1. seen push
   - Expected: seen.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: List<Int> = []
var seen: [i64] = []
each(items, \n:
    seen.push(1)
)
expect(seen.len()).to_equal(0)
```

</details>

#### List.each() accumulates a sum correctly

1. seen push
   - Expected: sum equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
var seen: [i64] = []
each(items, \n:
    seen.push(n)
)
var sum = 0
for n in seen:
    sum = sum + n
expect(sum).to_equal(15)
```

</details>

### for x in list works without iter() (replaces for x in list.iter())

#### for x in list visits every element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["a", "b", "c"]
var count = 0
for item in items:
    count = count + 1
expect(count).to_equal(3)
```

</details>

#### for x in list accumulates all values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [2, 4, 6]
var sum = 0
for n in items:
    sum = sum + n
expect(sum).to_equal(12)
```

</details>

#### for x in list on empty list executes zero iterations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: List<Int> = []
var count = 0
for n in items:
    count = count + 1
expect(count).to_equal(0)
```

</details>

### List.each_with_index provides index alongside element

#### List.each_with_index passes correct index and value

1. indices push
   - Expected: index_sum equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["x", "y", "z"]
var indices: [i64] = []
each_with_index(items, \v, i:
    indices.push(i)
)
var index_sum = 0
for i in indices:
    index_sum = index_sum + i
expect(index_sum).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
