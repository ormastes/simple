# Helpers Example Specification

> <details>

<!-- sdn-diagram:id=helpers_example_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helpers_example_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helpers_example_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helpers_example_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Example Specification

## Scenarios

### Inline Helpers - Phase 2 Workaround

#### String operations

#### trims whitespace from both ends

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "  hello world  "
val trimmed = string_trim_inline(input)
expect(trimmed).to_equal("hello world")
```

</details>

#### trims tabs and newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "\t\nhello\n\t"
val trimmed = string_trim_inline(input)
expect(trimmed).to_equal("hello")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = string_trim_inline("")
expect(empty).to_equal("")
```

</details>

#### splits string by delimiter

- var parts = string split inline
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `apple`
   - Expected: parts[1] equals `banana`
   - Expected: parts[2] equals `cherry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csv = "apple,banana,cherry"
var parts = string_split_inline(csv, ",")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("apple")
expect(parts[1]).to_equal("banana")
expect(parts[2]).to_equal("cherry")
```

</details>

#### splits with multi-character delimiter

- var parts = string split inline
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "foo::bar::baz"
var parts = string_split_inline(text, "::")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("foo")
```

</details>

#### handles no delimiters found

- var parts = string split inline
   - Expected: parts.len() equals `1`
   - Expected: parts[0] equals `no-delimiters-here`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "no-delimiters-here"
var parts = string_split_inline(text, ",")
expect(parts.len()).to_equal(1)
expect(parts[0]).to_equal("no-delimiters-here")
```

</details>

#### Array operations

#### appends two arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr1 = [1, 2, 3]
val arr2 = [4, 5, 6]
val combined = array_append_all_inline(arr1, arr2)
expect(combined.len()).to_equal(6)
expect(combined[0]).to_equal(1)
expect(combined[5]).to_equal(6)
```

</details>

#### partitions by predicate

- var result = array partition inline
   - Expected: evens.len() equals `3`
   - Expected: odds.len() equals `3`
   - Expected: evens[0] equals `2`
   - Expected: odds[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5, 6]
val is_even = fn(x): x % 2 == 0
var result = array_partition_inline(numbers, is_even)
val evens = result.0
val odds = result.1
expect(evens.len()).to_equal(3)
expect(odds.len()).to_equal(3)
expect(evens[0]).to_equal(2)
expect(odds[0]).to_equal(1)
```

</details>

#### flattens nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = [[1, 2], [3, 4], [5, 6]]
val flat_result = array_flatten_inline(nested)
expect(flat_result.len()).to_equal(6)
expect(flat_result[0]).to_equal(1)
expect(flat_result[5]).to_equal(6)
```

</details>

#### flattens arrays with different lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = [[1], [2, 3, 4], [5, 6]]
val flat_result = array_flatten_inline(nested)
expect(flat_result.len()).to_equal(6)
```

</details>

#### Real-world usage

#### processes CSV data

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate reading CSV lines
val csv_line = "Alice,30,Engineer"
val fields = string_split_inline(csv_line, ",")

expect(fields.len()).to_equal(3)
expect(fields[0]).to_equal("Alice")
expect(fields[1]).to_equal("30")
expect(fields[2]).to_equal("Engineer")
```

</details>

#### combines data from multiple sources

- var all data = array append all inline
- all data = array append all inline
   - Expected: all_data.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source1 = [1, 2, 3]
val source2 = [4, 5]
val source3 = [6, 7, 8, 9]

# Combine all sources
var all_data = array_append_all_inline(source1, source2)
all_data = array_append_all_inline(all_data, source3)

expect(all_data.len()).to_equal(9)
```

</details>

#### filters and processes text lines

- trimmed lines push
   - Expected: trimmed_lines[0] equals `line 1`
   - Expected: trimmed_lines[1] equals `line 2`
   - Expected: trimmed_lines[2] equals `line 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate file lines with whitespace
val lines = ["  line 1  ", "  line 2  ", "  line 3  "]
var trimmed_lines = []
for line in lines:
    trimmed_lines.push(string_trim_inline(line))

expect(trimmed_lines[0]).to_equal("line 1")
expect(trimmed_lines[1]).to_equal("line 2")
expect(trimmed_lines[2]).to_equal("line 3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/helpers_example_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Inline Helpers - Phase 2 Workaround

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
