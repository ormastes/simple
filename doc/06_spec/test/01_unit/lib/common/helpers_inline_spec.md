# Helpers Inline Specification

> 1. var result = string trim inline

<!-- sdn-diagram:id=helpers_inline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helpers_inline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helpers_inline_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helpers_inline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Inline Specification

## Scenarios

### string_trim_inline

#### trims leading spaces

1. var result = string trim inline
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = string_trim_inline("   hello")
expect(result).to_equal("hello")
```

</details>

#### trims trailing spaces

1. var result = string trim inline
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = string_trim_inline("hello   ")
expect(result).to_equal("hello")
```

</details>

#### trims both ends

1. var result = string trim inline
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = string_trim_inline("  hello  ")
expect(result).to_equal("hello")
```

</details>

#### trims tabs

1. var result = string trim inline
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = string_trim_inline("\thello\t")
expect(result).to_equal("hello")
```

</details>

#### returns empty for all whitespace

1. var result = string trim inline
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = string_trim_inline("   ")
expect(result).to_equal("")
```

</details>

#### returns empty for empty string

1. var result = string trim inline
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = string_trim_inline("")
expect(result).to_equal("")
```

</details>

#### returns same for no whitespace

1. var result = string trim inline
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = string_trim_inline("hello")
expect(result).to_equal("hello")
```

</details>

#### preserves internal whitespace

1. var result = string trim inline
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = string_trim_inline("  hello world  ")
expect(result).to_equal("hello world")
```

</details>

### string_split_inline

#### splits by comma

1. var parts = string split inline
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `a`
   - Expected: parts[1] equals `b`
   - Expected: parts[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts = string_split_inline("a,b,c", ",")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("a")
expect(parts[1]).to_equal("b")
expect(parts[2]).to_equal("c")
```

</details>

#### splits by space

1. var parts = string split inline
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `hello`
   - Expected: parts[1] equals `world`
   - Expected: parts[2] equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts = string_split_inline("hello world test", " ")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("hello")
expect(parts[1]).to_equal("world")
expect(parts[2]).to_equal("test")
```

</details>

#### returns single element for no delimiter found

1. var parts = string split inline
   - Expected: parts.len() equals `1`
   - Expected: parts[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts = string_split_inline("hello", ",")
expect(parts.len()).to_equal(1)
expect(parts[0]).to_equal("hello")
```

</details>

#### handles empty delimiter by returning whole string

1. var parts = string split inline
   - Expected: parts.len() equals `1`
   - Expected: parts[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts = string_split_inline("hello", "")
expect(parts.len()).to_equal(1)
expect(parts[0]).to_equal("hello")
```

</details>

#### handles empty string

1. var parts = string split inline
   - Expected: parts.len() equals `1`
   - Expected: parts[0] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts = string_split_inline("", ",")
expect(parts.len()).to_equal(1)
expect(parts[0]).to_equal("")
```

</details>

#### handles delimiter at start

1. var parts = string split inline
   - Expected: parts.len() equals `2`
   - Expected: parts[0] equals ``
   - Expected: parts[1] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts = string_split_inline(",hello", ",")
expect(parts.len()).to_equal(2)
expect(parts[0]).to_equal("")
expect(parts[1]).to_equal("hello")
```

</details>

#### handles delimiter at end

1. var parts = string split inline
   - Expected: parts.len() equals `2`
   - Expected: parts[0] equals `hello`
   - Expected: parts[1] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts = string_split_inline("hello,", ",")
expect(parts.len()).to_equal(2)
expect(parts[0]).to_equal("hello")
expect(parts[1]).to_equal("")
```

</details>

#### handles multi-char delimiter

1. var parts = string split inline
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `a`
   - Expected: parts[1] equals `b`
   - Expected: parts[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts = string_split_inline("a::b::c", "::")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("a")
expect(parts[1]).to_equal("b")
expect(parts[2]).to_equal("c")
```

</details>

### to_int_or_inline

#### parses a valid integer

1. var result = to int or inline
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = to_int_or_inline("42", 0)
expect(result).to_equal(42)
```

</details>

#### parses negative integer

1. var result = to int or inline
   - Expected: result equals `-10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = to_int_or_inline("-10", 0)
expect(result).to_equal(-10)
```

</details>

#### parses zero

1. var result = to int or inline
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = to_int_or_inline("0", -1)
expect(result).to_equal(0)
```

</details>

#### returns default for non-numeric

1. var result = to int or inline
   - Expected: result equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = to_int_or_inline("abc", 99)
expect(result).to_equal(99)
```

</details>

#### returns default for empty string

1. var result = to int or inline
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = to_int_or_inline("", 42)
expect(result).to_equal(42)
```

</details>

### array_append_all_inline

#### concatenates two arrays

1. var result = array append all inline
   - Expected: result.len() equals `4`
   - Expected: result[0] equals `1`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `3`
   - Expected: result[3] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_append_all_inline([1, 2], [3, 4])
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(3)
expect(result[3]).to_equal(4)
```

</details>

#### handles empty first array

1. var result = array append all inline
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_append_all_inline([], [1, 2])
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(1)
```

</details>

#### handles empty second array

1. var result = array append all inline
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_append_all_inline([1, 2], [])
expect(result.len()).to_equal(2)
```

</details>

#### handles both empty

1. var result = array append all inline
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_append_all_inline([], [])
expect(result.len()).to_equal(0)
```

</details>

### array_flatten_inline

#### flattens nested arrays

1. var result = array flatten inline
   - Expected: result.len() equals `5`
   - Expected: result[0] equals `1`
   - Expected: result[4] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_flatten_inline([[1, 2], [3, 4], [5]])
expect(result.len()).to_equal(5)
expect(result[0]).to_equal(1)
expect(result[4]).to_equal(5)
```

</details>

#### handles empty nested arrays

1. var result = array flatten inline
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_flatten_inline([[], [1], []])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(1)
```

</details>

#### handles empty outer array

1. var result = array flatten inline
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_flatten_inline([])
expect(result.len()).to_equal(0)
```

</details>

### array_uniq_inline

#### removes duplicates

1. var result = array uniq inline
   - Expected: result.len() equals `3`
   - Expected: result[0] equals `1`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_uniq_inline([1, 2, 2, 3, 3, 3])
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(3)
```

</details>

#### preserves order

1. var result = array uniq inline
   - Expected: result.len() equals `3`
   - Expected: result[0] equals `3`
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_uniq_inline([3, 1, 2, 1, 3])
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(3)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(2)
```

</details>

#### handles empty array

1. var result = array uniq inline
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_uniq_inline([])
expect(result.len()).to_equal(0)
```

</details>

#### handles all unique

1. var result = array uniq inline
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_uniq_inline([1, 2, 3])
expect(result.len()).to_equal(3)
```

</details>

#### handles all same

1. var result = array uniq inline
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_uniq_inline([5, 5, 5, 5])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(5)
```

</details>

### array_compact_inline

#### removes nil values

1. var result = array compact inline
   - Expected: result.len() equals `3`
   - Expected: result[0] equals `1`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_compact_inline([1, nil, 2, nil, 3])
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(3)
```

</details>

#### handles no nil values

1. var result = array compact inline
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_compact_inline([1, 2, 3])
expect(result.len()).to_equal(3)
```

</details>

#### handles all nil

1. var result = array compact inline
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_compact_inline([nil, nil, nil])
expect(result.len()).to_equal(0)
```

</details>

#### handles empty array

1. var result = array compact inline
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_compact_inline([])
expect(result.len()).to_equal(0)
```

</details>

#### handles single nil

1. var result = array compact inline
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_compact_inline([nil])
expect(result.len()).to_equal(0)
```

</details>

#### handles single value

1. var result = array compact inline
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = array_compact_inline([42])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/helpers_inline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- string_trim_inline
- string_split_inline
- to_int_or_inline
- array_append_all_inline
- array_flatten_inline
- array_uniq_inline
- array_compact_inline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
