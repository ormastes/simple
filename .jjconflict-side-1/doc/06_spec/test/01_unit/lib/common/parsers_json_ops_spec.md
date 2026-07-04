# JSON Operations Coverage Specification

> Branch-coverage tests for JSON object/array operations, path operations, validation, and utilities.

<!-- sdn-diagram:id=parsers_json_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parsers_json_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parsers_json_ops_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parsers_json_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON Operations Coverage Specification

Branch-coverage tests for JSON object/array operations, path operations, validation, and utilities.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-JSON-OPS |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/lib/common/parsers_json_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch-coverage tests for JSON object/array operations, path operations,
validation, and utilities.

## Scenarios

### JSON Object Operations

#### basic operations

#### returns nil when getting from non-object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_object_get(json_number(42), "key")
expect(result).to_be_nil()
```

</details>

#### sets value on non-object creates new object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = json_object_set(json_null(), "key", json_number(1))
expect(json_is_object(updated)).to_equal(true)
```

</details>

#### checks key on non-object returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object_has(json_array([]), "x")).to_equal(false)
```

</details>

#### empty object has zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object_size(json_object({}))).to_equal(0)
```

</details>

#### sets and checks object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val updated = json_object_set(obj, "name", json_string("Bob"))
expect(json_is_object(updated)).to_equal(true)
```

</details>

#### property accessors

#### gets keys from empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val keys = json_object_keys(obj)
expect(keys.len()).to_equal(0)
```

</details>

#### gets values from empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val vals = json_object_values(obj)
expect(vals.len()).to_equal(0)
```

</details>

#### gets entries from empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val entries = json_object_entries(obj)
expect(entries.len()).to_equal(0)
```

</details>

#### gets size of object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1), "b": json_number(2)})
expect(json_object_size(obj)).to_equal(2)
```

</details>

#### gets size of empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object_size(json_object({}))).to_equal(0)
```

</details>

#### checks empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object_empty(json_object({}))).to_equal(true)
expect(json_object_empty(json_object({"a": json_number(1)}))).to_equal(false)
```

</details>

### JSON Array Operations

#### basic operations

#### gets element by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10), json_number(20)])
val result = json_array_get(arr, 0)
expect(json_to_number(result)).to_equal(10)
```

</details>

#### returns nil for out-of-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10)])
expect(json_array_get(arr, 5)).to_be_nil()
```

</details>

#### returns nil for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10)])
expect(json_array_get(arr, -1)).to_be_nil()
```

</details>

#### returns nil when getting from non-array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array_get(json_object({}), 0)).to_be_nil()
```

</details>

#### sets element at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
val updated = json_array_set(arr, 0, json_number(99))
val result = json_array_get(updated, 0)
expect(json_to_number(result)).to_equal(99)
```

</details>

#### set returns unchanged for out-of-bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val updated = json_array_set(arr, 5, json_number(99))
expect(json_array_length(updated)).to_equal(1)
```

</details>

#### appends element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val updated = json_array_append(arr, json_number(2))
expect(json_array_length(updated)).to_equal(2)
```

</details>

#### prepends element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(2)])
val updated = json_array_prepend(arr, json_number(1))
expect(json_array_length(updated)).to_equal(2)
val first = json_array_get(updated, 0)
expect(json_to_number(first)).to_equal(1)
```

</details>

#### removes element at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val updated = json_array_remove(arr, 1)
expect(json_array_length(updated)).to_equal(2)
```

</details>

#### properties

#### gets length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_length(arr)).to_equal(2)
```

</details>

#### checks empty - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array_empty(json_array([]))).to_equal(true)
```

</details>

#### checks empty - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array_empty(json_array([json_number(1)]))).to_equal(false)
```

</details>

#### gets first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10), json_number(20)])
val first = json_array_first(arr)
expect(json_to_number(first)).to_equal(10)
```

</details>

#### gets last element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10), json_number(20)])
val last = json_array_last(arr)
expect(json_to_number(last)).to_equal(20)
```

</details>

#### slices array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3), json_number(4)])
val sliced = json_array_slice(arr, 1, 3)
expect(json_array_length(sliced)).to_equal(2)
```

</details>

#### concatenates two arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a1 = json_array([json_number(1)])
val a2 = json_array([json_number(2)])
val combined = json_array_concat(a1, a2)
expect(json_array_length(combined)).to_equal(2)
```

</details>

#### reverses array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val reversed = json_array_reverse(arr)
val first = json_array_get(reversed, 0)
expect(json_to_number(first)).to_equal(3)
```

</details>

#### checks contains - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_contains(arr, json_number(2))).to_equal(true)
```

</details>

#### checks contains - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
expect(json_array_contains(arr, json_number(99))).to_equal(false)
```

</details>

#### finds index of element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10), json_number(20), json_number(30)])
val idx = json_array_index_of(arr, json_number(20))
expect(idx).to_equal(1)
```

</details>

#### returns -1 for missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val idx = json_array_index_of(arr, json_number(99))
expect(idx).to_equal(-1)
```

</details>

#### flattens nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = json_array([json_number(3), json_number(4)])
val arr = json_array([json_number(1), json_number(2), inner])
val flat = json_array_flatten(arr)
expect(json_array_length(flat)).to_be_greater_than(2)
```

</details>

#### removes duplicate values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
val unique = json_array_unique(arr)
# unique of non-duplicated array should have same length
expect(json_array_length(unique)).to_equal(2)
```

</details>

### JSON Path Operations

#### path parsing

#### parses simple path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = json_path_parse("user.name")
expect(parts.len()).to_equal(2)
```

</details>

#### parses single-segment path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = json_path_parse("name")
expect(parts.len()).to_equal(1)
```

</details>

#### returns empty for empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = json_path_parse("")
expect(parts.len()).to_equal(0)
```

</details>

#### path get

#### returns nil for nil current

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_path_get(nil, "a.b")
expect(result).to_be_nil()
```

</details>

#### path set

#### returns new_value for empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_path_set(json_object({}), "", json_number(42))
expect(json_to_number(result)).to_equal(42)
```

</details>

#### path delete

#### returns object for empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1)})
val result = json_path_delete(obj, "")
expect(json_is_object(result)).to_equal(true)
```

</details>

### JSON Validation

#### schema validation

#### validates nil schema as valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_validate_schema(json_number(1), nil)
expect(result.0).to_equal(true)
```

</details>

#### deep equals

#### equal nulls

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_null(), json_null())).to_equal(true)
```

</details>

#### equal numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_number(42), json_number(42))).to_equal(true)
```

</details>

#### unequal numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_number(1), json_number(2))).to_equal(false)
```

</details>

#### different types

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_number(1), json_string("1"))).to_equal(false)
```

</details>

#### nil vs nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(nil, nil)).to_equal(true)
```

</details>

#### nil vs value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(nil, json_number(1))).to_equal(false)
```

</details>

#### value vs nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_number(1), nil)).to_equal(false)
```

</details>

#### equal booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_boolean(true), json_boolean(true))).to_equal(true)
```

</details>

#### unequal booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_boolean(true), json_boolean(false))).to_equal(false)
```

</details>

#### equal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_string("a"), json_string("a"))).to_equal(true)
```

</details>

#### unequal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_string("a"), json_string("b"))).to_equal(false)
```

</details>

#### equal arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_array([json_number(1), json_number(2)])
val b = json_array([json_number(1), json_number(2)])
expect(json_deep_equals(a, b)).to_equal(true)
```

</details>

#### unequal arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_array([json_number(1)])
val b = json_array([json_number(2)])
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### arrays with different lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_array([json_number(1)])
val b = json_array([json_number(1), json_number(2)])
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### equal empty objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_object({})
val b = json_object({})
expect(json_deep_equals(a, b)).to_equal(true)
```

</details>

#### empty vs non-empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_object({})
val b = json_object({"x": json_number(1)})
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### deep clone

#### clones null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(json_null())
expect(json_is_null(cloned)).to_equal(true)
```

</details>

#### clones nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(nil)
expect(cloned).to_be_nil()
```

</details>

#### clones boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(json_boolean(true))
expect(json_to_boolean(cloned)).to_equal(true)
```

</details>

#### clones number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(json_number(42))
expect(json_to_number(cloned)).to_equal(42)
```

</details>

#### clones string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(json_string("hello"))
expect(json_to_string(cloned)).to_equal("hello")
```

</details>

#### clones array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
val cloned = json_deep_clone(arr)
expect(json_deep_equals(arr, cloned)).to_equal(true)
```

</details>

#### clones empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val cloned = json_deep_clone(obj)
expect(json_is_object(cloned)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 64 |
| Active scenarios | 64 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
